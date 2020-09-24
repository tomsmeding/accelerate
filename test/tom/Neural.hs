{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Neural where

import qualified Data.Array.Accelerate as A
import Data.Array.Accelerate.Data.Bits
import Data.Array.Accelerate (Z(..), (:.)(..), pattern Z_, pattern (::.))
import Data.Function ((&))

type Weights = A.Matrix Float
type RowBatch = A.Matrix Float
type ColBatch = A.Matrix Float

data Network acc a where
    InputLayer :: Network acc ()
    NextLayer :: A.Arrays a => acc Weights -> Network acc a -> Network acc (a, Weights)

deriving instance A.Arrays a => Show (Network A.Acc a)

liftNetwork :: Network A.Acc a -> A.Acc a
liftNetwork InputLayer = A.lift ()
liftNetwork (NextLayer w net) = A.T2 (liftNetwork net) w

-- First argument only used as model for the types; its contained arrays are not inspected
unliftNetwork :: Network A.Acc a -> A.Acc a -> Network A.Acc a
unliftNetwork InputLayer _ = InputLayer
unliftNetwork (NextLayer _ net) (A.T2 lnet w) = NextLayer w (unliftNetwork net lnet)

networkZip :: (A.Acc Weights -> A.Acc Weights -> A.Acc Weights) -> Network A.Acc a -> Network A.Acc a -> Network A.Acc a
networkZip _ InputLayer InputLayer = InputLayer
networkZip f (NextLayer w1 net1) (NextLayer w2 net2) = NextLayer (f w1 w2) (networkZip f net1 net2)


-- layers: from closest to input, to output layer; Z :. output :. input
-- input: Z :. batchsize :. vector
-- output: Z :. batchsize :. vector
forward :: Network A.Acc a -> A.Acc RowBatch -> A.Acc RowBatch
forward net input = A.transpose $ applyNetwork (\w i -> A.map sigmoid (matmat w i)) net (A.transpose input)

applyNetwork :: (A.Acc Weights -> A.Acc ColBatch -> A.Acc ColBatch) -> Network A.Acc a -> A.Acc ColBatch -> A.Acc ColBatch
applyNetwork _ InputLayer i = i
applyNetwork f (NextLayer ws net) i = f ws (applyNetwork f net i)

sigmoid :: A.Exp Float -> A.Exp Float
sigmoid x = 1 / (1 + exp (-x))

matvec :: A.Acc (A.Matrix Float) -> A.Acc (A.Vector Float) -> A.Acc (A.Vector Float)
matvec mat vec =
    let A.I2 nrows _ = A.shape mat
        vecm = A.replicate (Z_ ::. nrows ::. liftAll) vec
    in A.sum (A.zipWith (*) mat vecm)

matmat :: A.Acc (A.Matrix Float) -> A.Acc (A.Matrix Float) -> A.Acc (A.Matrix Float)
matmat m1 m2 =
    let A.I2 k _ = A.shape m1
        A.I2 _ n = A.shape m2
        m1' = A.replicate (Z_ ::. liftAll ::. n ::. liftAll) m1
        m2' = A.replicate (Z_ ::. k ::. liftAll ::. liftAll) (A.transpose m2)
    in A.sum (A.zipWith (*) m1' m2')

liftAll :: A.Exp A.All
liftAll = A.constant A.All


learnSingle :: A.Arrays a => Network A.Acc a -> A.Acc RowBatch -> A.Acc RowBatch -> Network A.Acc a
learnSingle net input expectedOutput =
    let learnRate = 0.05
        A.T3 contribution' _ _ =
          A.gradientA (\(A.T3 lnet input' expectedOutput') ->
                          let net' = unliftNetwork net lnet
                              output = forward net' input'
                             -- loss = 1/2 (out - expected) ∙ (out - expected)
                          in A.map (* 0.5) . A.fold1All (+) . A.map (\x -> x * x) $ A.zipWith (-) output expectedOutput')
                      (A.T3 (liftNetwork net) input expectedOutput)
        contribution = unliftNetwork net contribution'
        updatedNet = networkZip (A.zipWith (\x dx -> x - learnRate * dx)) net contribution
    in updatedNet

learnLoop :: A.Arrays a => Network A.Acc a -> A.Acc RowBatch -> A.Acc RowBatch -> Network A.Acc a
learnLoop initNet inputs expectedOutputs =
    let A.T3 res _ _ =
          A.awhile (\(A.T3 _ _ (A.the -> iter)) ->
                        A.unit (iter A.< 1000))
                   (\(A.T3 (unliftNetwork initNet -> net) seeds (A.the -> iter)) ->
                        let batchInputs = sampleBatch seeds inputs
                            batchOutputs = sampleBatch seeds expectedOutputs
                            net' = learnSingle net batchInputs batchOutputs
                        in A.T3 (liftNetwork net') (stepRandomArray seeds) (A.unit (iter + 1)))
                   (A.T3 (liftNetwork initNet)
                         (initialSeedArray 1 (Z_ ::. (100 :: A.Exp Int)))
                         (A.unit 0 :: A.Acc (A.Scalar Int)))
    in unliftNetwork initNet res

sampleBatch :: A.Acc (A.Array (Z :. Int) A.Word32) -> A.Acc RowBatch -> A.Acc RowBatch
sampleBatch seeds batch =
    let A.I2 available width = A.shape batch
        A.I1 rows = A.shape seeds
    in A.generate (A.I2 rows width)
                  (\(A.I2 i j) -> batch A.! (Z_ ::. A.fromIntegral (seeds A.! A.I1 i) `mod` available ::. j))


-- Uses the Wang hash: https://tomsmeding.com/blog/random.html
initialSeedArray :: A.Shape sh => A.Exp A.Word32 -> A.Exp sh -> A.Acc (A.Array sh A.Word32)
initialSeedArray seed0 sh =
    let seed0' = A.cond (seed0 A.== 0) (complement 0) seed0
    in A.reshape sh $
          A.generate (Z_ ::. A.shapeSize sh)
                     (\(A.I1 i) -> wangHash (seed0' + A.fromIntegral i))
  where
    wangHash :: A.Exp A.Word32 -> A.Exp A.Word32
    wangHash initx =
        initx & (\x -> complement x + (x `shiftL` 15))
              & (\x -> x `xor` (x `rotateR` 12))
              & (\x -> x + (x `shiftL` 2))
              & (\x -> x `xor` (x `rotateR` 4))
              & (\x -> x * 2057)
              & (\x -> x `xor` (x `rotateR` 16))

-- Uses the basic 32-bit xorshift PRNG
stepRandomArray :: A.Shape sh => A.Acc (A.Array sh A.Word32) -> A.Acc (A.Array sh A.Word32)
stepRandomArray = A.map xorshift
  where
    xorshift :: A.Exp A.Word32 -> A.Exp A.Word32
    xorshift initx =
        initx & (\x -> x `xor` (x `shiftL` 13))
              & (\x -> x `xor` (x `shiftR` 17))
              & (\x -> x `xor` (x `shiftL` 5))
