{-# LANGUAGE PatternSynonyms #-}
module Neural.Help where

import qualified Data.Array.Accelerate as A
import Data.Array.Accelerate.Data.Bits
import Data.Array.Accelerate (pattern Z_, pattern (::.))
import Data.Function ((&))


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
