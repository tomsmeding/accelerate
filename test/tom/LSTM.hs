{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module LSTM where

import Data.Functor.Identity
import Data.List (mapAccumL)
import System.Random

import qualified Data.Array.Accelerate as A
import Data.Array.Accelerate (pattern Z_, pattern (::.))

import Neural.Help

type Weights = A.Matrix Float

data LSTMCells a =
    LSTMCells { cForget :: (a, a)  -- (x, h)
              , cInput :: (a, a)
              , cCell :: (a, a)
              , cOutput :: (a, a) }
  deriving (Show, Functor)

instance Applicative LSTMCells where
    pure x = LSTMCells (x, x) (x, x) (x, x) (x, x)
    LSTMCells (f1, f2) (f3, f4) (f5, f6) (f7, f8) <*> LSTMCells (x1, x2) (x3, x4) (x5, x6) (x7, x8) =
        LSTMCells (f1 x1, f2 x2) (f3 x3, f4 x4) (f5 x5, f6 x6) (f7 x7, f8 x8)

type LSTMUnlifted a = (a, a, a, a, a, a, a, a)
type LSTMCellsState = (A.Vector Float, A.Vector Float)  -- (c, h)

data Network acc a state where
    InputLayer :: Network acc () ()
    DenseLayer :: A.Arrays a
               => acc Weights
               -> Network acc a state
               -> Network acc (a, Weights) state
    LSTMLayer :: (A.Arrays a, A.Arrays state)
              => LSTMCells (acc Weights)
              -> Network acc a state
              -> Network acc (a, LSTMUnlifted Weights) (state, LSTMCellsState)

data NetworkSpec a state where
    SInput :: Int -> NetworkSpec () ()
    SDense :: A.Arrays a => Int -> NetworkSpec a state -> NetworkSpec (a, Weights) state
    SLSTM :: (A.Arrays a, A.Arrays state) => Int -> NetworkSpec a state -> NetworkSpec (a, LSTMUnlifted Weights) (state, LSTMCellsState)

deriving instance A.Arrays a => Show (Network Identity a state)
deriving instance A.Arrays a => Show (Network A.Acc a state)
deriving instance Show (NetworkSpec a state)

liftLSTMCells :: A.Arrays a => LSTMCells (A.Acc a) -> A.Acc (LSTMUnlifted a)
liftLSTMCells (LSTMCells (fx, fh) (ix, ih) (cx, ch) (ox, oh)) = A.T8 fx fh ix ih cx ch ox oh

unliftLSTMCell :: A.Arrays a => A.Acc (LSTMUnlifted a) -> LSTMCells (A.Acc a)
unliftLSTMCell (A.T8 fx fh ix ih cx ch ox oh) = LSTMCells (fx, fh) (ix, ih) (cx, ch) (ox, oh)

unliftLSTMCell' :: A.Arrays a => LSTMUnlifted a -> LSTMCells a
unliftLSTMCell' (fx, fh, ix, ih, cx, ch, ox, oh) = LSTMCells (fx, fh) (ix, ih) (cx, ch) (ox, oh)

liftNetwork :: Network A.Acc a state -> A.Acc a
liftNetwork InputLayer = A.lift ()
liftNetwork (DenseLayer w net) = A.T2 (liftNetwork net) w
liftNetwork (LSTMLayer cw net) = A.T2 (liftNetwork net) (liftLSTMCells cw)

-- First argument only used as model for the types; its contained arrays are not inspected
unliftNetwork :: Network f a state -> A.Acc a -> Network A.Acc a state
unliftNetwork InputLayer _ = InputLayer
unliftNetwork (DenseLayer _ net) (A.T2 lnet w) = DenseLayer w (unliftNetwork net lnet)
unliftNetwork (LSTMLayer _ net) (A.T2 lnet cw) = LSTMLayer (unliftLSTMCell cw) (unliftNetwork net lnet)

-- First argument only used as model for the types; its contained arrays are not inspected
unliftNetwork' :: Network f a state -> a -> Network Identity a state
unliftNetwork' InputLayer _ = InputLayer
unliftNetwork' (DenseLayer _ net) (lnet, w) = DenseLayer (Identity w) (unliftNetwork' net lnet)
unliftNetwork' (LSTMLayer _ net) (lnet, cw) = LSTMLayer (Identity <$> unliftLSTMCell' cw) (unliftNetwork' net lnet)

useNetwork :: Network Identity a state -> Network A.Acc a state
useNetwork InputLayer = InputLayer
useNetwork (DenseLayer (Identity w) net) = DenseLayer (A.use w) (useNetwork net)
useNetwork (LSTMLayer cell net) = LSTMLayer (A.use . runIdentity <$> cell) (useNetwork net)

networkZip :: (A.Acc Weights -> A.Acc Weights -> A.Acc Weights) -> Network A.Acc a state -> Network A.Acc a state -> Network A.Acc a state
networkZip _ InputLayer InputLayer = InputLayer
networkZip f (DenseLayer w1 net1) (DenseLayer w2 net2) = DenseLayer (f w1 w2) (networkZip f net1 net2)
networkZip f (LSTMLayer cell1 net1) (LSTMLayer cell2 net2) = LSTMLayer (f <$> cell1 <*> cell2) (networkZip f net1 net2)


randomWeights :: Int -> Int -> IO Weights
randomWeights inw outw = A.fromList (A.Z A.:. outw A.:. inw) <$> sequence (replicate (inw * outw) (randomRIO (0.0, 1.0)))

randomLSTMCells :: Int -> Int -> IO (LSTMCells Weights)
randomLSTMCells inw outw =
    let genPair = (,) <$> randomWeights inw outw <*> randomWeights outw outw
    in LSTMCells <$> genPair <*> genPair <*> genPair <*> genPair

zeroNetState :: NetworkSpec a state -> state
zeroNetState (SInput _) = ()
zeroNetState (SDense _ net) = zeroNetState net
zeroNetState (SLSTM n net) =
    let zeros = A.fromList (A.Z A.:. n) (replicate n 0.0)
    in (zeroNetState net, (zeros, zeros))

randomNetwork :: NetworkSpec a state -> IO (Network Identity a state)
randomNetwork = fmap snd . go
  where
    -- Also returns output size
    go :: NetworkSpec a state -> IO (Int, Network Identity a state)
    go (SInput n) = return (n, InputLayer)
    go (SDense n net) = do
        (inw, net') <- go net
        w <- randomWeights inw n
        return (n, DenseLayer (Identity w) net')
    go (SLSTM n net) = do
        (inw, net') <- go net
        cell <- randomLSTMCells inw n
        return (n, LSTMLayer (Identity <$> cell) net')


-- layers: from closest to input, to output layer; Z :. output :. input
-- input/output: plain vector
forward :: A.Arrays state => Network A.Acc a state -> A.Acc state -> A.Acc (A.Vector Float) -> A.Acc (A.Vector Float, state)
forward InputLayer state i = A.T2 i state
forward (DenseLayer ws net) state i =
    let A.T2 res state' = forward net state i
        res' = A.map sigmoid (ws `matvec` res)
    in A.T2 res' state'
forward (LSTMLayer cell net) (A.T2 state cellstate) i =
    let A.T2 res state' = forward net state i
        A.T2 res' cellstate' = runLSTMCell cell cellstate res
    in A.T2 res' (A.T2 state' cellstate')

runLSTMCell :: LSTMCells (A.Acc Weights) -> A.Acc LSTMCellsState -> A.Acc (A.Vector Float) -> A.Acc (A.Vector Float, LSTMCellsState)
runLSTMCell cell (A.T2 c_prev h_prev) input =
    let fval = A.map sigma_g (A.zipWith (+) (fst (cForget cell) `matvec` input) (snd (cForget cell) `matvec` h_prev))
        ival = A.map sigma_g (A.zipWith (+) (fst (cInput  cell) `matvec` input) (snd (cInput  cell) `matvec` h_prev))
        cval = A.map sigma_c (A.zipWith (+) (fst (cCell   cell) `matvec` input) (snd (cCell   cell) `matvec` h_prev))
        oval = A.map sigma_g (A.zipWith (+) (fst (cOutput cell) `matvec` input) (snd (cOutput cell) `matvec` h_prev))
        c_new = A.zipWith (+) (A.zipWith (*) c_prev fval) (A.zipWith (*) ival cval)
        h_new = A.zipWith (*) oval (A.map sigma_h c_new)
    in A.T2 h_new (A.T2 c_new h_new)
  where
    sigma_g = sigmoid  -- for forget gate, input gate, output gate
    sigma_c = tanh     -- for cell gate
    sigma_h = tanh     -- for hidden state cell transformer

-- Input/output: Z :. sequence_item :. vector_component
-- TODO: downsides of the current limited language support are here:
--       - No free variable references in the expression under gradientA, so have to compute gradient for more stuff than I need
--       - No loop support, even for bounded loops, forcing me to statically unroll the loop
learnSingle :: (A.Arrays a, A.Arrays state) => Int -> Network A.Acc a state -> A.Acc state -> A.Acc (A.Matrix Float) -> A.Acc (A.Matrix Float) -> Network A.Acc a state
learnSingle seqLen net initState input expectedOutput =
    let learnRate = 0.05
        A.T4 contribution' _ _ _ =
          A.gradientA (\(A.T4 lnet input' state' expectedOutput') ->
                          let net' = unliftNetwork net lnet
                              (_, errors) = mapAccumL
                                  (\s (item, expectedOut) ->
                                       let A.T2 out s' = forward net' s item
                                       in (s', A.map (\x -> x*x) (A.zipWith (-) out expectedOut)))
                                  state'
                                  [(A.slice input' (Z_ ::. A.constant i ::. liftAll)
                                   ,A.slice expectedOutput' (Z_ ::. A.constant i ::. liftAll))
                                  | i <- [0 .. seqLen-1]]
                          in A.sum (foldl1 (A.zipWith (+)) errors))
                      (A.T4 (liftNetwork net) input initState expectedOutput)
        contribution = unliftNetwork net contribution'
        updatedNet = networkZip (A.zipWith (\x dx -> x - learnRate * dx)) net contribution
    in updatedNet

-- Input/output: Z :. test_case :. sequence_item :. vector_component
learnLoop :: (A.Arrays a, A.Arrays state) => Int -> Network A.Acc a state -> A.Acc state -> A.Acc (A.Array A.DIM3 Float) -> A.Acc (A.Array A.DIM3 Float) -> Network A.Acc a state
learnLoop seqLen initNet initState inputs expectedOutputs =
    let A.T3 res _ _ =
          A.awhile (\(A.T3 _ _ (A.the -> iter)) ->
                        A.unit (iter A.< 1000))
                   (\(A.T3 (unliftNetwork initNet -> net) seed (A.the -> iter)) ->
                        let batchInputs = sampleSequence seed inputs
                            batchOutputs = sampleSequence seed expectedOutputs
                            net' = learnSingle seqLen net initState batchInputs batchOutputs
                        in A.T3 (liftNetwork net') (stepRandomArray seed) (A.unit (iter + 1)))
                   (A.T3 (liftNetwork initNet)
                         (initialSeedArray 1 Z_)
                         (A.unit 0 :: A.Acc (A.Scalar Int)))
    in unliftNetwork initNet res

sampleSequence :: A.Acc (A.Scalar A.Word32) -> A.Acc (A.Array A.DIM3 Float) -> A.Acc (A.Matrix Float)
sampleSequence (A.the -> seed) batch =
    let A.I3 available _ _ = A.shape batch
    in A.slice batch (Z_ ::. A.fromIntegral seed `mod` available ::. liftAll ::. liftAll)
