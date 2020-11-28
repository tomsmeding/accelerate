{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import Control.Monad
import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Interpreter as I
import Data.Array.Accelerate (Z(..), (:.)(..), All(..))
import System.CPUTime

import qualified ADHelp as AD
import qualified ConvNet
import qualified LSTM
import qualified Logistic
import qualified Neural
import qualified Optimise
import qualified Playground.Neural
import qualified Playground.Fusion
import qualified TestSuite


questionableBenchmark :: (Show a, Show b) => (a -> IO b) -> a -> IO (b, Double)
questionableBenchmark f x = do
  length (show x) `seq` return ()
  tm1 <- getCPUTime
  res <- f x
  length (show res) `seq` return ()
  tm2 <- getCPUTime
  return (res, fromInteger (tm2 - tm1) / 1e12)


logistic :: IO ()
logistic = do
  let theta = (A.fromList Z [-1.2], A.fromList (Z :. 2) [2, 1])
  print (Logistic.loglikelihood Logistic.dataset theta)
  print (I.run (Logistic.loglikelihoodAcc (A.use Logistic.dataset) (A.use theta)))
  -- print (I.run (A.map (A.gradientE id) (A.use (A.fromList Z [1.0 :: Float]))))

optimise :: IO ()
optimise = do
  let theta = A.fromList (Z :. Optimise.dimension) (repeat 0)
  print (I.run (Optimise.optimise (A.use theta) (A.use (A.fromList Z [0.3]))))

neural :: IO ()
neural = do
  -- print $ I.run $ Neural.matvec (A.use (A.fromList (Z :. 3 :. 4) [1..12]))
  --                               (A.use (A.fromList (Z :. 4) [10, 12, 13, 17]))
  -- print $ I.run $ Neural.matmat (A.use (A.fromList (Z :. 3 :. 4) [1..12]))
  --                               (A.use (A.fromList (Z :. 4 :. 3) [2..13]))

  let network1_l1 = A.fromList (Z :. 1 :. 3) [7.9, 3.9, -7.5]
      network1_l1' = A.use network1_l1
      network1_l2 = A.fromList (Z :. 3 :. 3) [-5.6,4.6,-2.3, 2.4,2.2,0.5, -4.8,5.8,2.3]
      network1_l2' = A.use network1_l2
      network1 =
          Neural.NextLayer network1_l1' $
          Neural.NextLayer network1_l2' $
          Neural.InputLayer
      input1 = A.use (A.fromList (Z :. 4 :. 3) [0,0,1, 0,1,1, 1,0,1, 1,1,1])
      output1 = A.use (A.fromList (Z :. 4 :. 1) [0, 1, 1, 0])
      lossfunc wanted got = A.fold1All (+) (A.map (\x -> x*x) (A.zipWith (-) wanted got))

  -- print $ I.run $ Neural.forward network1 input1

  -- print $ I.run1 (A.gradientA (\(A.T2 l1 l2) -> lossfunc output1 (Neural.forward (Neural.NextLayer l1 (Neural.NextLayer l2 Neural.InputLayer)) input1)))
  --                (network1_l1, network1_l2)

  -- print $ A.gradientA (\(A.T2 l1 l2) -> lossfunc output1 (Neural.forward (Neural.NextLayer l1 (Neural.NextLayer l2 Neural.InputLayer)) input1)) (A.T2 network1_l1' network1_l2')

  -- AD.aCompareAD (\(A.T2 l1 l2) -> lossfunc output1 (Neural.forward (Neural.NextLayer l1 (Neural.NextLayer l2 Neural.InputLayer)) input1))
  --               (network1_l1, network1_l2)

  print $ A.gradientA (\l1 -> lossfunc output1 (Neural.forward (Neural.NextLayer l1 Neural.InputLayer) input1)) network1_l1'

neural2 :: IO ()
neural2 = do
  let l1 = A.fromList (Z :. 1 :. 3) [0.99, 0.44, 0.66]
      l2 = A.fromList (Z :. 3 :. 3) [0.58, 0.31, 0.04, 0.90, 0.31, 0.86, 0.83, 0.77, 0.69]
      initNet = Neural.NextLayer (A.use l1) $
                Neural.NextLayer (A.use l2) $
                Neural.InputLayer
      input1 = A.use (A.fromList (Z :. 4 :. 3) [0,0,1, 0,1,1, 1,0,1, 1,1,1])
      output1 = A.use (A.fromList (Z :. 4 :. 1) [0, 1, 1, 0])

  let compiled = Neural.forward (Neural.learnLoop initNet input1 output1) input1
  questionableBenchmark (return . I.run) compiled >>= print
  print compiled
  -- print . I.run $ Neural.forward (Neural.learnLoop initNet input1 output1) input1

  -- print . I.run $ Neural.liftNetwork $ Neural.learnLoop initNet input1 output1

lstm :: IO ()
lstm = do
  let seqlen = 3 :: Int
  let combinations [] = [[]]
      combinations (l : ls) = concatMap (\x -> map (x :) (combinations ls)) l
      trainSet = [(input, map (fromIntegral . fromEnum) output)
                 | input <- combinations (replicate seqlen [0,1])
                 , let output = map (>= 2) (scanl1 (+) input)]
      trainInput = A.fromList @_ @Float (Z :. (2 ^ seqlen :: Int) :. seqlen :. (1 :: Int)) (concatMap fst trainSet)
      trainOutput = A.fromList @_ @Float (Z :. (2 ^ seqlen :: Int) :. seqlen :. (1 :: Int)) (concatMap snd trainSet)
      networkSpec = LSTM.SDense 1 (LSTM.SLSTM 2 (LSTM.SInput 1))
      zerostate = LSTM.zeroNetState networkSpec
  initnet <- LSTM.randomNetwork networkSpec
  let program = LSTM.liftNetwork (LSTM.learnLoop seqlen (LSTM.useNetwork initnet) (A.use zerostate) (A.use trainInput) (A.use trainOutput))
  -- print program
  let resnet = I.run program
      resnet' = LSTM.unliftNetwork' initnet resnet
  print resnet'
  forM_ trainSet $ \(input, output) -> do
    putStrLn ("==== INPUT: " ++ show input ++ "  OUTPUT: " ++ show output)
    foldM_ (\state' (inputItem, wantedOut) -> do
              let (out, state'') =
                    I.run1 (LSTM.forward (LSTM.useNetwork resnet') (A.use state'))
                           (A.fromList (Z :. (1 :: Int)) [inputItem])
              putStrLn ("  " ++ show inputItem ++ " -> " ++ show out ++
                          " (wanted=" ++ show wantedOut ++ ")")
              return state'')
           zerostate
           (zip input output)

convnet :: IO ()
convnet = do
  let networkSpec = ConvNet.SConv2dG (ConvNet.Geometry 1 2 1) ConvNet.ConvShrink $
                    ConvNet.SInput (ConvNet.Geometry 3 6 6)
      circle = [0,0,1,1,0,0
               ,0,1,0,0,1,0
               ,1,0,0,0,0,1
               ,1,0,0,0,0,1
               ,0,1,0,0,1,0
               ,0,0,1,1,0,0]
  initnet <- ConvNet.randomNetwork networkSpec
  print initnet
  print . I.run $
      A.reshape (A.lift (A.Z A.:. (5 :: Int) A.:. (6 :: Int))) $
      ConvNet.forward (ConvNet.useNetwork initnet)
                      (A.use (A.fromList (Z :. (3 :: Int) :. (6 :: Int) :. (6 :: Int)) (concat (replicate 3 circle))))

  let networkSpec2 = ConvNet.SConv2dS3x3 ConvNet.ConvShrink $
                     ConvNet.SInput (ConvNet.Geometry 1 6 6)
  initnet2 <- ConvNet.randomNetwork networkSpec2
  print . I.run $
      A.reshape (A.lift (A.Z A.:. (4 :: Int) A.:. (4 :: Int))) $
      ConvNet.forward (ConvNet.useNetwork initnet2)
                      (A.use (A.fromList (Z :. (1 :: Int) :. (6 :: Int) :. (6 :: Int)) circle))

indexing :: IO ()
indexing = do
  -- print $ I.run $ let store = A.use (A.fromList (Z :. (6 :: Int)) [1.0::Float .. 6])
  --                     source = A.use (A.fromList (Z :. 3) [42.0::Float, 10.0, 100.0])
  --                 in A.map (\(A.T2 (A.I1 i) x) -> (store A.! A.I1 (2 * i)) + x)
  --                          (A.indexed source)

  print . I.run $
    A.gradientA (\(A.T2 a b) -> A.sum (A.map (\x -> x * (a A.! A.I1 (2 * A.round x))) b))
                (A.T2 (A.use (A.fromList (Z :. (11 :: Int)) [1.0::Float ..]))
                      (A.use (A.fromList (Z :. (5 :: Int)) [1.0::Float ..])))

  print $
    A.gradientA (\a -> A.sum (A.generate (A.I1 5) (\(A.I1 i) -> A.cond (i A.> 2) (a A.! A.I1 (2 * i)) (a A.! A.I1 1))))
                (A.use (A.fromList (Z :. (10 :: Int)) [1.0::Float ..]))

apply :: IO ()
apply = do
  print $ I.run1 (A.map (*2)) (A.fromList (Z :. (10 :: Int)) [1.0::Float .. 10])
  let prog = A.map (\x -> (x :: A.Exp Float) * 2)
  print $ I.run1 prog (A.fromList (Z :. (10 :: Int)) [1.0::Float .. 10])
  print $ prog
  print $ I.run (let back = A.use (A.fromList (Z :. 5) [1.0::Float .. 5])
                 in A.generate (A.index1 100)
                               (\i -> back A.! A.index1 (A.unindex1 i `mod` A.length back)))

ignoretest :: IO ()
ignoretest = do
  -- ignore == Z, so can't permute onto a scalar
  print $ I.run
    (A.permute (+) (A.use (A.fromList Z [0]))
                   (\_ -> A.Just_ (A.lift Z))
                   (A.use (A.fromList (Z :. (10 :: Int)) [1::Float .. 10])))

adtest :: IO ()
adtest = do
  AD.compareAD (\x -> 2 * x)
               (\x -> 2 * x)
               5

  AD.compareAD (\x -> 2 * x * x)
               (\x -> 2 * x * x)
               5

  AD.compareAD (\(A.T2 x y) -> log (x + x * y))
               (\(x, y)     -> log (x + x * y))
               (5, 6)

  AD.compareAD (\x -> let A.T2 y z = A.T2 (log (x * x)) (log x) in y * z + z * y)
               (\x -> let (y, z)   =      (log (x * x),  log x) in y * z + z * y)
               5

  print $ I.run (A.unit (A.gradientE @Float (\x -> x * x + x) 4))

adtest2 :: IO ()
adtest2 = do
  print (I.run (A.map (A.gradientE (\x -> x * x))
                      (A.generate (A.index1 15) (\i -> A.toFloating @Int @Float (A.unindex1 i)))))

adtest3 :: IO ()
adtest3 = do
  print $ I.run (A.unit (A.gradientE @Float (\x -> A.toFloating @Int @Float (A.round x * 2)) 3))
  print $ I.run (A.map (A.gradientE @Float (\x -> A.cond (x A.> 0) (x + 1) (x * 2)))
                       (A.use (A.fromList (Z :. (11 :: Int)) [-5..5])))
  print . I.run . A.unit $ A.gradientE (\(A.T2 x i) -> x * A.toFloating (i `div` 2)) (A.T2 (42 :: A.Exp Float) (3 :: A.Exp Int))

adtest4 :: IO ()
adtest4 = do
  let prog = A.gradientE @Float (\x -> let a = 2 * x
                                           y = A.cond (x A.<= 2) (a + 1) (2 * a - 1)
                                       in y * a)
                                3
  print prog

adtestFree :: IO ()
adtestFree = do
  print $ I.run (A.map (let c = 1.0 in (c +) . A.gradientE @Float (\x -> c * x))
                       (A.use (A.fromList (Z :. (1 :: Int)) [1.0])))

  -- This still fails, because free variables in gradientA are not yet implemented.
  -- print $ I.run (let sharedArr = A.use (A.fromList @_ @Float (Z :. (1 :: Int)) [1.0])
  --                    arr1 = A.use (A.fromList @_ @Float (Z :. (1 :: Int)) [2.0])
  --                in A.zipWith (+) sharedArr (A.gradientA (A.sum . A.zipWith (*) sharedArr) arr1))

adtuple1 :: IO ()
adtuple1 = do
  print . I.run . A.unit $ A.gradientE @Float
    (\x -> let swap (A.T2 a b) = A.T2 b a
               swap _ = undefined
               x1 = A.T2 (A.T2 x (2 * x)) (3 * x)
               A.T2 y1 x2 = swap x1
               A.T2 _ y3 = x2
           in (3 * x) + y1 * x * y3)
    42
  -- expected output: 31755

adtuple2 :: IO ()
adtuple2 = do
  print . I.run . A.unit $ A.gradientE @Float
    (\x -> let swap (A.T2 a b) = A.T2 b a
               swap _ = undefined
               x1 = A.cond (x A.> 0) (A.T2 3 4) (A.T2 1 2) :: A.Exp (Float, Float)
               x2 = A.T2 x1 (swap x1)
               A.T2 _ (A.T2 y2 _) = x2
               A.T2 y1 _ = x1
           in x * y1 * y2)
    42
  -- expected output: 12

adtuple3 :: IO ()
adtuple3 = do
  print . I.run $
    A.map (A.gradientE @Float
                (\x -> let A.T2 a b = A.cond (x A.> 0) (A.T2 x 2) (A.T2 x 3) :: A.Exp (Float, Float)
                       in a * b))
          (A.use (A.fromList (Z :. (5 :: Int)) [-3, -2, 0, 2, 3]))

arrad :: IO ()
arrad = do
  -- print . I.run $
  --   A.gradientA (\arr -> A.sum (A.map (\x -> x * x) arr))
  --               (A.use (A.fromList (Z :. (5 :: Int)) [1 :: Float, 2, 3, 4, 5]))

  -- print . I.run $
  --   A.gradientA (\arr -> A.sum (A.map (\x -> x * log x) (A.map (\x -> 2 * (x + 3)) arr)))
  --               (A.use (A.fromList (Z :. (5 :: Int)) [1 :: Float, 2, 3, 4, 5]))

  -- print . I.run $
  --   A.map (\x -> 2 + 2 * log 2 + 2 * log (x + 3))
  --       (A.use (A.fromList (Z :. (5 :: Int)) [1 :: Float, 2, 3, 4, 5]))

  -- print . I.run $
  --   A.gradientA (\arr -> A.sum (A.map (\x -> A.toFloating (A.unindex1 (A.shape arr)) * x) arr))
  --               (A.use (A.fromList (Z :. (6 :: Int)) [1 :: Float, 2, 3, 4, 5, 6]))

  -- print . I.run $
  --   A.gradientA (\arr ->
  --                   let a1 = A.map (\x -> 2 * x) arr
  --                       a2 = A.map (\x -> log x) arr
  --                       a3 = A.map (\x -> x + 3) a1
  --                   in A.sum (A.map (\x -> let i1 = A.toFloating (A.unindex1 (A.shape a1))
  --                                              i2 = A.toFloating (A.unindex1 (A.shape a2))
  --                                              i3 = A.toFloating (A.unindex1 (A.shape a3))
  --                                          in i1 * i2 * i3 * x)
  --                                   arr))
  --               (A.use (A.fromList (Z :. (6 :: Int)) [1 :: Float, 2, 3, 4, 5, 6]))
  -- -- expected result: 6 * 6 * 6 = 216

  -- print $
  --   A.gradientA (\arr -> A.sum (A.map (\x -> x * x * x + 2 * x) arr))
  --               (A.use (A.fromList (Z :. (6 :: Int)) [1 :: Float, 2, 3, 4, 5, 6]))

  -- print . I.run $
  --   A.gradientA (\a -> A.sum (A.zipWith (\x y -> x * x * y + 2 * y) a (A.map (+6) a)))
  --               (A.use (A.fromList (Z :. (6 :: Int)) [1 :: Float, 2, 3, 4, 5, 6]))

  -- print . I.run $
  --   A.gradientA (\(A.T2 a1 a2) -> A.sum (A.zipWith (\x y -> x * x * y + 2 * y) a1 a2))
  --               (A.T2 (A.use (A.fromList (Z :. (6 :: Int)) [1 :: Float, 2, 3, 4, 5, 6]))
  --                     (A.use (A.fromList (Z :. (6 :: Int)) [7, 8, 9, 10, 11, 12])))

  -- print . I.run $
  --     A.gradientA (\arr -> (A.sum . A.flatten) (A.map (\x -> x * x) (A.replicate (A.lift (Z :. (3 :: Int) :. All :. (2 :: Int) :. All)) arr)))
  --                 (A.use (A.fromList (Z :. 3 :. 4) [1 :: Float .. 12]))

  print . I.run $
      A.gradientA (\arr -> A.sum $ A.zipWith (*) arr (A.generate (A.shape arr) (\(A.I1 i) -> A.cond (i A.< 5) 0 1)))
                  (A.use (A.fromList (Z :. 10) [1 :: Float .. 10]))

adfold :: IO ()
adfold = do
  -- print $
  --     A.gradientA (\arr -> A.maximum arr)
  --                 (A.use (A.fromList (Z :. 10) [1 :: Float .. 10]))
  let input = A.fromList (Z :. 8) [1 :: Float .. 8]

  AD.aCompareAD (\arr -> A.maximum arr) input
  AD.aCompareAD (\arr -> A.product arr) input

  print $
      A.gradientA (\arr -> let p = A.product arr
                         in A.zipWith (+) (A.map (*2) p) (A.map (*3) p))
                  (A.use input)

main :: IO ()
main = do
  TestSuite.main
  -- logistic
  -- optimise
  -- indexing
  -- apply
  -- ignoretest
  -- adtest
  -- adtest2
  -- adtest3
  -- adtest4
  -- adtestFree
  -- adtuple1
  -- adtuple2
  -- adtuple3
  -- arrad
  -- adfold
  -- neural
  -- neural2
  -- Playground.Neural.main
  -- lstm
  -- convnet
  -- Playground.Fusion.main
