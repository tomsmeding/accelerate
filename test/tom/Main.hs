{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Interpreter as I
import Data.Array.Accelerate (Z(..), (:.)(..), All(..))

import qualified ADHelp as AD
import qualified Logistic
import qualified Neural
import qualified Optimise


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
  print $ I.run $ Neural.matvec (A.use (A.fromList (Z :. 3 :. 4) [1..12]))
                                (A.use (A.fromList (Z :. 4) [10, 12, 13, 17]))
  print $ I.run $ Neural.matmat (A.use (A.fromList (Z :. 3 :. 4) [1..12]))
                                (A.use (A.fromList (Z :. 4 :. 3) [2..13]))

  let network1_l1 = A.use (A.fromList (Z :. 1 :. 3) [7.9, 3.9, -7.5])
      network1_l2 = A.use (A.fromList (Z :. 3 :. 3) [-5.6,4.6,-2.3, 2.4,2.2,0.5, -4.8,5.8,2.3])
      network1 =
          Neural.NextLayer network1_l1 $
          Neural.NextLayer network1_l2 $
          Neural.InputLayer
      input1 = A.use (A.fromList (Z :. 4 :. 3) [0,0,1, 0,1,1, 1,0,1, 1,1,1])
      output1 = A.use (A.fromList (Z :. 4 :. 1) [0, 1, 1, 0])
      lossfunc wanted got = A.fold1All (+) (A.zipWith (-) wanted got)

  print $ I.run $ Neural.forward network1 input1

  print $ I.run $ A.gradientA (\(A.T2 l1 l2) -> lossfunc output1 (Neural.forward (Neural.NextLayer l1 (Neural.NextLayer l2 Neural.InputLayer)) input1))
                              (A.T2 network1_l1 network1_l2)

indexing :: IO ()
indexing = do
  print $ I.run $ let store = A.use (A.fromList (Z :. 6) [1.0::Float .. 6])
                      source = A.use (A.fromList (Z :. 3) [42.0::Float, 10.0, 100.0])
                  in A.map (\(A.T2 idx x) -> let Z :. i = A.unlift idx :: Z :. A.Exp Int
                                             in (store A.! A.index1 (2 * i)) + x)
                           (A.indexed source)

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

  print . I.run $
      A.gradientA (\arr -> (A.sum . A.flatten) (A.map (\x -> x * x) (A.replicate (A.lift (Z :. (3 :: Int) :. All :. (2 :: Int) :. All)) arr)))
                  (A.use (A.fromList (Z :. 3 :. 4) [1 :: Float .. 12]))

main :: IO ()
main = do
  -- logistic
  -- optimise
  -- indexing
  -- apply
  -- ignoretest
  -- adtest
  -- adtest2
  -- adtest3
  -- adtuple1
  -- adtuple2
  -- adtuple3
  -- arrad
  neural
