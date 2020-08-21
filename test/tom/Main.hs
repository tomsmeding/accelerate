{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Interpreter as I
import Data.Array.Accelerate (Z(..), (:.)(..))

import qualified ADHelp as AD
import qualified Logistic
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

adtuple1 :: IO ()
adtuple1 = do
  print . I.run . A.unit $ A.gradientE @Float
    (\x -> let swap (A.T2 a b) = A.T2 b a
               x1 = A.T2 (A.T2 x (2 * x)) (3 * x)
               A.T2 y1 x2 = swap x1
               A.T2 _ y3 = x2
           in (3 * x) + y1 * x * y3)
    42

adtuple2 :: IO ()
adtuple2 = do
  print . I.run . A.unit $ A.gradientE @Float
    (\x -> let swap (A.T2 a b) = A.T2 b a
               x1 = A.cond (x A.> 0) (A.T2 3 4) (A.T2 1 2) :: A.Exp (Float, Float)
               x2 = A.T2 x1 (swap x1)
               A.T2 _ (A.T2 y2 _) = x2
               A.T2 y1 _ = x1
           in x * y1 * y2)
    42

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
  adtuple2
