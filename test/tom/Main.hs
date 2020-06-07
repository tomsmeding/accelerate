{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Interpreter as I
import Data.Array.Accelerate (Z(..), (:.)(..))

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
                   (\_ -> A.lift Z)
                   (A.use (A.fromList (Z :. (10 :: Int)) [1::Float .. 10])))

main :: IO ()
main = do
  -- logistic
  -- optimise
  -- indexing
  -- apply
  ignoretest
