{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
module ADHelp where

import Data.List (intercalate)

import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Interpreter as I
import Data.Array.Accelerate (Z(..))


class (A.Elt a, A.Lift A.Exp a, a ~ A.Plain a) => FinDiff a where
  hfindiff :: Float -> (a -> Float) -> a -> a

  findiff :: (a -> Float) -> a -> a
  findiff = hfindiff 1e-5

instance FinDiff Float where
  hfindiff h f x = (f (x + h) - f (x - h)) / (2 * h)

instance (FinDiff a, FinDiff b) => FinDiff (a, b) where
  hfindiff h f (x, y) = (hfindiff h (\x' -> f (x', y)) x, hfindiff h (\y' -> f (x, y')) y)

instance (FinDiff a, FinDiff b, FinDiff c) => FinDiff (a, b, c) where
  hfindiff h f (x, y, z) = (hfindiff h (\x' -> f (x', y, z)) x, hfindiff h (\y' -> f (x, y', z)) y, hfindiff h (\z' -> f (x, y, z')) z)


runAcc :: (FinDiff a, A.Elt b) => (A.Exp a -> A.Exp b) -> a -> b
runAcc f x =
  let res = I.run (A.unit (f (A.lift x)))
  in A.indexArray res Z

compareAD :: FinDiff a => (A.Exp a -> A.Exp Float) -> (a -> Float) -> a -> IO ()
compareAD facc fnative x =
  let res1 = runAcc (A.gradientE facc) x
      res2 = [hfindiff (10.0 ** ex) fnative x | ex <- [-3, -4, -5]]
  in do
      putStrLn ("\x1B[1mAccelerate AD: " ++ show res1 ++ "\x1B[0m")
      putStrLn ("\x1B[1mFinite differencing: " ++ intercalate ", " (map show res2) ++ "\x1B[0m")
