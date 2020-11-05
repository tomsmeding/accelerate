{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module TestSuite (main) where

import Control.Monad (when)
import qualified Data.List as List
import Hedgehog
import qualified Hedgehog.Gen as Gen
import Hedgehog.Gen (sized)
import qualified Hedgehog.Range as Range
import System.Exit (exitSuccess, exitFailure)

import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Interpreter as I

import qualified ADHelp


data ShapeType sh where
  SZ :: ShapeType A.Z
  SCons :: ShapeType sh -> ShapeType (sh A.:. Int)

class A.Shape sh => Shape sh where
  magicShapeType :: ShapeType sh

instance Shape A.Z where
  magicShapeType = SZ

instance Shape sh => Shape (sh A.:. Int) where
  magicShapeType = SCons magicShapeType

shapeSize :: Shape sh => sh -> Int
shapeSize = go magicShapeType
  where go :: ShapeType sh -> sh -> Int
        go SZ _ = 1
        go (SCons st) (sh A.:. n) = n * go st sh

genArray :: (A.Elt e, Shape sh) => Gen e -> sh -> Gen (A.Array sh e)
genArray genElt shape = A.fromList shape <$> sequence (replicate (shapeSize shape) genElt)

genFloat :: Gen Float
genFloat = Gen.float (Range.linearFrac (-10) 10)

vec :: Size -> Gen (A.Vector Float)
vec (Size n) = genArray (Gen.float (Range.linearFrac (-10) 10)) (A.Z A.:. n)

sized_vec :: Gen (A.Vector Float)
sized_vec = Gen.scale (min 50) (sized vec)

t2_ :: Gen a -> Gen b -> Gen (a, b)
t2_ a b = Gen.small ((,) <$> a <*> b)

uniqueMax :: (A.Elt a, Ord a, Fractional a) => A.Vector a -> Bool
uniqueMax v = let m = maximum (A.toList v)
              in sum (map (fromEnum . (>= m - 0.5)) (A.toList v)) <= 1


findiff :: ADHelp.AFinDiff a => (A.Acc a -> A.Acc (A.Scalar Float)) -> a -> a
findiff func = ADHelp.afdrOLS . ADHelp.afindiffPerform func

-- Relative difference (abs (x - y) / max (abs x) (abs y)) is allowed to be at
-- most 0.1; except if x and y are both small, then the absolute difference is
-- allowed to be at most 0.1.
checkApproxEqual :: (MonadTest m, ADHelp.AFinDiff a) => a -> a -> m ()
checkApproxEqual aGrad aFD =
  let diffs = ADHelp.fdfmap (\[x,y] -> abs (x - y) / max 1 (max (abs x) (abs y))) [aGrad, aFD]
      correct = List.foldl' max 0 (ADHelp.fdtoList diffs) < 0.1
  in when (not correct) $ diff aGrad (\_ _ -> False) aFD >> failure

compareAD :: (MonadTest m, ADHelp.AFinDiff a) => (A.Acc a -> A.Acc (A.Scalar Float)) -> a -> m ()
compareAD func arg = checkApproxEqual (I.run1 (A.gradientA func) arg) (findiff func arg)

compareAD' :: (Show a, ADHelp.AFinDiff a, A.Arrays a)
           => Gen a -> (A.Acc a -> A.Acc (A.Scalar Float)) -> Property
compareAD' gen func = withShrinks 10 $ property $ forAll gen >>= compareAD func


prop_map :: Property
prop_map = compareAD' sized_vec $ \a -> A.sum (A.map (*3) a)

prop_zipWith :: Property
prop_zipWith = compareAD' (t2_ sized_vec sized_vec) $
  \(A.T2 a b) -> A.sum (A.zipWith (\x y -> sin x * cos (x + y)) a b)

prop_fold_1 :: Property
prop_fold_1 = compareAD' sized_vec $ \a -> A.fold (*) 1 a

prop_fold_2 :: Property
prop_fold_2 = compareAD' (Gen.filter uniqueMax sized_vec) $ \a -> A.fold A.max 3 a

prop_fold1_1 :: Property
prop_fold1_1 = compareAD' sized_vec $ \a -> A.fold1 (*) a

prop_fold1_2 :: Property
prop_fold1_2 = compareAD' (Gen.filter uniqueMax sized_vec) $ \a -> A.fold1 A.max a

prop_replicate_1 :: Property
prop_replicate_1 = compareAD' sized_vec $ \a ->
  A.product . A.sum
    . A.map (*2) . A.replicate (A.I2 (A.constant A.All) (5 :: A.Exp Int))
    . A.map (\x -> x * x + x) $ a

prop_replicate_2 :: Property
prop_replicate_2 = compareAD' sized_vec $ \a ->
  A.fold1All (+)
    . A.map (/20) . A.replicate (A.I2 (5 :: A.Exp Int) (A.constant A.All))
    . A.map (\x -> x * x + x) $ a

prop_replicate_3 :: Property
prop_replicate_3 = compareAD' (Gen.small sized_vec) $ \a ->
  A.fold1All (+) . A.map (*2)
    . A.replicate (A.I4 (A.constant A.All) (5 :: A.Exp Int) (A.constant A.All) (3 :: A.Exp Int))
    . A.map (\x -> x * x + x)
    . A.replicate (A.I2 (A.constant A.All) (2 :: A.Exp Int))
    $ a

prop_replicate_4 :: Property
prop_replicate_4 = compareAD' (Gen.small sized_vec) $ \a ->
  A.fold1All (+) . A.map (*2)
    . A.replicate (A.I4 (5 :: A.Exp Int) (A.constant A.All) (3 :: A.Exp Int) (A.constant A.All))
    . A.map (\x -> x * x + x)
    . A.replicate (A.I2 (A.constant A.All) (2 :: A.Exp Int))
    $ a

-- prop_reshape :: Property
-- prop_reshape = compareAD' sized_vec


{-# NOINLINE main #-}
main :: IO ()
main = do
  result <- checkParallel $$(discover)
  if result then exitSuccess else exitFailure
