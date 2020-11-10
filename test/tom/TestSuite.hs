{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module TestSuite (main) where

import Control.Monad (when)
import qualified Data.List as List
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty(..))
import Data.String (fromString)
import Hedgehog
import qualified Hedgehog.Gen as Gen
import Hedgehog.Gen (sized)
import qualified Hedgehog.Range as Range
import Hedgehog.Internal.Property (unPropertyName)
import System.Environment (getArgs, lookupEnv)
import System.Exit (exitSuccess, exitFailure, die)

import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Interpreter as I

import qualified ADHelp


-- Auxiliary functions and types
-- -----------------------------

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
sized_vec = Gen.scale (min 20) (sized vec)

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
compareAD' gen func = withShrinks 10 $ property $ do
  arrs <- forAll gen
  when False $ classify (fromString "totalSize > 5") (ADHelp.fdTotalSize arrs > 5)
  compareAD func arrs

compareADE :: Gen (A.Vector Float) -> (A.Exp Float -> A.Exp Float) -> Property
compareADE gen f = compareAD' gen $ \a -> A.sum (A.map f a)


-- Array tests
-- -----------

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

-- TODO: unit tests for the other combinators!
-- prop_reshape :: Property
-- prop_reshape = compareAD' sized_vec

prop_acond_1 :: Property
prop_acond_1 = compareAD' sized_vec $ \a ->
  let b = A.map (*2) a
      A.T2 a1 _ = A.acond (A.the (A.sum a) A.> 0) (A.T2 a b) (A.T2 b a)
  in A.sum (A.map (\x -> x * A.toFloating (A.indexHead (A.shape a1))) b)

prop_aindex_generate_1 :: Property
prop_aindex_generate_1 = compareAD' sized_vec $ \a ->
  let A.I1 n = A.shape a
  in A.sum (A.generate (A.I1 (n `div` 2))
                       (\(A.I1 i) -> a A.! A.I1 (2 * i)))

prop_aindex_generate_2 :: Property
prop_aindex_generate_2 = compareAD' sized_vec $ \a ->
  let A.I1 n = A.shape a
  in A.sum (A.generate (A.I1 (2 * n))
                       (\(A.I1 i) -> a A.! A.I1 (i `div` 2) + a A.! A.I1 (min (i `mod` 2) (n - 1))))

prop_aindex_generate_3 :: Property
prop_aindex_generate_3 = compareAD' sized_vec $ \a ->
  let A.I1 n = A.shape a
  in A.sum (A.generate (A.I1 (2 * n))
                       (\(A.I1 i) -> A.cond (i A.< 5) (a A.! A.I1 (i `div` 2)) 42))

prop_aindex_generate_4 :: Property
prop_aindex_generate_4 = compareAD' sized_vec $ \a ->
  let A.I1 n = A.shape a
  in A.sum (A.generate (A.I1 (2 * n))
                       (\(A.I1 i) -> A.cond (i A.< n) (a A.! A.I1 i) (a A.! A.I1 (i - n))))


-- Expression tests
-- ----------------

prop_cond_1 :: Property
prop_cond_1 = compareADE sized_vec $ \x ->
  let y = A.cond (x A.> 0) (A.sin (x * x)) (x * x * A.exp x)  -- derivative continuous at 0
  in 2 * y

prop_cond_2 :: Property
prop_cond_2 = compareADE sized_vec $ \x ->
  let fmod :: A.Exp Float -> A.Exp Float -> A.Exp Float
      fmod a b = a - A.fromIntegral (A.floor (a / b) :: A.Exp Int) * b
      y = A.cond (x `fmod` (2 * A.pi) A.< A.pi)  -- derivative continuous at all switching points
                 (A.sin x)
                 (A.pi / 12 * ((2 - 2 / A.pi * (x - A.pi / 2) `fmod` (2 * pi)) ^^ (6 :: Int) - 1))
  in y * y


-- Main and driver
-- ---------------

splitOn :: Eq a => a -> [a] -> NonEmpty [a]
splitOn _ [] = [] :| []
splitOn c (x:xs) =
  let r :| rs = splitOn c xs
  in if x == c then [] :| (r : rs) else (x:r) :| rs

data Pattern = Pattern String [String]

parsePattern :: String -> Pattern
parsePattern s =
  let p :| ps = splitOn '*' s
  in Pattern p ps

match :: Pattern -> PropertyName -> Bool
match (Pattern prefix segments) prop =
    let (pre, post) = splitAt (length prefix) (unPropertyName prop)
    in if pre == prefix then go segments post else False
  where
    go :: [String] -> String -> Bool
    go [] [] = True
    go [] _ = False
    go (seg:segs) s' =
        any (\tl -> let (pre, post) = splitAt (length seg) tl
                    in pre == seg && go segs post)
            (List.tails s')

{-# NOINLINE main #-}
main :: IO ()
main = do
  let Group gname props = $$(discover)

  -- Command-line arguments have precedence, but if none given an environment variable is checked.
  args <- getArgs >>= \case
    ["-h"] -> die "When given no parameters, runs full test suite. With parameters, or alternatively the ACCELERATE_AD_TEST_PROPS environment variable (in which patterns are separated with ','), only matching properties will be run. Patterns support * wildcards."

    [] -> lookupEnv "ACCELERATE_AD_TEST_PROPS" >>= \case
            Just s -> return (NonEmpty.toList (splitOn ',' s))
            Nothing -> return []

    l -> return l

  props' <- case args of
    [] -> return props

    testnames ->
      let pats = map parsePattern (testnames ++ map ("prop_" ++) testnames)
      in case List.filter (\(prop, _) -> any (`match` prop) pats) props of
           [] -> die "No matching properties found"
           props' -> return props'

  result <- checkParallel (Group gname props')
  if result then exitSuccess else exitFailure
