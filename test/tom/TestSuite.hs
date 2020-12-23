{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module TestSuite (main) where

import Control.Monad (when)
import qualified Data.List as List
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty(..))
import Data.String (fromString)
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Hedgehog.Internal.Property (unPropertyName)
import System.Environment (getArgs, lookupEnv)
import System.Exit (exitSuccess, exitFailure, die)

import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Data.Bits as A
import qualified Data.Array.Accelerate.Interpreter as I
import qualified Data.Array.Accelerate.ForwardAD as ADF

import qualified ADHelp
import TestSuite.Util


-- Auxiliary functions and types
-- -----------------------------

disjointUnion :: [a] -> [b] -> [Either a b]
disjointUnion as bs = map Left as ++ map Right bs

genArray :: (A.Elt e, Shape sh) => Gen e -> sh -> Gen (A.Array sh e)
genArray genElt shape = A.fromList shape <$> sequence (replicate (shapeSize shape) genElt)

genFloat :: Gen Float
genFloat = Gen.float (Range.linearFrac (-10) 10)

vec :: Size -> Gen (A.Vector Float)
vec (Size n) = genArray (Gen.float (Range.linearFracFrom 0 (-10) 10)) (A.Z A.:. n)

sized_vec :: Gen (A.Vector Float)
sized_vec = Gen.scale (min 20) (Gen.sized vec)

nil :: Gen ()
nil = return ()

t2_ :: Gen a -> Gen b -> Gen (a, b)
t2_ a b = Gen.small ((,) <$> a <*> b)

uniqueMax :: (A.Elt a, Ord a, Fractional a) => A.Vector a -> Bool
uniqueMax v = let m = maximum (A.toList v)
              in sum (map (fromEnum . (>= m - 0.5)) (A.toList v)) <= 1

allNiceRound :: (A.Elt a, RealFrac a) => A.Vector a -> Bool
allNiceRound =
  all (\x -> let x' = x - fromIntegral (round x :: Int) in -0.4 < x' && x' < 0.4)
    . A.toList


-- This is not a typeclass because the types don't work out.
gradientFwdAD :: Shape sh
              => A.Array sh Float
              -> (forall a. ADF.ADFClasses a => A.Acc (A.Array sh a) -> A.Acc (A.Scalar a))
              -> A.Array sh Float
gradientFwdAD input func =
  A.fromList (A.arrayShape input)
             [ADF.derivativePlain $ (`A.linearIndexArray` 0) $ I.run1 func $
                 A.fromFunction (A.arrayShape input)
                                (\j -> let x = input `A.indexArray` j
                                       in if j == idx then ADF.variablePlain x
                                                      else ADF.constantPlain x)
             | idx <- enumShape (A.arrayShape input)]

gradientFwdAD2 :: (Shape sh1, Shape sh2)
               => (A.Array sh1 Float, A.Array sh2 Float)
               -> (forall a. ADF.ADFClasses a => A.Acc (A.Array sh1 a) -> A.Acc (A.Array sh2 a) -> A.Acc (A.Scalar a))
               -> (A.Array sh1 Float, A.Array sh2 Float)
gradientFwdAD2 (input1, input2) func =
  let grad =
        [ADF.derivativePlain $ (`A.linearIndexArray` 0) $ I.runN func
            (A.fromFunction (A.arrayShape input1)
                            (\j -> let x = input1 `A.indexArray` j
                                   in if Left j == eidx then ADF.variablePlain x
                                                        else ADF.constantPlain x))
            (A.fromFunction (A.arrayShape input2)
                            (\j -> let x = input2 `A.indexArray` j
                                   in if Right j == eidx then ADF.variablePlain x
                                                         else ADF.constantPlain x))
        | eidx <- disjointUnion (enumShape (A.arrayShape input1))
                                (enumShape (A.arrayShape input2))]
      (pre, post) = splitAt (A.arraySize input1) grad
  in (A.fromList (A.arrayShape input1) pre, A.fromList (A.arrayShape input2) post)


findiff :: ADHelp.AFinDiff a => (A.Acc a -> A.Acc (A.Scalar Float)) -> a -> ((String, Float), a)
findiff func = ADHelp.afdrOLS' . ADHelp.afindiffPerform func

-- Relative difference (abs (x - y) / max (abs x) (abs y)) is allowed to be at
-- most 0.1; except if x and y are both small, then the absolute difference is
-- allowed to be at most 0.1.
isApproxEqual :: ADHelp.AFinDiff a => a -> a -> (a, Bool)
isApproxEqual a1 a2 =
  let diffs = ADHelp.fdfmap (\[x,y] -> abs (x - y) / max 1 (max (abs x) (abs y))) [a1, a2]
  in (diffs, List.foldl' max 0 (ADHelp.fdtoList diffs) < 0.1)

checkApproxEqual :: (MonadTest m, ADHelp.AFinDiff a) => a -> a -> m ()
checkApproxEqual aGrad aControl =
  let (diffs, correct) = isApproxEqual aControl aGrad
  in do footnote ("approx-equality diffs: " ++ show diffs)
        when (not correct) $ diff aControl (\_ _ -> False) aGrad >> failure

compareADE :: Gen (A.Vector Float) -> (forall a. ADF.ADFClasses a => A.Exp a -> A.Exp a) -> Property
compareADE gen f = compareAD' nil gen $ \() a -> A.sum (A.map f a)

compareAD' :: (Show e, Shape sh) => Gen e -> Gen (A.Array sh Float) -> (forall a. ADF.ADFClasses a => e -> A.Acc (A.Array sh a) -> A.Acc (A.Scalar a)) -> Property
compareAD' egen gen func = withShrinks 10 $ property $ do
  expval <- forAll egen
  arr <- forAll gen
  let revadResult = I.run1 (A.gradientA (func expval)) arr
      fwdadResult = gradientFwdAD arr (func expval)
      (_, fdResult) = findiff (func expval) arr
  checkApproxEqual revadResult fwdadResult
  if snd (isApproxEqual fdResult fwdadResult)
      then checkApproxEqual revadResult fdResult
      else label (fromString "Warning: FD and forward AD do not agree")

compareAD'2 :: (Show e, Shape sh1, Shape sh2)
            => Gen e
            -> Gen (A.Array sh1 Float)
            -> Gen (A.Array sh2 Float)
            -> (forall a. ADF.ADFClasses a => e -> A.Acc (A.Array sh1 a) -> A.Acc (A.Array sh2 a) -> A.Acc (A.Scalar a))
            -> Property
compareAD'2 egen gen1 gen2 func = withShrinks 10 $ property $ do
  expval <- forAll egen
  arr1 <- forAll gen1
  arr2 <- forAll gen2
  let revadResult = I.runN (A.gradientA (\(A.T2 a1 a2) -> func expval a1 a2)) (arr1, arr2)
      fwdadResult = gradientFwdAD2 (arr1, arr2) (func expval)
      (_, fdResult) = findiff (\(A.T2 a1 a2) -> func expval a1 a2) (arr1, arr2)
  checkApproxEqual revadResult fwdadResult
  if snd (isApproxEqual fdResult fwdadResult)
      then checkApproxEqual revadResult fdResult
      else label (fromString "Warning: FD and forward AD do not agree")


-- Array tests
-- -----------

prop_acond_1 :: Property
prop_acond_1 = compareAD' nil sized_vec $ \() a ->
  let b = A.map (*2) a
      A.T2 a1 _ = A.acond (A.the (A.sum a) A.> 0) (A.T2 a b) (A.T2 b a)
  in A.sum (A.map (\x -> x * A.toFloating (A.indexHead (A.shape a1))) b)

-- This property, as well as prop_acond_2b, test ATTEMPT TO that Cond isn't
-- over-eager in finding the contents of its branches.
-- The tests apparently don't test well enough, because they don't find the bug.
prop_acond_2a :: Property
prop_acond_2a = compareAD' nil sized_vec $ \() x ->
  let a = A.map (2*) x
      y = A.acond (A.the (A.sum x) A.<= 2) (A.map (+1) a) (A.map (subtract 1) (A.map (2*) a))
  in A.sum (A.zipWith (*) a y)

prop_acond_2b :: Property
prop_acond_2b = compareAD' nil sized_vec $ \() x ->
  let a = A.map (2*) x
      y = A.acond (A.the (A.sum x) A.<= 2) (A.map (+1) a) (A.map (subtract 1) (A.map (2*) a))
  in A.sum (A.zipWith (*) y a)

prop_map :: Property
prop_map = compareAD' nil sized_vec $ \() a -> A.sum (A.map (*3) a)

prop_zipWith :: Property
prop_zipWith = compareAD'2 nil sized_vec sized_vec $
  \() a b -> A.sum (A.zipWith (\x y -> sin x * cos (x + y)) a b)

prop_fold_1 :: Property
prop_fold_1 = compareAD' nil sized_vec $ \() a -> A.fold (*) 1 a

prop_fold_2 :: Property
prop_fold_2 = compareAD' nil sized_vec $ \() a -> A.fold A.max 3 a

prop_fold1_1 :: Property
prop_fold1_1 = compareAD' nil sized_vec $ \() a -> A.fold1 (*) a

prop_fold1_2 :: Property
prop_fold1_2 = compareAD' nil sized_vec $ \() a -> A.fold1 A.max a

prop_fold1_2_friendly :: Property
prop_fold1_2_friendly = compareAD' nil (Gen.filter uniqueMax sized_vec) $ \() a -> A.fold1 A.max a

prop_replicate_1 :: Property
prop_replicate_1 = compareAD' nil sized_vec $ \() a ->
  A.product . A.sum
    . A.map (*2) . A.replicate (A.I2 (A.constant A.All) (5 :: A.Exp Int))
    . A.map (\x -> x * x + x) $ a

prop_replicate_2 :: Property
prop_replicate_2 = compareAD' nil sized_vec $ \() a ->
  A.fold1All (+)
    . A.map (/20) . A.replicate (A.I2 (5 :: A.Exp Int) (A.constant A.All))
    . A.map (\x -> x * x + x) $ a

prop_replicate_3 :: Property
prop_replicate_3 = compareAD' nil (Gen.small sized_vec) $ \() a ->
  A.fold1All (+) . A.map (*2)
    . A.replicate (A.I4 (A.constant A.All) (5 :: A.Exp Int) (A.constant A.All) (3 :: A.Exp Int))
    . A.map (\x -> x * x + x)
    . A.replicate (A.I2 (A.constant A.All) (2 :: A.Exp Int))
    $ a

prop_replicate_4 :: Property
prop_replicate_4 = compareAD' nil (Gen.small sized_vec) $ \() a ->
  A.fold1All (+) . A.map (*2)
    . A.replicate (A.I4 (5 :: A.Exp Int) (A.constant A.All) (3 :: A.Exp Int) (A.constant A.All))
    . A.map (\x -> x * x + x)
    . A.replicate (A.I2 (A.constant A.All) (2 :: A.Exp Int))
    $ a

prop_slice_1 :: Property
prop_slice_1 = compareAD' nil sized_vec $ \() a ->
  let A.I1 n = A.shape a
      m = n `div` 4 + 3
      a1 = A.replicate (A.I3 m m cAll) a
  in A.sum (A.slice a1 (A.I3 (2 :: A.Exp Int) (1 :: A.Exp Int) cAll))
  where cAll = A.constant A.All

prop_slice_2 :: Property
prop_slice_2 = compareAD' (t2_ intgen intgen) (Gen.small sized_vec) $ \(p1, p2) a ->
  let A.I1 n = A.shape a
      a1 = A.backpermute (A.I3 n n (n+1))
                         (\(A.I3 i j k) -> A.I1 ((i + j + k) `mod` n))
                         a
  in A.sum (A.slice a1 (A.I3 (A.constant p1 `mod` n) (A.constant p2 `mod` n) cAll))
  where cAll = A.constant A.All
        intgen = Gen.int (Range.linear 0 100)

prop_reshape_1 :: Property
prop_reshape_1 = compareAD' nil (Gen.filter (even . A.arraySize) sized_vec) $ \() a ->
  let A.I1 n = A.shape a
      b = A.reshape (A.I2 2 (n `div` 2)) a
  in A.product (A.sum b)

prop_reshape_2 :: Property
prop_reshape_2 = compareAD' nil (Gen.filter (even . A.arraySize) sized_vec) $ \() a ->
  let A.I1 n = A.shape a
      b = A.reshape (A.I2 (2 :: A.Exp Int) (n `div` 2)) a
      c = A.reshape (A.I2 n 1) b
  in A.sum (A.product c)

prop_backpermute_1 :: Property
prop_backpermute_1 =
  compareAD' (Gen.int (Range.linear 5 15))
              (Gen.filter ((> 0) . A.arraySize) sized_vec)
  $ \m a ->
    let A.I1 n = A.shape a
        b = A.backpermute (A.I2 (A.constant m) (2 * A.constant m))
                          (\(A.I2 i j) -> A.I1 ((i + j) `mod` n))
                          a
    in A.fold1All (+) b

prop_backpermute_2 :: Property
prop_backpermute_2 =
  compareAD' (Gen.int (Range.linear 5 15))
              (Gen.filter ((> 0) . A.arraySize) sized_vec)
  $ \m a ->
    let A.I1 n = A.shape a
        b = A.backpermute (A.I2 (A.constant m) (2 * A.constant m))
                          (\(A.I2 i j) -> A.I1 ((i + j) `mod` n))
                          a
        c = A.sum b
        d = A.backpermute (A.I3 (2 :: A.Exp Int) (3 :: A.Exp Int) (A.constant m))
                          (\(A.I3 _ i j) -> A.I1 (min (A.constant m - 1) (i * j)))
                          c
        e = A.map (/2) d
        f = A.slice e (A.I3 (A.constant A.All) (A.constant A.All) (2 :: A.Exp Int))
    in A.fold1All (+) f

prop_aindex_generate_1 :: Property
prop_aindex_generate_1 = compareAD' nil sized_vec $ \() a ->
  let A.I1 n = A.shape a
  in A.sum (A.generate (A.I1 (n `div` 2))
                       (\(A.I1 i) -> a A.! A.I1 (2 * i)))

prop_aindex_generate_2 :: Property
prop_aindex_generate_2 = compareAD' nil sized_vec $ \() a ->
  let A.I1 n = A.shape a
  in A.sum (A.generate (A.I1 (2 * n))
                       (\(A.I1 i) -> a A.! A.I1 (i `div` 2) + a A.! A.I1 (min (i `mod` 2) (n - 1))))

prop_aindex_generate_3 :: Property
prop_aindex_generate_3 = compareAD' nil sized_vec $ \() a ->
  let A.I1 n = A.shape a
  in A.sum (A.generate (A.I1 (2 * n))
                       (\(A.I1 i) -> A.cond (i A.< 5) (a A.! A.I1 (i `div` 2)) 42))

-- gradientA (\a -> let I1 n = shape (a :: Acc (Vector Float)) in sum (generate (I1 (2 * n)) (\(I1 i) -> cond (i < n) (a ! I1 i) (a ! I1 (i - n)))))
prop_aindex_generate_4 :: Property
prop_aindex_generate_4 = compareAD' nil sized_vec $ \() a ->
  let A.I1 n = A.shape a
  in A.sum (A.generate (A.I1 (2 * n))
                       (\(A.I1 i) -> A.cond (i A.< n) (a A.! A.I1 i) (a A.! A.I1 (i - n))))

prop_aindex_map_1 :: Property
prop_aindex_map_1 = compareAD' nil (Gen.filter ((>= 3) . A.arraySize) sized_vec) $ \() a ->
  A.sum (A.map (\x -> x + a A.! A.I1 2) a)

prop_aindex_map_2 :: Property
prop_aindex_map_2 = compareAD' nil sized_vec $ \() a ->
  let A.I1 n = A.shape a
  in A.sum (A.map (\x -> x + a A.! A.I1 (A.abs (A.round x) `mod` n)) a)

prop_aindex_map_2_friendly :: Property
prop_aindex_map_2_friendly = compareAD' nil (Gen.filter allNiceRound sized_vec) $ \() a ->
  let A.I1 n = A.shape a
  in A.sum (A.map (\x -> x + a A.! A.I1 (A.abs (A.round x) `mod` n)) a)

prop_aindex_map_3 :: Property
prop_aindex_map_3 = compareAD' nil sized_vec $ \() a ->
  let A.I1 n = A.shape a
      b = A.fold max (-20)
                 (A.backpermute (A.I2 n n) (\(A.I2 i j) -> A.I1 (i A..&. j)) a)
  in A.sum (A.map (\x -> x * b A.! A.I1 (A.abs (A.round x) `mod` n)) a)

prop_aindex_map_3_friendly :: Property
prop_aindex_map_3_friendly = withDiscards 1000 $ compareAD' nil (Gen.filter (\a -> allNiceRound a && uniqueMax a) sized_vec) $ \() a ->
  let A.I1 n = A.shape a
      b = A.fold max (-20)
                 (A.backpermute (A.I2 n n) (\(A.I2 i j) -> A.I1 (i A..&. j)) a)
  in A.sum (A.map (\x -> x * b A.! A.I1 (A.abs (A.round x) `mod` n)) a)

prop_aindex_map_4 :: Property
prop_aindex_map_4 = compareAD' nil sized_vec $ \() a ->
  let A.I1 n = A.shape a
      b = A.sum (A.backpermute (A.I2 n n)
                               (\(A.I2 i j) -> A.I1 (min (i `A.xor` j) (n-1)))
                               a)
  in A.sum (A.map (\x -> x * a A.! A.I1 (A.abs (A.round x) `mod` n)) b)

-- This property tests whether acond branches are only executed if the condition has the correct value.
prop_aindex_acond_1 :: Property
prop_aindex_acond_1 = compareAD' nil sized_vec $ \() a ->
  let A.I1 n = A.shape a
      s = A.round (A.the (A.sum a))
  in A.sum (A.acond (0 A.<= s A.&& s A.< n)
                    (A.generate (A.I1 1) (\(A.I1 _) -> a A.! A.I1 s))
                    (A.generate (A.I1 1) (\(A.I1 _) -> 0)))

prop_aindex_only :: Property
prop_aindex_only = compareAD' nil sized_vec $ \() a ->
  let A.I1 n = A.shape a
  in A.sum (A.generate (A.I1 5) (\(A.I1 i) -> a A.! A.I1 (i `mod` n)))

prop_a_ignore_argument :: Property
prop_a_ignore_argument = compareAD' nil sized_vec $ \() _ -> A.generate A.I0 (\_ -> 42.0)

prop_nonfloat_lambda :: Property
prop_nonfloat_lambda = compareAD' nil sized_vec $ \() a ->
  let b = A.map (\x -> A.T2 (A.round x :: A.Exp Int) (A.sin x)) a
  in A.sum (A.map (\(A.T2 i x) -> A.toFloating i * x) b)

prop_nonfloat_lambda_friendly :: Property
prop_nonfloat_lambda_friendly = compareAD' nil (Gen.filter allNiceRound sized_vec) $ \() a ->
  let b = A.map (\x -> A.T2 (A.round x :: A.Exp Int) (A.sin x)) a
  in A.sum (A.map (\(A.T2 i x) -> A.toFloating i * x) b)


-- Expression tests
-- ----------------

prop_cond_1 :: Property
prop_cond_1 = compareADE sized_vec $ \x ->
  let y = A.cond (x A.> 0) (A.sin (x * x)) (x * x * A.exp x)  -- derivative continuous at 0
  in 2 * y

prop_cond_2 :: Property
prop_cond_2 = compareADE sized_vec $ \x ->
  let fmod a b = a - A.toFloating (A.floor (a / b) :: A.Exp Int) * b
      y = A.cond (x `fmod` (2 * A.pi) A.< A.pi)  -- derivative continuous at all switching points
                 (A.sin x)
                 (A.pi / 12 * ((2 - 2 / A.pi * (x - A.pi / 2) `fmod` (2 * pi)) ^^ (6 :: Int) - 1))
  in y * y

-- This property, as well as prop_cond_3b, test that Cond isn't over-eager in finding the contents
-- of its branches.
prop_cond_3a :: Property
prop_cond_3a = compareADE sized_vec $ \x ->
  let a = 2 * x
      y = A.cond (x A.<= 2) (a + 1) (2 * a - 1)
  in a * y

prop_cond_3b :: Property
prop_cond_3b = compareADE sized_vec $ \x ->
  let a = 2 * x
      y = A.cond (x A.<= 2) (a + 1) (2 * a - 1)
  in y * a

prop_ignore_argument :: Property
prop_ignore_argument = compareADE sized_vec $ \_ -> 42.0


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
    ["-h"] -> die "When given no parameters, runs full test suite. With parameters, or alternatively the ACCELERATE_ADTEST_PROPS environment variable (in which patterns are separated with ','), only matching properties will be run. Patterns support * wildcards."

    [] -> lookupEnv "ACCELERATE_ADTEST_PROPS" >>= \case
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
