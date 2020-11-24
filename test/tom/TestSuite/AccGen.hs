{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module TestSuite.AccGen (genAcc) where

import Data.Functor.Product
import Data.GADT.Compare
import Data.Some
import Data.Type.Equality ((:~:)(Refl))
import Hedgehog (MonadGen)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Data.Array.Accelerate as A

import TestSuite.Util


genAcc :: forall m sh. (MonadGen m, Shape sh) => m (A.Acc (A.Array sh Float) -> A.Acc (A.Scalar Float))
genAcc = undefined
-- genAcc = Gen.recursive Gen.choice nonrecGen recGen
--   where
--     shtype :: ShapeType sh
--     shtype = magicShapeType

--     nonrecGen :: [m (A.Acc (A.Array sh Float) -> A.Acc (A.Scalar Float))]
--     nonrecGen =
--       [do x <- genConstFloat ; return (\_ -> A.use (A.fromList A.Z [x]))
--       ]
--       ++ (case shtype of SCons SZ -> nonrecFromVec
--                          _        -> [])

--     nonrecFromVec :: [m (A.Acc (A.Vector Float) -> A.Acc (A.Scalar Float))]
--     nonrecFromVec =
--       [return A.sum
--       ,A.fold <$> genFoldOper <*> undefined]

data ExpType a where
  TInt :: ExpType Int
  TFloat :: ExpType Float
  TNil :: ExpType ()
  TPair :: ExpType a -> ExpType b -> ExpType (a, b)

instance GEq ExpType where
  geq TInt TInt = Just Refl
  geq TFloat TFloat = Just Refl
  geq TNil TNil = Just Refl
  geq (TPair a b) (TPair a' b')
    | Just Refl <- geq a a'
    , Just Refl <- geq b b'
    = Just Refl
  geq _ _ = Nothing

type SomeExp = Some (Product ExpType A.Exp)

class A.Elt e => GenExpr e where
  magicType :: ExpType e

  -- Given an environment of defined variables, build an expression of the
  -- given type.
  genExpr :: MonadGen m => [SomeExp] -> m (A.Exp e)

instance GenExpr () where
  magicType = TNil

  genExpr _ = return (A.lift ())

instance (GenExpr a, GenExpr b) => GenExpr (a, b) where
  magicType = TPair magicType magicType

  genExpr env = do
    a <- Gen.choice (genExpr env : map return (filterType env))
    b <- Gen.choice (genExpr env : map return (filterType env))
    return (A.T2 a b)

instance GenExpr Int where


filterType :: GenExpr e => [SomeExp] -> [A.Exp e]
filterType = go magicType
  where
    go :: GenExpr e => ExpType e -> [SomeExp] -> [A.Exp e]
    go _ [] = []
    go target (Some (Pair ty e) : xs)
      | Just Refl <- geq ty target = e : go target xs
      | otherwise = go target xs

genConstFloat :: MonadGen m => m Float
genConstFloat = Gen.float (Range.linearFracFrom 0 (-10) 10)
