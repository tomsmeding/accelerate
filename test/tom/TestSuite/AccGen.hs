{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module TestSuite.AccGen (genAcc) where

import Data.Functor.Product
import Data.GADT.Compare
import Data.Some
import Data.Type.Equality ((:~:)(Refl))
import Hedgehog (MonadGen, Gen)
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
  TBool :: ExpType Bool
  TInt :: ExpType Int
  TFloat :: ExpType Float
  TNil :: ExpType ()
  TPair :: ExpType a -> ExpType b -> ExpType (a, b)

instance GEq ExpType where
  geq TBool TBool = Just Refl
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

  genConstant :: MonadGen m => m (A.Exp e)

  -- Given an environment of defined variables, build an expression of the
  -- given type.
  genExpr :: MonadGen m => [SomeExp] -> m (A.Exp e)

instance GenExpr () where
  magicType = TNil
  genConstant = return (A.lift ())
  genExpr _ = return (A.lift ())

instance (GenExpr a, GenExpr b) => GenExpr (a, b) where
  magicType = TPair magicType magicType

  genConstant = A.T2 <$> genConstant <*> genConstant

  genExpr env = do
    a <- Gen.choice (genExpr env : map return (filterType env))
    b <- Gen.choice (genExpr env : map return (filterType env))
    return (A.T2 a b)

instance GenExpr Bool where
  magicType = TBool
  genConstant = A.constant <$> Gen.choice [return False, return True]
  genExpr = genWithOpers [(1, Operation HNil (const genConstant))]
                         (map (fmap (binaryOp TInt TInt)) [(2, (A.==)), (2, (A./=)), (1, (A.>))]
                          ++ map (fmap (binaryOp TFloat TFloat)) [(2, (A.==)), (2, (A./=)), (1, (A.>))])

instance GenExpr Int where
  magicType = TInt
  genConstant = A.constant <$> Gen.int (Range.linearFrom 0 (-10) 10)
  genExpr = genWithOpers [(1, Operation HNil (const genConstant))]
                         (map (fmap (binaryOp TInt TInt)) [(2, (+)), (2, (*)), (1, div)]
                          ++ [(1, condOper)])

instance GenExpr Float where
  magicType = TFloat
  genConstant = A.constant <$> Gen.float (Range.linearFracFrom 0 (-10) 10)
  genExpr = genWithOpers [(1, Operation HNil (const genConstant))]
                         (map (fmap (binaryOp TFloat TFloat)) [(2, (+)), (2, (*)), (1, (/))]
                          ++ [(1, condOper)])

condOper :: GenExpr t => Operation t
condOper = Operation (HCons TBool (HCons magicType (HCons magicType HNil)))
                     (\(HCons a (HCons b (HCons c _))) -> return (A.cond a b c))

genWithOpers :: MonadGen m => [(Int, Operation e)] -> [(Int, Operation e)] -> [SomeExp] -> m (A.Exp e)
genWithOpers nonrecopers recopers env = do
  let buildOper (Operation argtys build) =
        hmap (\ty -> case witnessGenExpr ty of
                        Witness -> Gen.choice (genExpr env : map return (filterType env)))
              argtys
        >>= build
  recursiveF (map (fmap buildOper) nonrecopers) (map (fmap buildOper) recopers)

data Witness t where
  Witness :: GenExpr t => Witness t

witnessGenExpr :: ExpType t -> Witness t
witnessGenExpr TNil = Witness
witnessGenExpr TBool = Witness
witnessGenExpr TInt = Witness
witnessGenExpr TFloat = Witness
witnessGenExpr (TPair t1 t2) | Witness <- witnessGenExpr t1, Witness <- witnessGenExpr t2 = Witness

binaryOp :: ExpType a -> ExpType b -> (A.Exp a -> A.Exp b -> A.Exp c) -> Operation c
binaryOp t1 t2 op = Operation (HCons t1 (HCons t2 HNil)) (\(HCons a (HCons b _)) -> return (op a b))

data Operation t =
  forall args. Operation (HList ExpType args) (forall m. MonadGen m => HList A.Exp args -> m (A.Exp t))

data HList f ts where
  HNil :: HList f ()
  HCons :: f t -> HList f ts -> HList f (t, ts)

hmap :: Applicative m => (forall t. f t -> m (g t)) -> HList f ts -> m (HList g ts)
hmap _ HNil = pure HNil
hmap f (HCons x xs) = HCons <$> f x <*> hmap f xs

filterType :: GenExpr e => [SomeExp] -> [A.Exp e]
filterType = go magicType
  where
    go :: GenExpr e => ExpType e -> [SomeExp] -> [A.Exp e]
    go _ [] = []
    go target (Some (Pair ty e) : xs)
      | Just Refl <- geq ty target = e : go target xs
      | otherwise = go target xs

-- Gen.recursive claims to work with frequency, but it doesn't
recursiveF :: MonadGen m => [(Int, m a)] -> [(Int, m a)] -> m a
recursiveF nonrec rec =
  Gen.sized $ \n ->
    if n <= 1 then Gen.frequency nonrec
              else Gen.frequency (nonrec ++ fmap (fmap Gen.small) rec)
