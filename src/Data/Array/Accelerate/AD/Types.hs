{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Array.Accelerate.AD.Types where

import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import qualified Data.Array.Accelerate.Sugar.Array as Sugar
import Data.Array.Accelerate.Sugar.Vec ()
import Data.Array.Accelerate.Type
import Data.Primitive.Vec

import Data.Kind (Type)


type family Ctg a where
  Ctg Int = ()
  Ctg Int8 = ()
  Ctg Int16 = ()
  Ctg Int32 = ()
  Ctg Int64 = ()
  Ctg Word = ()
  Ctg Word8 = ()
  Ctg Word16 = ()
  Ctg Word32 = ()
  Ctg Word64 = ()
  Ctg Half = Half
  Ctg Float = Float
  Ctg Double = Double
  Ctg (Vec n Int) = ()
  Ctg (Vec n Int8) = ()
  Ctg (Vec n Int16) = ()
  Ctg (Vec n Int32) = ()
  Ctg (Vec n Int64) = ()
  Ctg (Vec n Word) = ()
  Ctg (Vec n Word8) = ()
  Ctg (Vec n Word16) = ()
  Ctg (Vec n Word32) = ()
  Ctg (Vec n Word64) = ()
  Ctg (Vec n Half) = Vec n Half
  Ctg (Vec n Float) = Vec n Float
  Ctg (Vec n Double) = Vec n Double
  Ctg (Sugar.Array n a) = Sugar.Array n (Ctg a)
  Ctg (Array n a) = Array n (Ctg a)
  Ctg () = ()
  Ctg (a, b) = (Ctg a, Ctg b)

class HasCtg f where
  type HasCtgOutput f :: Type -> Type
  ctgR :: f a -> HasCtgOutput f (Ctg a)

instance HasCtg ScalarType where
  type HasCtgOutput ScalarType = TypeR
  ctgR (SingleScalarType (NumSingleType (IntegralNumType t))) = case t of
    TypeInt -> TupRunit
    TypeInt8 -> TupRunit ; TypeInt16 -> TupRunit
    TypeInt32 -> TupRunit ; TypeInt64 -> TupRunit
    TypeWord -> TupRunit
    TypeWord8 -> TupRunit ; TypeWord16 -> TupRunit
    TypeWord32 -> TupRunit ; TypeWord64 -> TupRunit
  ctgR ty@(SingleScalarType (NumSingleType (FloatingNumType t))) = case t of
    TypeHalf -> TupRsingle ty
    TypeFloat -> TupRsingle ty
    TypeDouble -> TupRsingle ty
  ctgR (VectorScalarType (VectorType _ (NumSingleType (IntegralNumType t)))) = case t of
    TypeInt -> TupRunit
    TypeInt8 -> TupRunit ; TypeInt16 -> TupRunit
    TypeInt32 -> TupRunit ; TypeInt64 -> TupRunit
    TypeWord -> TupRunit
    TypeWord8 -> TupRunit ; TypeWord16 -> TupRunit
    TypeWord32 -> TupRunit ; TypeWord64 -> TupRunit
  ctgR ty@(VectorScalarType (VectorType _ (NumSingleType (FloatingNumType t)))) = case t of
    TypeHalf -> TupRsingle ty
    TypeFloat -> TupRsingle ty
    TypeDouble -> TupRsingle ty

instance HasCtg TypeR where
  type HasCtgOutput TypeR = TypeR
  ctgR TupRunit = TupRunit
  ctgR (TupRsingle t) = ctgR t
  ctgR (TupRpair a b) = TupRpair (ctgR a) (ctgR b)

instance HasCtg ArrayR where
  type HasCtgOutput ArrayR = ArrayR
  ctgR (ArrayR sh t) = ArrayR sh (ctgR t)

instance HasCtg ArraysR where
  type HasCtgOutput ArraysR = ArraysR
  ctgR TupRunit = TupRunit
  ctgR (TupRsingle t) = TupRsingle (ctgR t)
  ctgR (TupRpair a b) = TupRpair (ctgR a) (ctgR b)

-- ctgIsElt :: TypeR a -> (Elt (Ctg a) => r) -> r
-- ctgIsElt TupRunit k = k
-- ctgIsElt (TupRpair t1 t2) k = ctgIsElt t1 $ ctgIsElt t2 k
-- ctgIsElt (TupRsingle t) k = case t of
--   SingleScalarType (NumSingleType (IntegralNumType TypeInt)) -> k
--   SingleScalarType (NumSingleType (IntegralNumType TypeInt8)) -> k
--   SingleScalarType (NumSingleType (IntegralNumType TypeInt16)) -> k
--   SingleScalarType (NumSingleType (IntegralNumType TypeInt32)) -> k
--   SingleScalarType (NumSingleType (IntegralNumType TypeInt64)) -> k
--   SingleScalarType (NumSingleType (IntegralNumType TypeWord)) -> k
--   SingleScalarType (NumSingleType (IntegralNumType TypeWord8)) -> k
--   SingleScalarType (NumSingleType (IntegralNumType TypeWord16)) -> k
--   SingleScalarType (NumSingleType (IntegralNumType TypeWord32)) -> k
--   SingleScalarType (NumSingleType (IntegralNumType TypeWord64)) -> k
--   SingleScalarType (NumSingleType (FloatingNumType TypeHalf)) -> k
--   SingleScalarType (NumSingleType (FloatingNumType TypeFloat)) -> k
--   SingleScalarType (NumSingleType (FloatingNumType TypeDouble)) -> k
--   VectorScalarType (VectorType _ (NumSingleType (IntegralNumType TypeInt))) -> k
--   VectorScalarType (VectorType _ (NumSingleType (IntegralNumType TypeInt8))) -> k
--   VectorScalarType (VectorType _ (NumSingleType (IntegralNumType TypeInt16))) -> k
--   VectorScalarType (VectorType _ (NumSingleType (IntegralNumType TypeInt32))) -> k
--   VectorScalarType (VectorType _ (NumSingleType (IntegralNumType TypeInt64))) -> k
--   VectorScalarType (VectorType _ (NumSingleType (IntegralNumType TypeWord))) -> k
--   VectorScalarType (VectorType _ (NumSingleType (IntegralNumType TypeWord8))) -> k
--   VectorScalarType (VectorType _ (NumSingleType (IntegralNumType TypeWord16))) -> k
--   VectorScalarType (VectorType _ (NumSingleType (IntegralNumType TypeWord32))) -> k
--   VectorScalarType (VectorType _ (NumSingleType (IntegralNumType TypeWord64))) -> k
--   VectorScalarType (VectorType _ (NumSingleType (FloatingNumType TypeHalf))) -> k
--   VectorScalarType (VectorType _ (NumSingleType (FloatingNumType TypeFloat))) -> k
--   VectorScalarType (VectorType _ (NumSingleType (FloatingNumType TypeDouble))) -> k

-- ctgIsArrays :: ArraysR a -> (Arrays (Ctg a) => r) -> r
-- ctgIsArrays TupRunit k = k
-- ctgIsArrays (TupRpair t1 t2) k = ctgIsArrays t1 $ ctgIsArrays t2 k
-- ctgIsArrays (TupRsingle (ArrayR sh t)) k = shapeIsShape sh $ ctgIsElt t k
--   where
--     shapeIsShape :: ShapeR sh -> (Shape sh => r) -> r
--     shapeIsShape ShapeRz k = k
