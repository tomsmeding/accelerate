{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS -Wno-orphans #-}
module Data.Array.Accelerate.Trafo.AD.Orphans where

import Data.GADT.Compare
import Data.Type.Equality

import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Type


instance GEq IntegralType where
  geq TypeInt TypeInt = Just Refl
  geq TypeInt8 TypeInt8 = Just Refl
  geq TypeInt16 TypeInt16 = Just Refl
  geq TypeInt32 TypeInt32 = Just Refl
  geq TypeInt64 TypeInt64 = Just Refl
  geq TypeWord TypeWord = Just Refl
  geq TypeWord8 TypeWord8 = Just Refl
  geq TypeWord16 TypeWord16 = Just Refl
  geq TypeWord32 TypeWord32 = Just Refl
  geq TypeWord64 TypeWord64 = Just Refl
  geq _ _ = Nothing

instance GEq FloatingType where
  geq TypeHalf TypeHalf = Just Refl
  geq TypeFloat TypeFloat = Just Refl
  geq TypeDouble TypeDouble = Just Refl
  geq _ _ = Nothing

instance GEq NumType where
  geq (IntegralNumType t1) (IntegralNumType t2) = geq t1 t2
  geq (FloatingNumType t1) (FloatingNumType t2) = geq t1 t2
  geq _ _ = Nothing

instance GEq SingleType where
  geq (NumSingleType t1) (NumSingleType t2) = geq t1 t2

instance GEq VectorType where
  geq _ _ =
    error "Cannot properly compare VectorType's, because the KnownNat is not materialised"

instance GEq ScalarType where
  geq (SingleScalarType t1) (SingleScalarType t2) = geq t1 t2
  geq (VectorScalarType t1) (VectorScalarType t2) = geq t1 t2
  geq _ _ = Nothing

instance GEq (TupR ScalarType) where
  geq TupRunit TupRunit = Just Refl
  geq (TupRsingle t1) (TupRsingle t2) = geq t1 t2
  geq (TupRpair t1 u1) (TupRpair t2 u2)
    | Just Refl <- geq t1 t2
    , Just Refl <- geq u1 u2
    = Just Refl
  geq _ _ = Nothing


instance GCompare IntegralType where
  gcompare TypeInt TypeInt = GEQ
  gcompare TypeInt _ = GLT
  gcompare _ TypeInt = GGT
  gcompare TypeInt8 TypeInt8 = GEQ
  gcompare TypeInt8 _ = GLT
  gcompare _ TypeInt8 = GGT
  gcompare TypeInt16 TypeInt16 = GEQ
  gcompare TypeInt16 _ = GLT
  gcompare _ TypeInt16 = GGT
  gcompare TypeInt32 TypeInt32 = GEQ
  gcompare TypeInt32 _ = GLT
  gcompare _ TypeInt32 = GGT
  gcompare TypeInt64 TypeInt64 = GEQ
  gcompare TypeInt64 _ = GLT
  gcompare _ TypeInt64 = GGT
  gcompare TypeWord TypeWord = GEQ
  gcompare TypeWord _ = GLT
  gcompare _ TypeWord = GLT
  gcompare TypeWord8 TypeWord8 = GEQ
  gcompare TypeWord8 _ = GLT
  gcompare _ TypeWord8 = GGT
  gcompare TypeWord16 TypeWord16 = GEQ
  gcompare TypeWord16 _ = GLT
  gcompare _ TypeWord16 = GGT
  gcompare TypeWord32 TypeWord32 = GEQ
  gcompare TypeWord32 _ = GLT
  gcompare _ TypeWord32 = GGT
  gcompare TypeWord64 TypeWord64 = GEQ

instance GCompare FloatingType where
  gcompare TypeHalf TypeHalf = GEQ
  gcompare TypeHalf _ = GLT
  gcompare _ TypeHalf = GGT
  gcompare TypeFloat TypeFloat = GEQ
  gcompare TypeFloat _ = GLT
  gcompare _ TypeFloat = GGT
  gcompare TypeDouble TypeDouble = GEQ

instance GCompare NumType where
  gcompare (IntegralNumType t1) (IntegralNumType t2) = gcompare t1 t2
  gcompare (IntegralNumType _) (FloatingNumType _) = GLT
  gcompare (FloatingNumType _) (IntegralNumType _) = GGT
  gcompare (FloatingNumType t1) (FloatingNumType t2) = gcompare t1 t2

instance GCompare SingleType where
  gcompare (NumSingleType t1) (NumSingleType t2) = gcompare t1 t2

instance GCompare VectorType where
  gcompare _ _ =
    error "Cannot properly compare VectorType's, because the KnownNat is not materialised"

instance GCompare ScalarType where
  gcompare (SingleScalarType t1) (SingleScalarType t2) = gcompare t1 t2
  gcompare (SingleScalarType _) (VectorScalarType _) = GLT
  gcompare (VectorScalarType _) (SingleScalarType _) = GGT
  gcompare (VectorScalarType t1) (VectorScalarType t2) = gcompare t1 t2

instance GCompare (TupR ScalarType) where
  gcompare TupRunit TupRunit = GEQ
  gcompare TupRunit _ = GLT
  gcompare _ TupRunit = GGT
  gcompare (TupRsingle t1) (TupRsingle t2) = gcompare t1 t2
  gcompare (TupRsingle _) _ = GLT
  gcompare _ (TupRsingle _) = GGT
  gcompare (TupRpair t1 u1) (TupRpair t2 u2) =
    case gcompare t1 t2 of
      GLT -> GLT
      GGT -> GGT
      GEQ -> case gcompare u1 u2 of
               GLT -> GLT
               GGT -> GGT
               GEQ -> GEQ
