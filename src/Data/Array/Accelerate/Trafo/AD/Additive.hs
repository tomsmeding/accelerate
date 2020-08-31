{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Data.Array.Accelerate.Trafo.AD.Additive where

import qualified Data.Array.Accelerate.AST as A
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.TupleZip


class IsAdditive s where
    zeroForType' :: (forall a. Num a => a) -> s t -> OpenExp env lab args t
    expPlus :: s t -> OpenExp env lab args t -> OpenExp env lab args t -> OpenExp env lab args t

    zeroForType :: s t -> OpenExp env lab args t
    zeroForType = zeroForType' 0

    expSum :: s t -> [OpenExp env lab args t] -> OpenExp env lab args t
    expSum ty [] = zeroForType ty
    expSum ty es = foldl1 (expPlus ty) es

instance IsAdditive IntegralType where
    zeroForType' z ty = case ty of
        TypeInt -> Const (scalar TypeInt) z
        TypeInt8 -> Const (scalar TypeInt8) z
        TypeInt16 -> Const (scalar TypeInt16) z
        TypeInt32 -> Const (scalar TypeInt32) z
        TypeInt64 -> Const (scalar TypeInt64) z
        TypeWord -> Const (scalar TypeWord) z
        TypeWord8 -> Const (scalar TypeWord8) z
        TypeWord16 -> Const (scalar TypeWord16) z
        TypeWord32 -> Const (scalar TypeWord32) z
        TypeWord64 -> Const (scalar TypeWord64) z
      where scalar = SingleScalarType . NumSingleType . IntegralNumType

    expPlus ty e1 e2 =
      PrimApp (TupRsingle (scalar ty)) (A.PrimAdd (IntegralNumType ty))
              (Pair (TupRpair (TupRsingle (scalar ty)) (TupRsingle (scalar ty))) e1 e2)
      where scalar = SingleScalarType . NumSingleType . IntegralNumType

instance IsAdditive FloatingType where
    zeroForType' z ty = case ty of
        TypeHalf -> Const (flttype TypeHalf) z
        TypeFloat -> Const (flttype TypeFloat) z
        TypeDouble -> Const (flttype TypeDouble) z
      where flttype = SingleScalarType . NumSingleType . FloatingNumType

    expPlus ty e1 e2 =
      PrimApp (TupRsingle (scalar ty)) (A.PrimAdd (FloatingNumType ty))
              (Pair (TupRpair (TupRsingle (scalar ty)) (TupRsingle (scalar ty))) e1 e2)
      where scalar = SingleScalarType . NumSingleType . FloatingNumType

instance IsAdditive NumType where
    zeroForType' z (IntegralNumType t) = zeroForType' z t
    zeroForType' z (FloatingNumType t) = zeroForType' z t

    expPlus ty e1 e2 =
      PrimApp (TupRsingle (scalar ty)) (A.PrimAdd ty)
              (Pair (TupRpair (TupRsingle (scalar ty)) (TupRsingle (scalar ty))) e1 e2)
      where scalar = SingleScalarType . NumSingleType

instance IsAdditive SingleType where
    zeroForType' z (NumSingleType t) = zeroForType' z t

    expPlus (NumSingleType ty) e1 e2 = expPlus ty e1 e2

instance IsAdditive ScalarType where
    zeroForType' z (SingleScalarType t) = zeroForType' z t
    zeroForType' _ (VectorScalarType _) = internalError "AD: Can't handle vectors yet"

    expPlus (SingleScalarType ty) e1 e2 = expPlus ty e1 e2
    expPlus (VectorScalarType _) _ _ = internalError "AD: Can't handle vectors yet"

instance IsAdditive TypeR where
    zeroForType' _ TupRunit = Nil
    zeroForType' z (TupRsingle t) = zeroForType' z t
    zeroForType' z (TupRpair t1 t2) =
        Pair (TupRpair t1 t2) (zeroForType' z t1) (zeroForType' z t2)

    expPlus ty e1 e2 = tupleZip' ty expPlus e1 e2
