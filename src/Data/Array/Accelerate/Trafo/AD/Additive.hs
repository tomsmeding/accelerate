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
import Data.Array.Accelerate.Analysis.Match (matchConst)


class IsAdditive s where
    zeroForType' :: (forall a. Num a => a) -> s t -> OpenExp env aenv lab alab args tenv t
    expPlus :: s t -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv t

    zeroForType :: s t -> OpenExp env aenv lab alab args tenv t
    zeroForType = zeroForType' 0

    expSum :: s t -> [OpenExp env aenv lab alab args tenv t] -> OpenExp env aenv lab alab args tenv t
    expSum ty [] = zeroForType ty
    expSum ty es = foldl1 (expPlus ty) es

instance IsAdditive IntegralType where
    zeroForType' z ty = case ty of
        TypeInt -> Const scalarType z
        TypeInt8 -> Const scalarType z
        TypeInt16 -> Const scalarType z
        TypeInt32 -> Const scalarType z
        TypeInt64 -> Const scalarType z
        TypeWord -> Const scalarType z
        TypeWord8 -> Const scalarType z
        TypeWord16 -> Const scalarType z
        TypeWord32 -> Const scalarType z
        TypeWord64 -> Const scalarType z

    expPlus ty e1 e2 =
      PrimApp (TupRsingle (scalar ty)) (A.PrimAdd (IntegralNumType ty))
              (Pair (TupRpair (TupRsingle (scalar ty)) (TupRsingle (scalar ty))) e1 e2)
      where scalar = SingleScalarType . NumSingleType . IntegralNumType

instance IsAdditive FloatingType where
    zeroForType' z ty = case ty of
        TypeHalf -> Const scalarType z
        TypeFloat -> Const scalarType z
        TypeDouble -> Const scalarType z

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

    expPlus ty e1 e2 = tupleZipExp' ty expPlus isZero e1 e2
      where isZero sty (Const _ c)
              | Const _ c' <- zeroForType sty = matchConst (TupRsingle sty) c c'
            isZero _ _ = False
