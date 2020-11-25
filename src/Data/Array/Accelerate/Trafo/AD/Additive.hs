{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Data.Array.Accelerate.Trafo.AD.Additive where

import qualified Data.Array.Accelerate.AST as A
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.TupleZip
import Data.Array.Accelerate.Analysis.Match (matchConst)


class IsAdditive s where
    zeroForType' :: (forall a. Num a => a) -> s t -> OpenExp env aenv () alab args tenv t
    expPlus :: s t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t

    zeroForType :: s t -> OpenExp env aenv () alab args tenv t
    zeroForType = zeroForType' 0

    expSum :: s t -> [OpenExp env aenv () alab args tenv t] -> OpenExp env aenv () alab args tenv t
    expSum ty [] = zeroForType ty
    expSum ty es = foldl1 (expPlus ty) es

instance IsAdditive IntegralType where
    zeroForType' z ty = case ty of
        TypeInt -> Const scalarLabel z
        TypeInt8 -> Const scalarLabel z
        TypeInt16 -> Const scalarLabel z
        TypeInt32 -> Const scalarLabel z
        TypeInt64 -> Const scalarLabel z
        TypeWord -> Const scalarLabel z
        TypeWord8 -> Const scalarLabel z
        TypeWord16 -> Const scalarLabel z
        TypeWord32 -> Const scalarLabel z
        TypeWord64 -> Const scalarLabel z

    expPlus ty e1 e2 =
      PrimApp (nilLabel (TupRsingle (scalar ty))) (A.PrimAdd (IntegralNumType ty))
              (Pair (nilLabel (TupRpair (TupRsingle (scalar ty)) (TupRsingle (scalar ty)))) e1 e2)
      where scalar = SingleScalarType . NumSingleType . IntegralNumType

instance IsAdditive FloatingType where
    zeroForType' z ty = case ty of
        TypeHalf -> Const scalarLabel z
        TypeFloat -> Const scalarLabel z
        TypeDouble -> Const scalarLabel z

    expPlus ty e1 e2 =
      PrimApp (nilLabel (TupRsingle (scalar ty))) (A.PrimAdd (FloatingNumType ty))
              (Pair (nilLabel (TupRpair (TupRsingle (scalar ty)) (TupRsingle (scalar ty)))) e1 e2)
      where scalar = SingleScalarType . NumSingleType . FloatingNumType

instance IsAdditive NumType where
    zeroForType' z (IntegralNumType t) = zeroForType' z t
    zeroForType' z (FloatingNumType t) = zeroForType' z t

    expPlus ty e1 e2 =
      PrimApp (nilLabel (TupRsingle (scalar ty))) (A.PrimAdd ty)
              (Pair (nilLabel (TupRpair (TupRsingle (scalar ty)) (TupRsingle (scalar ty)))) e1 e2)
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
    zeroForType' _ TupRunit = Nil magicLabel
    zeroForType' z (TupRsingle t) = zeroForType' z t
    zeroForType' z (TupRpair t1 t2) =
        Pair (nilLabel (TupRpair t1 t2)) (zeroForType' z t1) (zeroForType' z t2)

    expPlus ty e1 e2 = tupleZipExp' ty expPlus isZero e1 e2
      where isZero sty (Const _ c)
              | Const _ c' <- zeroForType sty = matchConst (TupRsingle sty) c c'
            isZero _ _ = False
