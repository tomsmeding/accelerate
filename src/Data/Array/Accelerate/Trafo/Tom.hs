{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Array.Accelerate.Trafo.Tom (
  convertExp, convertAccWith
) where

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Trafo.Config
import Data.Array.Accelerate.Array.Representation (showArrayR)

import Debug.Trace


showTupRA :: TupR ArrayR arrs -> String
showTupRA TupRunit = "()"
showTupRA (TupRsingle rep) = showArrayR rep ""
showTupRA (TupRpair a b) = "(" ++ showTupRA a ++ ", " ++ showTupRA b ++ ")"

showLHSA :: LeftHandSide ArrayR arrs aenv aenv' -> String
showLHSA (LeftHandSideSingle s) = showArrayR s ""
showLHSA (LeftHandSideWildcard r) = showTupRA r
showLHSA (LeftHandSidePair as bs) = "(" ++ showLHSA as ++ ", " ++ showLHSA bs ++ ")"

showPrimFun :: PrimFun a -> String
showPrimFun (PrimAdd _)            = "PrimAdd"
showPrimFun (PrimSub _)            = "PrimSub"
showPrimFun (PrimMul _)            = "PrimMul"
showPrimFun (PrimNeg _)            = "PrimNeg"
showPrimFun (PrimAbs _)            = "PrimAbs"
showPrimFun (PrimSig _)            = "PrimSig"
showPrimFun (PrimQuot _)           = "PrimQuot"
showPrimFun (PrimRem _)            = "PrimRem"
showPrimFun (PrimQuotRem _)        = "PrimQuotRem"
showPrimFun (PrimIDiv _)           = "PrimIDiv"
showPrimFun (PrimMod _)            = "PrimMod"
showPrimFun (PrimDivMod _)         = "PrimDivMod"
showPrimFun (PrimBAnd _)           = "PrimBAnd"
showPrimFun (PrimBOr _)            = "PrimBOr"
showPrimFun (PrimBXor _)           = "PrimBXor"
showPrimFun (PrimBNot _)           = "PrimBNot"
showPrimFun (PrimBShiftL _)        = "PrimBShiftL"
showPrimFun (PrimBShiftR _)        = "PrimBShiftR"
showPrimFun (PrimBRotateL _)       = "PrimBRotateL"
showPrimFun (PrimBRotateR _)       = "PrimBRotateR"
showPrimFun (PrimFDiv _)           = "PrimFDiv"
showPrimFun (PrimRecip _)          = "PrimRecip"
showPrimFun (PrimSin _)            = "PrimSin"
showPrimFun (PrimCos _)            = "PrimCos"
showPrimFun (PrimTan _)            = "PrimTan"
showPrimFun (PrimAsin _)           = "PrimAsin"
showPrimFun (PrimAcos _)           = "PrimAcos"
showPrimFun (PrimAtan _)           = "PrimAtan"
showPrimFun (PrimSinh _)           = "PrimSinh"
showPrimFun (PrimCosh _)           = "PrimCosh"
showPrimFun (PrimTanh _)           = "PrimTanh"
showPrimFun (PrimAsinh _)          = "PrimAsinh"
showPrimFun (PrimAcosh _)          = "PrimAcosh"
showPrimFun (PrimAtanh _)          = "PrimAtanh"
showPrimFun (PrimExpFloating _)    = "PrimExpFloating"
showPrimFun (PrimSqrt _)           = "PrimSqrt"
showPrimFun (PrimLog _)            = "PrimLog"
showPrimFun (PrimFPow _)           = "PrimFPow"
showPrimFun (PrimLogBase _)        = "PrimLogBase"
showPrimFun (PrimTruncate _ _)     = "PrimTruncate"
showPrimFun (PrimRound _ _)        = "PrimRound"
showPrimFun (PrimFloor _ _)        = "PrimFloor"
showPrimFun (PrimCeiling _ _)      = "PrimCeiling"
showPrimFun (PrimAtan2 _)          = "PrimAtan2"
showPrimFun (PrimIsNaN _)          = "PrimIsNaN"
showPrimFun (PrimLt _)             = "PrimLt"
showPrimFun (PrimGt _)             = "PrimGt"
showPrimFun (PrimLtEq _)           = "PrimLtEq"
showPrimFun (PrimGtEq _)           = "PrimGtEq"
showPrimFun (PrimEq _)             = "PrimEq"
showPrimFun (PrimNEq _)            = "PrimNEq"
showPrimFun (PrimMax _)            = "PrimMax"
showPrimFun (PrimMin _)            = "PrimMin"
showPrimFun PrimLAnd               = "PrimLAnd"
showPrimFun PrimLOr                = "PrimLOr"
showPrimFun PrimLNot               = "PrimLNot"
showPrimFun PrimOrd                = "PrimOrd"
showPrimFun PrimChr                = "PrimChr"
showPrimFun PrimBoolToInt          = "PrimBoolToInt"
showPrimFun (PrimFromIntegral _ _) = "PrimFromIntegral"
showPrimFun (PrimPopCount _)       = "PrimPopCount"
showPrimFun (PrimCountLeadingZeros _) = "PrimCountLeadingZeros"
showPrimFun (PrimCountTrailingZeros _) = "PrimCountTrailingZeros"
showPrimFun (PrimIsInfinite _)     = "PrimIsInfinite"
showPrimFun (PrimToFloating _ _)   = "PrimToFloating"

-- type ExpVar = Var ScalarType
-- data Var s env t = Var (s t) (Idx env t)
-- data Idx env t where
--   ZeroIdx ::              Idx (env, t) t
--   SuccIdx :: Idx env t -> Idx (env, s) t


convertExp :: PreOpenExp OpenAcc env aenv e -> PreOpenExp OpenAcc env aenv e
convertExp (Const ty con) = Const ty con
convertExp (PrimApp f e) =
  trace ("Exp: applying primitive " ++ showPrimFun f) $
    PrimApp f (convertExp e)
convertExp (Evar (Var rep idx)) =
  trace ("Exp: Referencing variable at index: " ++ show (idxToInt idx)) $
    Evar (Var rep idx)
convertExp Nil = Nil
convertExp (Pair e1 e2) = Pair (convertExp e1) (convertExp e2)
convertExp (Shape arr) = Shape (convertAcc arr)
convertExp e =
  $internalError "Tom.convertExp" ("Cannot convert Exp node <" ++ showPreExpOp e ++ ">")

convertAccWith :: Config -> Acc arrs -> Acc arrs
convertAccWith _ = convertAcc
-- convertAccWith _ acc@(OpenAcc a) = trace ("ENTRY " ++ showPreAccOp a) $ convertAcc acc

convertAcc :: OpenAcc env arrs -> OpenAcc env arrs
convertAcc (OpenAcc (Unit ty e)) = OpenAcc (Unit ty (convertExp e))
convertAcc (OpenAcc (Map ty f a)) =
  trace "MAP" $
    OpenAcc (Map ty (convertFun f) (convertAcc a))
convertAcc (OpenAcc (Alet lhs def body)) =
  trace ("Let-assigning to: " ++ showLHSA lhs) $
    OpenAcc (Alet lhs (convertAcc def) (convertAcc body))
convertAcc (OpenAcc (Avar (Var rep idx))) =
  trace ("Referencing variable at index: " ++ show (idxToInt idx)) $
    OpenAcc (Avar (Var rep idx))
convertAcc (OpenAcc (Apair a1 a2)) = OpenAcc (Apair (convertAcc a1) (convertAcc a2))
convertAcc (OpenAcc Anil) = OpenAcc Anil
convertAcc (OpenAcc (Use rep a)) = OpenAcc (Use rep a)
convertAcc (OpenAcc (Fold f e a)) = OpenAcc (Fold (convertFun f) (convertExp e) (convertAcc a))
convertAcc (OpenAcc (ZipWith ty f a1 a2)) = OpenAcc (ZipWith ty (convertFun f) (convertAcc a1) (convertAcc a2))
convertAcc (OpenAcc (Backpermute rep e f a)) = OpenAcc (Backpermute rep (convertExp e) (convertFun f) (convertAcc a))
convertAcc (OpenAcc acc) =
  $internalError "Tom.convertAcc" ("Cannot convert Acc node <" ++ showPreAccOp acc ++ ">")

convertFun :: PreOpenFun OpenAcc env aenv t -> PreOpenFun OpenAcc env aenv t
convertFun (Lam lhs f) = Lam lhs (convertFun f)
convertFun (Body e) = Body (convertExp e)
