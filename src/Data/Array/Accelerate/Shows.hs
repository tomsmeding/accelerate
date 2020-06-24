{-# LANGUAGE GADTs #-}
module Data.Array.Accelerate.Shows where

import Data.Array.Accelerate.Array.Representation
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Type


showTupR :: TupR ScalarType arrs -> String
showTupR TupRunit = "()"
showTupR (TupRsingle rep) = show rep
showTupR (TupRpair a b) = "(" ++ showTupR a ++ ", " ++ showTupR b ++ ")"

showTupRA :: TupR ArrayR arrs -> String
showTupRA TupRunit = "()"
showTupRA (TupRsingle rep) = showArrayR rep ""
showTupRA (TupRpair a b) = "(" ++ showTupRA a ++ ", " ++ showTupRA b ++ ")"

showLHS :: LeftHandSide ScalarType arrs aenv aenv' -> String
showLHS (LeftHandSideSingle s) = show s
showLHS (LeftHandSideWildcard r) = showTupR r
showLHS (LeftHandSidePair as bs) = "(" ++ showLHS as ++ ", " ++ showLHS bs ++ ")"

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
