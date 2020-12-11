{-# LANGUAGE GADTs #-}
{-| Heuristics for the AD transformation. Intended to be imported qualified. -}
module Data.Array.Accelerate.Trafo.AD.Heuristic where

import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Exp


functionSize :: OpenFun env aenv lab alab tenv t -> Int
functionSize (Lam _ fun) = functionSize fun
functionSize (Body expr) = exprSize expr

exprSize :: OpenExp env aenv lab alab args tenv t -> Int
exprSize (Const _ _) = 1
exprSize (PrimApp _ _ arg) = 1 + exprSize arg
exprSize (PrimConst _ _) = 1
exprSize (Pair _ e1 e2) = exprSize e1 + exprSize e2
exprSize (Nil _) = 0
exprSize (Cond _ e1 e2 e3) = exprSize e1 + exprSize e2 + exprSize e3
exprSize (Shape _ _) = 1
exprSize (Index _ _ _ e) = 1 + exprSize e
exprSize (ShapeSize _ _ e) = exprSize e
exprSize (Get ty (TILeft tidx) (Pair _ e _)) = exprSize (Get ty tidx e)
exprSize (Get ty (TIRight tidx) (Pair _ _ e)) = exprSize (Get ty tidx e)
exprSize (Get _ TIHere e) = exprSize e
exprSize (Get _ _ e) = 1 + exprSize e
exprSize (Undef _) = 0
exprSize (Let _ e1 e2) = exprSize e1 + exprSize e2
exprSize (Var _ _ _) = 0
exprSize (FreeVar _ _) = 0
exprSize (Arg _ _ _) = 0
