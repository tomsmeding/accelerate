{-# LANGUAGE GADTs #-}
module Data.Array.Accelerate.Trafo.AD.Translate where

import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.Trafo.Substitution as A
import Data.Array.Accelerate.Error
import qualified Data.Array.Accelerate.Trafo.AD.Exp as D
import Data.Array.Accelerate.Type


translateExp :: A.OpenExp env () t -> D.OpenExp env lab t
translateExp expr = case expr of
    A.Const ty con -> D.Const ty con
    A.PrimApp f e -> D.PrimApp (A.expType expr) f (translateExp e)
    A.Evar (A.Var rep idx) -> D.Var (A.Var rep idx)
    A.Let lhs def body -> D.Let lhs (translateExp def) (translateExp body)
    A.Nil -> D.Nil
    A.Pair e1 e2 -> D.Pair (A.expType expr) (translateExp e1) (translateExp e2)
    _ -> internalError "AD.translateExp" ("Cannot perform AD on Exp node <" ++ A.showPreExpOp expr ++ ">")

untranslateExp :: D.OpenExp env lab t -> A.OpenExp env () t
untranslateExp expr = case expr of
    D.Const ty con -> A.Const ty con
    D.PrimApp _ f e -> A.PrimApp f (untranslateExp e)
    D.Var (A.Var rep idx) -> A.Evar (A.Var rep idx)
    D.Let lhs def body -> A.Let lhs (untranslateExp def) (untranslateExp body)
    D.Nil -> A.Nil
    D.Pair _ e1 e2 -> A.Pair (untranslateExp e1) (untranslateExp e2)
    D.Get _ path e
      | LetBoundExp lhs body <- untranslateGet (D.typeOf e) path
      -> A.Let lhs (untranslateExp e) body
    D.Label _ -> internalError "AD.untranslateExp" "Unexpected Label in untranslate!"

data LetBoundExp env t s = forall env'. LetBoundExp (A.ELeftHandSide t env env') (A.OpenExp env' () s)

untranslateGet :: TupleType t -> D.TupleIdx s t -> LetBoundExp env t s
untranslateGet ty D.TIHere = lhsCopy ty
untranslateGet (TupRpair t1 t2) (D.TILeft path)
  | LetBoundExp lhs1 ex1 <- untranslateGet t1 path
  = LetBoundExp (A.LeftHandSidePair lhs1 (A.LeftHandSideWildcard t2)) ex1
untranslateGet (TupRpair t1 t2) (D.TIRight path)
  | LetBoundExp lhs2 ex2 <- untranslateGet t2 path
  = LetBoundExp (A.LeftHandSidePair (A.LeftHandSideWildcard t1) lhs2) ex2
untranslateGet _ _ = error "untranslateGet: impossible GADTs"

lhsCopy :: TupleType t -> LetBoundExp env t t
lhsCopy TupRunit = LetBoundExp (A.LeftHandSideWildcard TupRunit) A.Nil
lhsCopy (TupRsingle sty) = LetBoundExp (A.LeftHandSideSingle sty) (A.Evar (A.Var sty A.ZeroIdx))
lhsCopy (TupRpair t1 t2)
  | LetBoundExp lhs1 ex1 <- lhsCopy t1
  , LetBoundExp lhs2 ex2 <- lhsCopy t2
  = let ex1' = A.weakenE (A.weakenWithLHS lhs2) ex1
    in LetBoundExp (A.LeftHandSidePair lhs1 lhs2) (A.Pair ex1' ex2)
