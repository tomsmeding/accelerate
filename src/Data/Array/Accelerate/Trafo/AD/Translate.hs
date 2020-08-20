{-# LANGUAGE GADTs #-}
module Data.Array.Accelerate.Trafo.AD.Translate where

import Data.Maybe (fromJust)

import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Environment as A
import qualified Data.Array.Accelerate.AST.LeftHandSide as A
import qualified Data.Array.Accelerate.AST.Idx as A
import qualified Data.Array.Accelerate.AST.Var as A
import qualified Data.Array.Accelerate.Trafo.Substitution as A
import Data.Array.Accelerate.Error
import qualified Data.Array.Accelerate.Trafo.AD.Exp as D
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Analysis.Match (matchTypeR, (:~:)(Refl))
import qualified Data.Array.Accelerate.Trafo.AD.Sink as D


translateExp :: A.OpenExp env aenv t -> D.OpenExp env lab args t
translateExp expr = case expr of
    A.Const ty con -> D.Const ty con
    A.PrimApp f e -> D.PrimApp (A.expType expr) f (translateExp e)
    A.Evar (A.Var rep idx) -> D.Var (A.Var rep idx)
    A.Let lhs def body -> D.Let lhs (translateExp def) (translateExp body)
    A.Nil -> D.Nil
    A.Pair e1 e2 -> D.Pair (A.expType expr) (translateExp e1) (translateExp e2)
    _ -> internalError "AD.translateExp" ("Cannot perform AD on Exp node <" ++ A.showExpOp expr ++ ">")

untranslateExp :: D.OpenExp env lab args t -> A.OpenExp env aenv t
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
    D.Arg _ _ -> internalError "AD.untranslateExp" "Unexpected Arg in untranslate!"
    D.Label _ -> internalError "AD.untranslateExp" "Unexpected Label in untranslate!"

data PartialVal topenv env where
    PTEmpty :: PartialVal topenv topenv
    PTPush :: PartialVal topenv env -> TypeR t -> PartialVal topenv (env, t)

pvalPushLHS :: A.ELeftHandSide t env env' -> PartialVal topenv env -> PartialVal topenv env'
pvalPushLHS (A.LeftHandSideWildcard _) tv = tv
pvalPushLHS (A.LeftHandSideSingle sty) tv = PTPush tv (TupRsingle sty)
pvalPushLHS (A.LeftHandSidePair lhs1 lhs2) tv = pvalPushLHS lhs2 (pvalPushLHS lhs1 tv)

data UntranslateResult a env aenv t =
    forall env'. UntranslateResult (A.ELeftHandSide a env env') (A.OpenExp env' aenv t)

untranslateLHSboundExp :: A.ELeftHandSide a () env
                       -> D.OpenExp env lab args t
                       -> UntranslateResult a env1 aenv t
untranslateLHSboundExp toplhs topexpr
  | D.GenLHS toplhs' <- D.generaliseLHS toplhs =
      UntranslateResult toplhs' (go topexpr (pvalPushLHS toplhs' PTEmpty))
  where
    go :: D.OpenExp env lab args t -> PartialVal topenv env2 -> A.OpenExp env2 aenv t
    go expr pv = case expr of
        D.Const ty con -> A.Const ty con
        D.PrimApp _ f e -> A.PrimApp f (go e pv)
        D.Var var -> A.Evar (fromJust (checkLocal var pv))
          where
            checkLocal :: A.ExpVar env t -> PartialVal topenv env2 -> Maybe (A.ExpVar env2 t)
            checkLocal _ PTEmpty = Nothing
            checkLocal (A.Var sty A.ZeroIdx) (PTPush _ sty')
              | Just Refl <- matchTypeR (TupRsingle sty) sty' =
                  Just (A.Var sty A.ZeroIdx)
              | otherwise = Nothing
            checkLocal (A.Var sty (A.SuccIdx idx)) (PTPush tagval _)
              | Just (A.Var sty' idx') <- checkLocal (A.Var sty idx) tagval =
                  Just (A.Var sty' (A.SuccIdx idx'))
              | otherwise = Nothing
        D.Let lhs def body
          | D.GenLHS lhs' <- D.generaliseLHS lhs
          -> A.Let lhs' (go def pv) (go body (pvalPushLHS lhs' pv))
        D.Nil -> A.Nil
        D.Pair _ e1 e2 -> A.Pair (go e1 pv) (go e2 pv)
        D.Get _ path e
          | LetBoundExp lhs body <- untranslateGet (D.typeOf e) path
          -> A.Let lhs (go e pv) body
        D.Arg _ _ -> internalError "AD.untranslateExp" "Unexpected Arg in untranslate!"
        D.Label _ -> internalError "AD.untranslateExp" "Unexpected Label in untranslate!"

data LetBoundExp env aenv t s =
    forall env'. LetBoundExp (A.ELeftHandSide t env env') (A.OpenExp env' aenv s)

untranslateGet :: TypeR t -> D.TupleIdx s t -> LetBoundExp env aenv t s
untranslateGet ty D.TIHere = lhsCopy ty
untranslateGet (TupRpair t1 t2) (D.TILeft path)
  | LetBoundExp lhs1 ex1 <- untranslateGet t1 path
  = LetBoundExp (A.LeftHandSidePair lhs1 (A.LeftHandSideWildcard t2)) ex1
untranslateGet (TupRpair t1 t2) (D.TIRight path)
  | LetBoundExp lhs2 ex2 <- untranslateGet t2 path
  = LetBoundExp (A.LeftHandSidePair (A.LeftHandSideWildcard t1) lhs2) ex2
untranslateGet _ _ = error "untranslateGet: impossible GADTs"

lhsCopy :: TypeR t -> LetBoundExp env aenv t t
lhsCopy TupRunit = LetBoundExp (A.LeftHandSideWildcard TupRunit) A.Nil
lhsCopy (TupRsingle sty) = LetBoundExp (A.LeftHandSideSingle sty) (A.Evar (A.Var sty A.ZeroIdx))
lhsCopy (TupRpair t1 t2)
  | LetBoundExp lhs1 ex1 <- lhsCopy t1
  , LetBoundExp lhs2 ex2 <- lhsCopy t2
  = let ex1' = A.weakenE (A.weakenWithLHS lhs2) ex1
    in LetBoundExp (A.LeftHandSidePair lhs1 lhs2) (A.Pair ex1' ex2)
