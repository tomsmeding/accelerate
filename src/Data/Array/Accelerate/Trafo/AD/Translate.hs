{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.Translate where

import Data.Maybe (fromJust)

import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Environment as A
import qualified Data.Array.Accelerate.AST.LeftHandSide as A
import qualified Data.Array.Accelerate.AST.Idx as A
import qualified Data.Array.Accelerate.AST.Var as A
import qualified Data.Array.Accelerate.Trafo.Substitution as A
import Data.Array.Accelerate.Analysis.Match (matchTypeR, matchArraysR, (:~:)(Refl))
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.Trafo.AD.Acc as D
import qualified Data.Array.Accelerate.Trafo.AD.Common as D
import qualified Data.Array.Accelerate.Trafo.AD.Exp as D
import qualified Data.Array.Accelerate.Trafo.AD.Sink as D


translateAcc :: A.OpenAcc aenv t -> D.OpenAcc aenv lab args t
translateAcc (A.OpenAcc expr) = case expr of
    A.Use ty arr -> D.Aconst ty arr
    A.Apair e1 e2 ->
        D.Apair (A.arraysR expr) (translateAcc e1) (translateAcc e2)
    A.Anil -> D.Anil
    A.Acond c t e ->
        D.Acond (A.arraysR expr) (translateExp c) (translateAcc t) (translateAcc e)
    A.Map _ f e -> D.Map (A.arrayR expr) (translateFun f) (translateAcc e)
    A.ZipWith _ f e1 e2 ->
        D.ZipWith (A.arrayR expr) (translateFun f) (translateAcc e1) (translateAcc e2)
    A.Fold f me0 e ->
        D.Fold (A.arrayR expr) (translateFun f) (translateExp <$> me0) (translateAcc e)
    A.Alet lhs def body -> D.Alet lhs (translateAcc def) (translateAcc body)
    A.Avar var -> D.Avar var
    _ -> internalError ("AD.translateAcc: Cannot perform AD on Acc node <" ++ A.showPreAccOp expr ++ ">")

translateFun :: A.OpenFun env aenv t -> D.OpenFun env aenv lab t
translateFun (A.Lam lhs fun) = D.Lam lhs (translateFun fun)
translateFun (A.Body e) = D.Body (translateExp e)

translateExp :: A.OpenExp env aenv t -> D.OpenExp env aenv lab args t
translateExp expr = case expr of
    A.Const ty con -> D.Const ty con
    A.PrimApp f e -> D.PrimApp (A.expType expr) f (translateExp e)
    A.Evar (A.Var rep idx) -> D.Var (A.Var rep idx)
    A.Let lhs def body -> D.Let lhs (translateExp def) (translateExp body)
    A.Nil -> D.Nil
    A.Cond c t e -> D.Cond (A.expType t) (translateExp c) (translateExp t) (translateExp e)
    A.Pair e1 e2 -> D.Pair (A.expType expr) (translateExp e1) (translateExp e2)
    _ -> internalError ("AD.translateExp: Cannot perform AD on Exp node <" ++ A.showExpOp expr ++ ">")

data PartialVal s topenv env where
    PTEmpty :: PartialVal s topenv topenv
    PTPush :: PartialVal s topenv env -> TupR s t -> PartialVal s topenv (env, t)

pvalPushLHS :: A.LeftHandSide s t env env' -> PartialVal s topenv env -> PartialVal s topenv env'
pvalPushLHS (A.LeftHandSideWildcard _) tv = tv
pvalPushLHS (A.LeftHandSideSingle sty) tv = PTPush tv (TupRsingle sty)
pvalPushLHS (A.LeftHandSidePair lhs1 lhs2) tv = pvalPushLHS lhs2 (pvalPushLHS lhs1 tv)

data UntranslateResultE a env aenv t =
    forall env'. UntranslateResultE (A.ELeftHandSide a env env') (A.OpenExp env' aenv t)

untranslateLHSboundExp :: A.ELeftHandSide a () env
                       -> D.OpenExp env aenv lab args t
                       -> UntranslateResultE a env1 aenv t
untranslateLHSboundExp toplhs topexpr
  | D.GenLHS toplhs' <- D.generaliseLHS toplhs =
      UntranslateResultE toplhs' (go topexpr (pvalPushLHS toplhs' PTEmpty))
  where
    go :: D.OpenExp env aenv lab args t -> PartialVal ScalarType topenv env2 -> A.OpenExp env2 aenv t
    go expr pv = case expr of
        D.Const ty con -> A.Const ty con
        D.PrimApp _ f e -> A.PrimApp f (go e pv)
        D.Var var -> A.Evar (fromJust (checkLocal matchTypeR var pv))
        D.Let lhs def body
          | D.GenLHS lhs' <- D.generaliseLHS lhs
          -> A.Let lhs' (go def pv) (go body (pvalPushLHS lhs' pv))
        D.Nil -> A.Nil
        D.Pair _ e1 e2 -> A.Pair (go e1 pv) (go e2 pv)
        D.Cond _ e1 e2 e3 -> A.Cond (go e1 pv) (go e2 pv) (go e3 pv)
        D.Shape avar -> A.Shape avar
        D.Get _ path e
          | LetBoundExpE lhs body <- euntranslateGet (D.etypeOf e) path
          -> A.Let lhs (go e pv) body
        D.Arg _ _ -> internalError "AD.untranslateLHSboundExp: Unexpected Arg in untranslate!"
        D.Label _ -> internalError "AD.untranslateLHSboundExp: Unexpected Label in untranslate!"

untranslateLHSboundExpA :: forall a env env1 lab args t aenv topaenv aenv2.
                           A.ELeftHandSide a () env
                        -> D.OpenExp env aenv lab args t
                        -> PartialVal ArrayR topaenv aenv2
                        -> UntranslateResultE a env1 aenv2 t
untranslateLHSboundExpA toplhs topexpr arrpv
  | D.GenLHS toplhs' <- D.generaliseLHS toplhs =
      UntranslateResultE toplhs' (go topexpr (pvalPushLHS toplhs' PTEmpty))
  where
    go :: D.OpenExp env' aenv lab args t' -> PartialVal ScalarType topenv env2 -> A.OpenExp env2 aenv2 t'
    go expr pv = case expr of
        D.Const ty con -> A.Const ty con
        D.PrimApp _ f e -> A.PrimApp f (go e pv)
        D.Var var -> A.Evar (fromJust (checkLocal matchTypeR var pv))
        D.Let lhs def body
          | D.GenLHS lhs' <- D.generaliseLHS lhs
          -> A.Let lhs' (go def pv) (go body (pvalPushLHS lhs' pv))
        D.Nil -> A.Nil
        D.Pair _ e1 e2 -> A.Pair (go e1 pv) (go e2 pv)
        D.Cond _ e1 e2 e3 -> A.Cond (go e1 pv) (go e2 pv) (go e3 pv)
        D.Shape avar -> A.Shape (fromJust (checkLocal matchArraysR avar arrpv))
        D.Get _ path e
          | LetBoundExpE lhs body <- euntranslateGet (D.etypeOf e) path
          -> A.Let lhs (go e pv) body
        D.Arg _ _ -> internalError "AD.untranslateLHSboundExp: Unexpected Arg in untranslate!"
        D.Label _ -> internalError "AD.untranslateLHSboundExp: Unexpected Label in untranslate!"

untranslateClosedExp :: forall lab args t aenv. D.OpenExp () aenv lab args t -> A.OpenExp () aenv t
untranslateClosedExp expr
  | UntranslateResultE A.LeftHandSideUnit res <-
        untranslateLHSboundExp A.LeftHandSideUnit expr
            :: UntranslateResultE () () aenv t
  = res
untranslateClosedExp _ = error "unreachable"

untranslateClosedExpA :: forall lab args t topaenv aenv aenv2.
                         D.OpenExp () aenv lab args t
                      -> PartialVal ArrayR topaenv aenv2
                      -> A.OpenExp () aenv2 t
untranslateClosedExpA expr arrpv
  | UntranslateResultE A.LeftHandSideUnit res <-
        untranslateLHSboundExpA A.LeftHandSideUnit expr arrpv
            :: UntranslateResultE () () aenv2 t
  = res
untranslateClosedExpA _ _ = error "unreachable"

data UntranslateFunResultE a env aenv t =
    forall env'. UntranslateFunResultE (A.ELeftHandSide a env env') (A.OpenFun env' aenv t)

untranslateClosedFun :: forall lab t aenv. D.OpenFun () aenv lab t -> A.OpenFun () aenv t
untranslateClosedFun topfun
  | UntranslateFunResultE A.LeftHandSideUnit fun' <- go A.LeftHandSideUnit topfun
  = fun'
  where
    go :: A.ELeftHandSide a () env -> D.OpenFun env aenv lab t' -> UntranslateFunResultE a () aenv t'
    go lhs (D.Lam bindings fun)
      | UntranslateFunResultE (A.LeftHandSidePair lhs' bindings') res
          <- go (A.LeftHandSidePair lhs bindings) fun
      = UntranslateFunResultE lhs' (A.Lam bindings' res)
    go lhs (D.Body body)
      | UntranslateResultE lhs' res <- untranslateLHSboundExp lhs body
      = UntranslateFunResultE lhs' (A.Body res)
    go _ _ = error "unreachable"
untranslateClosedFun _ = error "unreachable"

untranslateClosedFunA :: forall lab t topaenv aenv aenv2.
                         D.OpenFun () aenv lab t
                      -> PartialVal ArrayR topaenv aenv2
                      -> A.OpenFun () aenv2 t
untranslateClosedFunA topfun arrpv
  | UntranslateFunResultE A.LeftHandSideUnit fun' <- go A.LeftHandSideUnit topfun
  = fun'
  where
    go :: A.ELeftHandSide a () env -> D.OpenFun env aenv lab t' -> UntranslateFunResultE a () aenv2 t'
    go lhs (D.Lam bindings fun)
      | UntranslateFunResultE (A.LeftHandSidePair lhs' bindings') res
          <- go (A.LeftHandSidePair lhs bindings) fun
      = UntranslateFunResultE lhs' (A.Lam bindings' res)
    go lhs (D.Body body)
      | UntranslateResultE lhs' res <- untranslateLHSboundExpA lhs body arrpv
      = UntranslateFunResultE lhs' (A.Body res)
    go _ _ = error "unreachable"
untranslateClosedFunA _ _ = error "unreachable"

data UntranslateResultA a aenv t =
    forall aenv'. UntranslateResultA (A.ALeftHandSide a aenv aenv') (A.OpenAcc aenv' t)

untranslateLHSboundAcc :: A.ALeftHandSide a () aenv
                       -> D.OpenAcc aenv lab args t
                       -> UntranslateResultA a aenv1 t
untranslateLHSboundAcc toplhs topexpr
  | D.GenLHS toplhs' <- D.generaliseLHS toplhs =
      UntranslateResultA toplhs' (go topexpr (pvalPushLHS toplhs' PTEmpty))
  where
    go :: D.OpenAcc aenv lab args t -> PartialVal ArrayR topenv aenv2 -> A.OpenAcc aenv2 t
    go expr pv = A.OpenAcc $ case expr of
        D.Aconst ty con -> A.Use ty con
        D.Avar var -> A.Avar (fromJust (checkLocal matchArraysR var pv))
        D.Alet lhs def body
          | D.GenLHS lhs' <- D.generaliseLHS lhs
          -> A.Alet lhs' (go def pv) (go body (pvalPushLHS lhs' pv))
        D.Anil -> A.Anil
        D.Apair _ e1 e2 -> A.Apair (go e1 pv) (go e2 pv)
        D.Acond _ e1 e2 e3 -> A.Acond (untranslateClosedExpA e1 pv) (go e2 pv) (go e3 pv)
        D.Map (ArrayR _ ty) f e -> A.Map ty (untranslateClosedFunA f pv) (go e pv)
        D.ZipWith (ArrayR _ ty) f e1 e2 -> A.ZipWith ty (untranslateClosedFunA f pv) (go e1 pv) (go e2 pv)
        D.Fold _ f me0 e -> A.Fold (untranslateClosedFunA f pv) (untranslateClosedExpA <$> me0 <*> Just pv) (go e pv)
        D.Generate ty e f -> A.Generate ty (untranslateClosedExpA e pv) (untranslateClosedFunA f pv)
        D.Aget _ path e
          | LetBoundExpA lhs body <- auntranslateGet (D.atypeOf e) path
          -> A.Alet lhs (go e pv) body
        D.Aarg _ _ -> internalError "AD.untranslateLHSboundAcc: Unexpected Arg in untranslate!"
        D.Alabel _ -> internalError "AD.untranslateLHSboundAcc: Unexpected Label in untranslate!"

checkLocal :: (forall t1 t2. TupR s t1 -> TupR s t2 -> Maybe (t1 :~: t2)) -> A.Var s env t -> PartialVal s topenv env2 -> Maybe (A.Var s env2 t)
checkLocal _ _ PTEmpty = Nothing
checkLocal match (A.Var sty A.ZeroIdx) (PTPush _ sty')
  | Just Refl <- match (TupRsingle sty) sty' =
      Just (A.Var sty A.ZeroIdx)
  | otherwise = Nothing
checkLocal match (A.Var sty (A.SuccIdx idx)) (PTPush tagval _)
  | Just (A.Var sty' idx') <- checkLocal match (A.Var sty idx) tagval =
      Just (A.Var sty' (A.SuccIdx idx'))
  | otherwise = Nothing

data LetBoundExpE env aenv t s =
    forall env'. LetBoundExpE (A.ELeftHandSide t env env') (A.OpenExp env' aenv s)

euntranslateGet :: TypeR t -> D.TupleIdx t s -> LetBoundExpE env aenv t s
euntranslateGet ty D.TIHere = elhsCopy ty
euntranslateGet (TupRpair t1 t2) (D.TILeft path)
  | LetBoundExpE lhs1 ex1 <- euntranslateGet t1 path
  = LetBoundExpE (A.LeftHandSidePair lhs1 (A.LeftHandSideWildcard t2)) ex1
euntranslateGet (TupRpair t1 t2) (D.TIRight path)
  | LetBoundExpE lhs2 ex2 <- euntranslateGet t2 path
  = LetBoundExpE (A.LeftHandSidePair (A.LeftHandSideWildcard t1) lhs2) ex2
euntranslateGet _ _ = error "euntranslateGet: impossible GADTs"

elhsCopy :: TypeR t -> LetBoundExpE env aenv t t
elhsCopy TupRunit = LetBoundExpE (A.LeftHandSideWildcard TupRunit) A.Nil
elhsCopy (TupRsingle sty) = LetBoundExpE (A.LeftHandSideSingle sty) (A.Evar (A.Var sty A.ZeroIdx))
elhsCopy (TupRpair t1 t2)
  | LetBoundExpE lhs1 ex1 <- elhsCopy t1
  , LetBoundExpE lhs2 ex2 <- elhsCopy t2
  = let ex1' = A.weakenE (A.weakenWithLHS lhs2) ex1
    in LetBoundExpE (A.LeftHandSidePair lhs1 lhs2) (A.Pair ex1' ex2)

data LetBoundExpA aenv t s =
    forall aenv'. LetBoundExpA (A.ALeftHandSide t aenv aenv') (A.OpenAcc aenv' s)

auntranslateGet :: ArraysR t -> D.TupleIdx t s -> LetBoundExpA aenv t s
auntranslateGet ty D.TIHere = alhsCopy ty
auntranslateGet (TupRpair t1 t2) (D.TILeft path)
  | LetBoundExpA lhs1 ex1 <- auntranslateGet t1 path
  = LetBoundExpA (A.LeftHandSidePair lhs1 (A.LeftHandSideWildcard t2)) ex1
auntranslateGet (TupRpair t1 t2) (D.TIRight path)
  | LetBoundExpA lhs2 ex2 <- auntranslateGet t2 path
  = LetBoundExpA (A.LeftHandSidePair (A.LeftHandSideWildcard t1) lhs2) ex2
auntranslateGet _ _ = error "auntranslateGet: impossible GADTs"

alhsCopy :: ArraysR t -> LetBoundExpA aenv t t
alhsCopy TupRunit = LetBoundExpA (A.LeftHandSideWildcard TupRunit) (A.OpenAcc A.Anil)
alhsCopy (TupRsingle sty@(ArrayR _ _)) = LetBoundExpA (A.LeftHandSideSingle sty) (A.OpenAcc (A.Avar (A.Var sty A.ZeroIdx)))
alhsCopy (TupRpair t1 t2)
  | LetBoundExpA lhs1 ex1 <- alhsCopy t1
  , LetBoundExpA lhs2 ex2 <- alhsCopy t2
  = let ex1' = A.weaken (A.weakenWithLHS lhs2) ex1
    in LetBoundExpA (A.LeftHandSidePair lhs1 lhs2) (A.OpenAcc (A.Apair ex1' ex2))
