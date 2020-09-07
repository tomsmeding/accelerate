{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.Sink (
  sinkExp, sinkExpAenv, sinkFunAenv, sinkAcc,
  GenLHS(..), generaliseLHS,
  eCheckClosed, eCheckClosedInLHS, eCheckClosedInTagval,
  aCheckClosed, aCheckClosedInLHS, aCheckClosedInTagval,
  ExpandLHS(..), expandLHS, sameLHSsameEnv
) where

import qualified Data.Array.Accelerate.Representation.Array as A
import qualified Data.Array.Accelerate.Representation.Type as A
import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Environment as A
import qualified Data.Array.Accelerate.AST.Idx as A
import qualified Data.Array.Accelerate.AST.LeftHandSide as A
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.Analysis.Match (matchTypeR, matchArraysR, (:~:)(Refl))
import Data.Array.Accelerate.Trafo.AD.Acc
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Exp


sinkExpAenv :: aenv A.:> aenv' -> OpenExp env aenv lab alab args t -> OpenExp env aenv' lab alab args t
sinkExpAenv _ (Const ty x) = Const ty x
sinkExpAenv k (PrimApp ty op e) = PrimApp ty op (sinkExpAenv k e)
sinkExpAenv k (Pair ty e1 e2) = Pair ty (sinkExpAenv k e1) (sinkExpAenv k e2)
sinkExpAenv _ Nil = Nil
sinkExpAenv k (Cond ty c t e) = Cond ty (sinkExpAenv k c) (sinkExpAenv k t) (sinkExpAenv k e)
sinkExpAenv k (Shape (Left (A.Var sht idx))) = Shape (Left (A.Var sht (k A.>:> idx)))
sinkExpAenv _ (Shape (Right lab)) = Shape (Right lab)
sinkExpAenv k (Get ty ti e) = Get ty ti (sinkExpAenv k e)
sinkExpAenv k (Let lhs rhs e) = Let lhs (sinkExpAenv k rhs) (sinkExpAenv k e)
sinkExpAenv _ (Var (A.Var sty idx)) = Var (A.Var sty idx)
sinkExpAenv _ (Arg ty idx) = Arg ty idx
sinkExpAenv _ (Label lab) = Label lab

sinkFunAenv :: aenv A.:> aenv' -> OpenFun env aenv lab alab t -> OpenFun env aenv' lab alab t
sinkFunAenv k (Lam lhs fun) = Lam lhs (sinkFunAenv k fun)
sinkFunAenv k (Body e) = Body (sinkExpAenv k e)

sinkAcc :: env A.:> env' -> OpenAcc env lab alab args t -> OpenAcc env' lab alab args t
sinkAcc _ (Aconst ty x) = Aconst ty x
sinkAcc k (Apair ty e1 e2) = Apair ty (sinkAcc k e1) (sinkAcc k e2)
sinkAcc _ Anil = Anil
sinkAcc k (Acond ty c t e) = Acond ty (sinkExpAenv k c) (sinkAcc k t) (sinkAcc k e)
sinkAcc k (Map ty f e) = Map ty (sinkFunAenv k <$> f) (sinkAcc k e)
sinkAcc k (ZipWith ty f e1 e2) = ZipWith ty (sinkFunAenv k <$> f) (sinkAcc k e1) (sinkAcc k e2)
sinkAcc k (Fold ty f me0 e) = Fold ty (sinkFunAenv k <$> f) (sinkExpAenv k <$> me0) (sinkAcc k e)
sinkAcc k (Generate ty e f) = Generate ty (sinkExpAenv k e) (sinkFunAenv k <$> f)
sinkAcc k (Aget ty ti e) = Aget ty ti (sinkAcc k e)
sinkAcc k (Alet lhs rhs e)
  | GenLHS lhs' <- generaliseLHS lhs =
      Alet lhs' (sinkAcc k rhs) (sinkAcc (A.sinkWithLHS lhs lhs' k) e)
sinkAcc k (Avar (A.Var sty idx)) = Avar (A.Var sty (k A.>:> idx))
sinkAcc _ (Aarg ty idx) = Aarg ty idx
sinkAcc _ (Alabel lab) = Alabel lab

eCheckLocal :: A.ExpVar env t -> TagVal A.TypeR env2 -> Maybe (A.ExpVar env2 t)
eCheckLocal _ TEmpty = Nothing
eCheckLocal (A.Var sty A.ZeroIdx) (TPush _ sty')
  | Just Refl <- matchTypeR (A.TupRsingle sty) sty' =
      Just (A.Var sty ZeroIdx)
  | otherwise = Nothing
eCheckLocal (A.Var sty (A.SuccIdx idx)) (TPush tagval _)
  | Just (A.Var sty' idx') <- eCheckLocal (A.Var sty idx) tagval =
      Just (A.Var sty' (SuccIdx idx'))
  | otherwise = Nothing

aCheckLocal :: A.ArrayVar env t -> TagVal A.ArraysR env2 -> Maybe (A.ArrayVar env2 t)
aCheckLocal _ TEmpty = Nothing
aCheckLocal (A.Var sty A.ZeroIdx) (TPush _ sty')
  | Just Refl <- matchArraysR (A.TupRsingle sty) sty' =
      Just (A.Var sty ZeroIdx)
  | otherwise = Nothing
aCheckLocal (A.Var sty (A.SuccIdx idx)) (TPush tagval _)
  | Just (A.Var sty' idx') <- aCheckLocal (A.Var sty idx) tagval =
      Just (A.Var sty' (SuccIdx idx'))
  | otherwise = Nothing

-- | If the expression is closed in env2, returns the re-typed expression;
-- otherwise, returns Nothing.
eCheckClosed :: OpenExp env aenv lab alab args t -> Maybe (OpenExp () aenv lab alab args t)
eCheckClosed = eCheckClosedInTagval TEmpty

eCheckClosedInLHS :: A.ELeftHandSide t' () env
                  -> OpenExp env2 aenv lab alab args t
                  -> Maybe (OpenExp env aenv lab alab args t)
eCheckClosedInLHS lhs expr = eCheckClosedInTagval (valPushLHS lhs TEmpty) expr

eCheckClosedInTagval :: TagVal A.TypeR env2 -> OpenExp env aenv lab alab args t -> Maybe (OpenExp env2 aenv lab alab args t)
eCheckClosedInTagval tv expr = case expr of
    Const ty x -> Just (Const ty x)
    PrimApp ty op e -> PrimApp ty op <$> eCheckClosedInTagval tv e
    Pair ty e1 e2 -> Pair ty <$> eCheckClosedInTagval tv e1 <*> eCheckClosedInTagval tv e2
    Nil -> Just Nil
    Cond ty c t e -> Cond ty <$> eCheckClosedInTagval tv c <*> eCheckClosedInTagval tv t <*> eCheckClosedInTagval tv e
    Shape avar -> Just (Shape avar)
    Get ty ti e -> Get ty ti <$> eCheckClosedInTagval tv e
    Let lhs rhs e
      | GenLHS lhs' <- generaliseLHS lhs ->
          Let lhs' <$> eCheckClosedInTagval tv rhs <*> eCheckClosedInTagval (valPushLHS lhs' tv) e
    Var var -> Var <$> eCheckLocal var tv
    Arg ty idx -> Just (Arg ty idx)
    Label lab -> Just (Label lab)

eCheckAClosedInTagval :: TagVal A.ArraysR aenv2 -> OpenExp env aenv lab alab args t -> Maybe (OpenExp env aenv2 lab alab args t)
eCheckAClosedInTagval tv expr = case expr of
    Const ty x -> Just (Const ty x)
    PrimApp ty op e -> PrimApp ty op <$> eCheckAClosedInTagval tv e
    Pair ty e1 e2 -> Pair ty <$> eCheckAClosedInTagval tv e1 <*> eCheckAClosedInTagval tv e2
    Nil -> Just Nil
    Shape (Left var) -> Shape . Left <$> aCheckLocal var tv
    Shape (Right _) -> error "Exp with label in arrayvar position is not closed, todo?"
    Cond ty c t e -> Cond ty <$> eCheckAClosedInTagval tv c <*> eCheckAClosedInTagval tv t <*> eCheckAClosedInTagval tv e
    Get ty ti e -> Get ty ti <$> eCheckAClosedInTagval tv e
    Let lhs rhs e -> Let lhs <$> eCheckAClosedInTagval tv rhs <*> eCheckAClosedInTagval tv e
    Var var -> Just (Var var)
    Arg ty idx -> Just (Arg ty idx)
    Label lab -> Just (Label lab)

efCheckAClosedInTagval :: TagVal A.ArraysR aenv2 -> OpenFun env aenv lab alab t -> Maybe (OpenFun env aenv2 lab alab t)
efCheckAClosedInTagval tv (Lam lhs fun) = Lam lhs <$> efCheckAClosedInTagval tv fun
efCheckAClosedInTagval tv (Body e) = Body <$> eCheckAClosedInTagval tv e

-- | If the expression is closed in env2, returns the re-typed expression;
-- otherwise, returns Nothing.
aCheckClosed :: OpenAcc env lab alab args t -> Maybe (OpenAcc () lab alab args t)
aCheckClosed = aCheckClosedInTagval TEmpty

aCheckClosedInLHS :: A.ALeftHandSide t' () env
                  -> OpenAcc env2 lab alab args t
                  -> Maybe (OpenAcc env lab alab args t)
aCheckClosedInLHS lhs expr = aCheckClosedInTagval (valPushLHS lhs TEmpty) expr

aCheckClosedInTagval :: TagVal A.ArraysR env2 -> OpenAcc env lab alab args t -> Maybe (OpenAcc env2 lab alab args t)
aCheckClosedInTagval tv expr = case expr of
    Aconst ty x -> Just (Aconst ty x)
    Apair ty e1 e2 -> Apair ty <$> aCheckClosedInTagval tv e1 <*> aCheckClosedInTagval tv e2
    Anil -> Just Anil
    Acond ty c t e -> Acond ty <$> eCheckAClosedInTagval tv c <*> aCheckClosedInTagval tv t <*> aCheckClosedInTagval tv e
    Map ty f e -> Map ty <$> traverse (efCheckAClosedInTagval tv) f <*> aCheckClosedInTagval tv e
    ZipWith ty f e1 e2 -> ZipWith ty <$> traverse (efCheckAClosedInTagval tv) f <*> aCheckClosedInTagval tv e1 <*> aCheckClosedInTagval tv e2
    Fold ty f me0 e -> Fold ty <$> traverse (efCheckAClosedInTagval tv) f <*> (eCheckAClosedInTagval tv <$> me0) <*> aCheckClosedInTagval tv e
    Generate ty e f -> Generate ty <$> eCheckAClosedInTagval tv e <*> traverse (efCheckAClosedInTagval tv) f
    Aget ty ti e -> Aget ty ti <$> aCheckClosedInTagval tv e
    Alet lhs rhs e
      | GenLHS lhs' <- generaliseLHS lhs ->
          Alet lhs' <$> aCheckClosedInTagval tv rhs <*> aCheckClosedInTagval (valPushLHS lhs' tv) e
    Avar var -> Avar <$> aCheckLocal var tv
    Aarg ty idx -> Just (Aarg ty idx)
    Alabel lab -> Just (Alabel lab)

valPushLHS :: A.LeftHandSide s t env env' -> TagVal (A.TupR s) env -> TagVal (A.TupR s) env'
valPushLHS (A.LeftHandSideWildcard _) tv = tv
valPushLHS (A.LeftHandSideSingle sty) tv = TPush tv (A.TupRsingle sty)
valPushLHS (A.LeftHandSidePair lhs1 lhs2) tv = valPushLHS lhs2 (valPushLHS lhs1 tv)

data ExpandLHS s t env env1
    = forall env2. ExpandLHS (A.LeftHandSide s t env env2) (env1 A.:> env2)

-- Eliminates all Wildcard bindings.
expandLHS :: A.LeftHandSide s t env0 env1 -> ExpandLHS s t env0 env1
expandLHS lhs@(A.LeftHandSideSingle _) = ExpandLHS lhs A.weakenId
expandLHS (A.LeftHandSidePair lhs1 lhs2)
  | ExpandLHS lhs1' weaken1 <- expandLHS lhs1
  , GenLHS lhs2gen <- generaliseLHS lhs2
  , ExpandLHS lhs2' weaken2 <- expandLHS lhs2gen
  = ExpandLHS (A.LeftHandSidePair lhs1' lhs2')
              (weaken2 A..> A.sinkWithLHS lhs2 lhs2gen weaken1)
expandLHS lhs@(A.LeftHandSideWildcard A.TupRunit) = ExpandLHS lhs A.weakenId
expandLHS (A.LeftHandSideWildcard (A.TupRsingle sty)) =
    ExpandLHS (A.LeftHandSideSingle sty) (A.weakenSucc' A.weakenId)
expandLHS (A.LeftHandSideWildcard (A.TupRpair t1 t2))
  | ExpandLHS lhs1' weaken1 <- expandLHS (A.LeftHandSideWildcard t1)
  , ExpandLHS lhs2' weaken2 <- expandLHS (A.LeftHandSideWildcard t2)
  = ExpandLHS (A.LeftHandSidePair lhs1' lhs2') (weaken2 A..> weaken1)

-- Assumes the LeftHandSide's are equal in structure
sameLHSsameEnv :: A.LeftHandSide s t env env1 -> A.LeftHandSide s t env env2 -> env1 :~: env2
sameLHSsameEnv (A.LeftHandSideWildcard _) (A.LeftHandSideWildcard _) = Refl
sameLHSsameEnv (A.LeftHandSideSingle _) (A.LeftHandSideSingle _) = Refl
sameLHSsameEnv (A.LeftHandSidePair a b) (A.LeftHandSidePair c d)
  | Refl <- sameLHSsameEnv a c, Refl <- sameLHSsameEnv b d = Refl
sameLHSsameEnv _ _ = error "sameLHSsameEnv: Different LeftHandSide's"
