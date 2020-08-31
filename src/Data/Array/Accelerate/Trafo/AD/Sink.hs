{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.Sink (
  sinkExp, sinkAcc,
  GenLHS(..), generaliseLHS,
  eCheckClosed, eCheckClosedInLHS, eCheckClosedInTagval,
  aCheckClosed, aCheckClosedInLHS, aCheckClosedInTagval
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


sinkExp :: env A.:> env' -> OpenExp env lab args t -> OpenExp env' lab args t
sinkExp _ (Const ty x) = Const ty x
sinkExp k (PrimApp ty op e) = PrimApp ty op (sinkExp k e)
sinkExp k (Pair ty e1 e2) = Pair ty (sinkExp k e1) (sinkExp k e2)
sinkExp _ Nil = Nil
sinkExp k (Cond ty c t e) = Cond ty (sinkExp k c) (sinkExp k t) (sinkExp k e)
sinkExp k (Get ty ti e) = Get ty ti (sinkExp k e)
sinkExp k (Let lhs rhs e)
  | GenLHS lhs' <- generaliseLHS lhs =
      Let lhs' (sinkExp k rhs) (sinkExp (A.sinkWithLHS lhs lhs' k) e)
sinkExp k (Var (A.Var sty idx)) = Var (A.Var sty (k A.>:> idx))
sinkExp _ (Arg ty idx) = Arg ty idx
sinkExp _ (Label lab) = Label lab

sinkAcc :: env A.:> env' -> OpenAcc env lab args t -> OpenAcc env' lab args t
sinkAcc _ (Aconst ty x) = Aconst ty x
sinkAcc k (Apair ty e1 e2) = Apair ty (sinkAcc k e1) (sinkAcc k e2)
sinkAcc _ Anil = Anil
sinkAcc k (Acond ty c t e) = Acond ty c (sinkAcc k t) (sinkAcc k e)
sinkAcc k (Map ty f e) = Map ty f (sinkAcc k e)
sinkAcc k (ZipWith ty f e1 e2) = ZipWith ty f (sinkAcc k e1) (sinkAcc k e2)
sinkAcc k (Fold ty f me0 e) = Fold ty f me0 (sinkAcc k e)
sinkAcc _ (Generate ty e f) = Generate ty e f
sinkAcc k (Aget ty ti e) = Aget ty ti (sinkAcc k e)
sinkAcc k (Alet lhs rhs e)
  | GenLHS lhs' <- generaliseLHS lhs =
      Alet lhs' (sinkAcc k rhs) (sinkAcc (A.sinkWithLHS lhs lhs' k) e)
sinkAcc k (Avar (A.Var sty idx)) = Avar (A.Var sty (k A.>:> idx))
sinkAcc _ (Aarg ty idx) = Aarg ty idx
sinkAcc _ (Alabel lab) = Alabel lab

data GenLHS s env t = forall env'. GenLHS (A.LeftHandSide s t env env')

generaliseLHS :: A.LeftHandSide s t env1 env1' -> GenLHS s env2 t
generaliseLHS (A.LeftHandSideWildcard ty) = GenLHS (A.LeftHandSideWildcard ty)
generaliseLHS (A.LeftHandSideSingle ty) = GenLHS (A.LeftHandSideSingle ty)
generaliseLHS (A.LeftHandSidePair lhs1 lhs2)
  | GenLHS lhs1' <- generaliseLHS lhs1
  , GenLHS lhs2' <- generaliseLHS lhs2 =
      GenLHS (A.LeftHandSidePair lhs1' lhs2')

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
eCheckClosed :: OpenExp env lab args t -> Maybe (OpenExp () lab args t)
eCheckClosed = eCheckClosedInTagval TEmpty

eCheckClosedInLHS :: A.ELeftHandSide t' () env
                  -> OpenExp env2 lab args t
                  -> Maybe (OpenExp env lab args t)
eCheckClosedInLHS lhs expr = eCheckClosedInTagval (valPushLHS lhs TEmpty) expr

eCheckClosedInTagval :: TagVal A.TypeR env2 -> OpenExp env lab args t -> Maybe (OpenExp env2 lab args t)
eCheckClosedInTagval tv expr = case expr of
    Const ty x -> Just (Const ty x)
    PrimApp ty op e -> PrimApp ty op <$> eCheckClosedInTagval tv e
    Pair ty e1 e2 -> Pair ty <$> eCheckClosedInTagval tv e1 <*> eCheckClosedInTagval tv e2
    Nil -> Just Nil
    Cond ty c t e -> Cond ty <$> eCheckClosedInTagval tv c <*> eCheckClosedInTagval tv t <*> eCheckClosedInTagval tv e
    Get ty ti e -> Get ty ti <$> eCheckClosedInTagval tv e
    Let lhs rhs e
      | GenLHS lhs' <- generaliseLHS lhs ->
          Let lhs' <$> eCheckClosedInTagval tv rhs <*> eCheckClosedInTagval (valPushLHS lhs' tv) e
    Var var -> Var <$> eCheckLocal var tv
    Arg ty idx -> Just (Arg ty idx)
    Label lab -> Just (Label lab)

-- | If the expression is closed in env2, returns the re-typed expression;
-- otherwise, returns Nothing.
aCheckClosed :: OpenAcc env lab args t -> Maybe (OpenAcc () lab args t)
aCheckClosed = aCheckClosedInTagval TEmpty

aCheckClosedInLHS :: A.ALeftHandSide t' () env
                  -> OpenAcc env2 lab args t
                  -> Maybe (OpenAcc env lab args t)
aCheckClosedInLHS lhs expr = aCheckClosedInTagval (valPushLHS lhs TEmpty) expr

aCheckClosedInTagval :: TagVal A.ArraysR env2 -> OpenAcc env lab args t -> Maybe (OpenAcc env2 lab args t)
aCheckClosedInTagval tv expr = case expr of
    Aconst ty x -> Just (Aconst ty x)
    Apair ty e1 e2 -> Apair ty <$> aCheckClosedInTagval tv e1 <*> aCheckClosedInTagval tv e2
    Anil -> Just Anil
    Acond ty c t e -> Acond ty <$> return c <*> aCheckClosedInTagval tv t <*> aCheckClosedInTagval tv e
    Map ty f e -> Map ty <$> return f <*> aCheckClosedInTagval tv e
    ZipWith ty f e1 e2 -> ZipWith ty <$> return f <*> aCheckClosedInTagval tv e1 <*> aCheckClosedInTagval tv e2
    Fold ty f me0 e -> Fold ty <$> return f <*> return me0 <*> aCheckClosedInTagval tv e
    Generate ty e f -> return (Generate ty e f)
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
