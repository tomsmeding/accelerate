{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.Sink (
  sinkExp,
  GenLHS(..), generaliseLHS,
  checkClosed, checkClosedInLHS, checkClosedInTagval
) where

import qualified Data.Array.Accelerate.Representation.Type as A
import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Environment as A
import qualified Data.Array.Accelerate.AST.Idx as A
import qualified Data.Array.Accelerate.AST.LeftHandSide as A
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.Analysis.Match (matchTypeR, (:~:)(Refl))
import Data.Array.Accelerate.Trafo.AD.Exp


sinkExp :: env A.:> env' -> OpenExp env lab args t -> OpenExp env' lab args t
sinkExp _ (Const ty x) = Const ty x
sinkExp k (PrimApp ty op e) = PrimApp ty op (sinkExp k e)
sinkExp k (Pair ty e1 e2) = Pair ty (sinkExp k e1) (sinkExp k e2)
sinkExp _ Nil = Nil
sinkExp k (Get ty ti e) = Get ty ti (sinkExp k e)
sinkExp k (Let lhs rhs e)
  | GenLHS lhs' <- generaliseLHS lhs =
      Let lhs' (sinkExp k rhs) (sinkExp (A.sinkWithLHS lhs lhs' k) e)
sinkExp k (Var (A.Var sty idx)) = Var (A.Var sty (k A.>:> idx))
sinkExp _ (Arg ty idx) = Arg ty idx
sinkExp _ (Label lab) = Label lab

data GenLHS s env t = forall env'. GenLHS (A.LeftHandSide s t env env')

generaliseLHS :: A.LeftHandSide s t env1 env1' -> GenLHS s env2 t
generaliseLHS (A.LeftHandSideWildcard ty) = GenLHS (A.LeftHandSideWildcard ty)
generaliseLHS (A.LeftHandSideSingle ty) = GenLHS (A.LeftHandSideSingle ty)
generaliseLHS (A.LeftHandSidePair lhs1 lhs2)
  | GenLHS lhs1' <- generaliseLHS lhs1
  , GenLHS lhs2' <- generaliseLHS lhs2 =
      GenLHS (A.LeftHandSidePair lhs1' lhs2')

checkLocal :: A.ExpVar env t -> TagVal () env2 -> Maybe (A.ExpVar env2 t)
checkLocal _ TEmpty = Nothing
checkLocal (A.Var sty A.ZeroIdx) (TPush _ _ sty')
  | Just Refl <- matchTypeR (A.TupRsingle sty) sty' =
      Just (A.Var sty ZeroIdx)
  | otherwise = Nothing
checkLocal (A.Var sty (A.SuccIdx idx)) (TPush tagval _ _)
  | Just (A.Var sty' idx') <- checkLocal (A.Var sty idx) tagval =
      Just (A.Var sty' (SuccIdx idx'))
  | otherwise = Nothing

-- | If the expression is closed in env2, returns the re-typed expression;
-- otherwise, returns Nothing.
checkClosed :: OpenExp env lab args t -> Maybe (OpenExp () lab args t)
checkClosed topexpr = checkClosedInTagval TEmpty topexpr

checkClosedInLHS :: A.ELeftHandSide t' () env
                 -> OpenExp env2 lab args t
                 -> Maybe (OpenExp env lab args t)
checkClosedInLHS lhs expr = checkClosedInTagval (valPushLHS lhs TEmpty) expr

checkClosedInTagval :: TagVal () env2 -> OpenExp env lab args t -> Maybe (OpenExp env2 lab args t)
checkClosedInTagval tv expr = case expr of
    Const ty x -> Just (Const ty x)
    PrimApp ty op e -> PrimApp ty op <$> checkClosedInTagval tv e
    Pair ty e1 e2 -> Pair ty <$> checkClosedInTagval tv e1 <*> checkClosedInTagval tv e2
    Nil -> Just Nil
    Get ty ti e -> Get ty ti <$> checkClosedInTagval tv e
    Let lhs rhs e
      | GenLHS lhs' <- generaliseLHS lhs ->
          Let lhs' <$> checkClosedInTagval tv rhs <*> checkClosedInTagval (valPushLHS lhs' tv) e
    Var var -> Var <$> checkLocal var tv
    Arg ty idx -> Just (Arg ty idx)
    Label lab -> Just (Label lab)

valPushLHS :: A.ELeftHandSide t env env' -> TagVal () env -> TagVal () env'
valPushLHS (A.LeftHandSideWildcard _) tv = tv
valPushLHS (A.LeftHandSideSingle sty) tv = TPush tv () (A.TupRsingle sty)
valPushLHS (A.LeftHandSidePair lhs1 lhs2) tv = valPushLHS lhs2 (valPushLHS lhs1 tv)
