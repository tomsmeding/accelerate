{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.Sink (
  sinkExp, sinkExpAenv, sinkFunAenv, sinkAcc,
  eCheckClosedInLHS, aCheckClosedInLHS,
  ExpandLHS(..), expandLHS, sameLHSsameEnv
) where

import qualified Data.Array.Accelerate.Representation.Array as A
import qualified Data.Array.Accelerate.Representation.Type as A
import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Environment as A
import qualified Data.Array.Accelerate.AST.Idx as A
import qualified Data.Array.Accelerate.AST.LeftHandSide as A
import qualified Data.Array.Accelerate.AST.Var as A
import qualified Data.Array.Accelerate.Type as A
import Data.Array.Accelerate.Trafo.Substitution (rebuildLHS)
import Data.Array.Accelerate.Analysis.Match (matchScalarType, matchArrayR, (:~:)(Refl))
import Data.Array.Accelerate.Trafo.AD.Acc
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Exp


sinkExpAenv :: aenv A.:> aenv' -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv' lab alab args tenv t
sinkExpAenv _ (Const lab x) = Const lab x
sinkExpAenv k (PrimApp lab op e) = PrimApp lab op (sinkExpAenv k e)
sinkExpAenv _ (PrimConst lab c) = PrimConst lab c
sinkExpAenv k (Pair ty e1 e2) = Pair ty (sinkExpAenv k e1) (sinkExpAenv k e2)
sinkExpAenv _ (Nil lab) = Nil lab
sinkExpAenv k (Cond lab c t e) = Cond lab (sinkExpAenv k c) (sinkExpAenv k t) (sinkExpAenv k e)
sinkExpAenv k (Shape lab (Left (A.Var sht idx))) = Shape lab (Left (A.Var sht (k A.>:> idx)))
sinkExpAenv _ (Shape lab (Right alab)) = Shape lab (Right alab)
sinkExpAenv k (Index lab (Left (A.Var sht idx)) idxe) = Index lab (Left (A.Var sht (k A.>:> idx))) (sinkExpAenv k idxe)
sinkExpAenv k (Index lab (Right alab) idxe) = Index lab (Right alab) (sinkExpAenv k idxe)
sinkExpAenv k (ShapeSize lab sht e) = ShapeSize lab sht (sinkExpAenv k e)
sinkExpAenv k (Get lab ti e) = Get lab ti (sinkExpAenv k e)
sinkExpAenv _ (Undef lab) = Undef lab
sinkExpAenv k (Let lhs rhs e) = Let lhs (sinkExpAenv k rhs) (sinkExpAenv k e)
sinkExpAenv _ (Var lab var referLab) = Var lab var referLab
sinkExpAenv _ (FreeVar lab var) = FreeVar lab var
sinkExpAenv _ (Arg lab idx) = Arg lab idx

sinkFunAenv :: aenv A.:> aenv' -> OpenFun env aenv lab alab tenv t -> OpenFun env aenv' lab alab tenv t
sinkFunAenv k (Lam lhs fun) = Lam lhs (sinkFunAenv k fun)
sinkFunAenv k (Body e) = Body (sinkExpAenv k e)

sinkAcc :: env A.:> env' -> OpenAcc env lab alab args t -> OpenAcc env' lab alab args t
sinkAcc _ (Aconst lab x) = Aconst lab x
sinkAcc k (Apair lab e1 e2) = Apair lab (sinkAcc k e1) (sinkAcc k e2)
sinkAcc _ (Anil lab) = Anil lab
sinkAcc k (Acond lab c t e) = Acond lab (sinkExpAenv k c) (sinkAcc k t) (sinkAcc k e)
sinkAcc k (Map lab f e) = Map lab (fmapPlain (sinkFunAenv k) f) (sinkAcc k e)
sinkAcc k (ZipWith lab f e1 e2) = ZipWith lab (fmapPlain (sinkFunAenv k) f) (sinkAcc k e1) (sinkAcc k e2)
sinkAcc k (Fold lab f me0 e) = Fold lab (sinkFunAenv k f) (sinkExpAenv k <$> me0) (sinkAcc k e)
sinkAcc k (Scan lab dir f me0 e) = Scan lab dir (sinkFunAenv k f) (sinkExpAenv k <$> me0) (sinkAcc k e)
sinkAcc k (Scan' lab dir f e0 e) = Scan' lab dir (sinkFunAenv k f) (sinkExpAenv k e0) (sinkAcc k e)
sinkAcc k (Backpermute lab dim f e) = Backpermute lab (sinkExpAenv k dim) (sinkFunAenv k f) (sinkAcc k e)
sinkAcc k (Permute lab comb def pf e) = Permute lab (sinkFunAenv k comb) (sinkAcc k def) (sinkFunAenv k pf) (sinkAcc k e)
sinkAcc k (Sum lab e) = Sum lab (sinkAcc k e)
sinkAcc k (Generate lab e f) = Generate lab (sinkExpAenv k e) (fmapPlain (sinkFunAenv k) f)
sinkAcc k (Replicate lab slt sle e) = Replicate lab slt (sinkExpAenv k sle) (sinkAcc k e)
sinkAcc k (Slice lab slt e sle) = Slice lab slt (sinkAcc k e) (sinkExpAenv k sle)
sinkAcc k (Reduce lab slt f e) = Reduce lab slt (sinkFunAenv k f) (sinkAcc k e)
sinkAcc k (Reshape lab sle e) = Reshape lab (sinkExpAenv k sle) (sinkAcc k e)
sinkAcc k (Aget lab ti e) = Aget lab ti (sinkAcc k e)
sinkAcc k (Alet lhs rhs e)
  | A.Exists lhs' <- rebuildLHS lhs =
      Alet lhs' (sinkAcc k rhs) (sinkAcc (A.sinkWithLHS lhs lhs' k) e)
sinkAcc k (Avar lab (A.Var sty idx) referLab) = Avar lab (A.Var sty (k A.>:> idx)) referLab
sinkAcc _ (Aarg lab idx) = Aarg lab idx

aCheckLocal :: A.ArrayVar env t -> TagVal A.ArrayR env2 -> Maybe (A.ArrayVar env2 t)
aCheckLocal _ TEmpty = Nothing
aCheckLocal (A.Var sty A.ZeroIdx) (TPush _ sty')
  | Just Refl <- matchArrayR sty sty' =
      Just (A.Var sty ZeroIdx)
  | otherwise = Nothing
aCheckLocal (A.Var sty (A.SuccIdx idx)) (TPush tagval _)
  | Just (A.Var sty' idx') <- aCheckLocal (A.Var sty idx) tagval =
      Just (A.Var sty' (SuccIdx idx'))
  | otherwise = Nothing

-- | If the expression is closed in env, returns the re-typed expression;
-- otherwise, returns Nothing.
eCheckClosedInLHS :: A.ELeftHandSide t' () env
                  -> OpenExp env2 aenv lab alab args tenv t
                  -> Maybe (OpenExp env aenv lab alab args tenv t)
eCheckClosedInLHS lhs expr = eCheckClosedInTagval (valPushLHS lhs TEmpty) expr

eCheckClosedInTagval :: TagVal A.ScalarType env2 -> OpenExp env aenv lab alab args tenv t -> Maybe (OpenExp env2 aenv lab alab args tenv t)
eCheckClosedInTagval tv expr = case expr of
    Const lab x -> Just (Const lab x)
    PrimApp lab op e -> PrimApp lab op <$> eCheckClosedInTagval tv e
    PrimConst lab c -> Just (PrimConst lab c)
    Pair lab e1 e2 -> Pair lab <$> eCheckClosedInTagval tv e1 <*> eCheckClosedInTagval tv e2
    Nil lab -> Just (Nil lab)
    Cond lab c t e -> Cond lab <$> eCheckClosedInTagval tv c  <*> eCheckClosedInTagval tv t  <*> eCheckClosedInTagval tv e
    Shape lab avar -> Just (Shape lab avar)
    Index lab avar e -> Index lab avar <$> eCheckClosedInTagval tv e
    ShapeSize lab sht e -> ShapeSize lab sht <$> eCheckClosedInTagval tv e
    Get lab ti e -> Get lab ti <$> eCheckClosedInTagval tv e
    Undef lab -> Just (Undef lab)
    Let lhs rhs e
      | A.Exists lhs' <- rebuildLHS lhs ->
          Let lhs' <$> eCheckClosedInTagval tv rhs <*> eCheckClosedInTagval (valPushLHS lhs' tv) e
    Var lab var referLab -> Var lab <$> eCheckLocalT matchScalarType var tv <*> return referLab
    FreeVar lab var -> Just (FreeVar lab var)
    Arg lab idx -> Just (Arg lab idx)

eCheckAClosedInTagval :: TagVal A.ArrayR aenv2 -> OpenExp env aenv lab alab args tenv t -> Maybe (OpenExp env aenv2 lab alab args tenv t)
eCheckAClosedInTagval tv expr = case expr of
    Const lab x -> Just (Const lab x)
    PrimApp lab op e -> PrimApp lab op <$> eCheckAClosedInTagval tv e
    PrimConst lab c -> Just (PrimConst lab c)
    Pair lab e1 e2 -> Pair lab <$> eCheckAClosedInTagval tv e1 <*> eCheckAClosedInTagval tv e2
    Nil lab -> Just (Nil lab)
    Shape lab (Left var) -> Shape lab . Left <$> aCheckLocal var tv
    Shape _ (Right _) -> error "Exp with label in arrayvar position (Shape) is not closed, todo?"
    Index lab (Left var) idxe -> Index lab <$> (Left <$> aCheckLocal var tv) <*> eCheckAClosedInTagval tv idxe
    Index _ (Right _) _ -> error "Exp with label in arrayvar position (Index) is not closed, todo?"
    ShapeSize lab sht e -> ShapeSize lab sht <$> eCheckAClosedInTagval tv e
    Cond lab c t e -> Cond lab <$> eCheckAClosedInTagval tv c  <*> eCheckAClosedInTagval tv t <*> eCheckAClosedInTagval tv e
    Get lab ti e -> Get lab ti <$> eCheckAClosedInTagval tv e
    Undef lab -> Just (Undef lab)
    Let lhs rhs e -> Let lhs <$> eCheckAClosedInTagval tv rhs <*> eCheckAClosedInTagval tv e
    Var lab var referLab -> Just (Var lab var referLab)
    FreeVar lab var -> Just (FreeVar lab var)
    Arg lab idx -> Just (Arg lab idx)

efCheckAClosedInTagval :: TagVal A.ArrayR aenv2 -> OpenFun env aenv lab alab tenv t -> Maybe (OpenFun env aenv2 lab alab tenv t)
efCheckAClosedInTagval tv (Lam lhs fun) = Lam lhs <$> efCheckAClosedInTagval tv fun
efCheckAClosedInTagval tv (Body e) = Body <$> eCheckAClosedInTagval tv e

-- | If the expression is closed in env, returns the re-typed expression;
-- otherwise, returns Nothing.
aCheckClosedInLHS :: A.ALeftHandSide t' () env
                  -> OpenAcc env2 lab alab args t
                  -> Maybe (OpenAcc env lab alab args t)
aCheckClosedInLHS lhs expr = aCheckClosedInTagval (valPushLHS lhs TEmpty) expr

aCheckClosedInTagval :: TagVal A.ArrayR env2 -> OpenAcc env lab alab args t -> Maybe (OpenAcc env2 lab alab args t)
aCheckClosedInTagval tv expr = case expr of
    Aconst lab x -> Just (Aconst lab x)
    Apair lab e1 e2 -> Apair lab <$> aCheckClosedInTagval tv e1 <*> aCheckClosedInTagval tv e2
    Anil lab -> Just (Anil lab)
    Acond lab c t e -> Acond lab <$> eCheckAClosedInTagval tv c <*> aCheckClosedInTagval tv t <*> aCheckClosedInTagval tv e
    Map lab f e -> Map lab <$> traversePlain (efCheckAClosedInTagval tv) f <*> aCheckClosedInTagval tv e
    ZipWith lab f e1 e2 -> ZipWith lab <$> traversePlain (efCheckAClosedInTagval tv) f <*> aCheckClosedInTagval tv e1 <*> aCheckClosedInTagval tv e2
    Fold lab f me0 e -> Fold lab <$> efCheckAClosedInTagval tv f <*> traverse (eCheckAClosedInTagval tv) me0 <*> aCheckClosedInTagval tv e
    Scan lab dir f me0 e -> Scan lab dir <$> efCheckAClosedInTagval tv f <*> traverse (eCheckAClosedInTagval tv) me0 <*> aCheckClosedInTagval tv e
    Scan' lab dir f e0 e -> Scan' lab dir <$> efCheckAClosedInTagval tv f <*> eCheckAClosedInTagval tv e0 <*> aCheckClosedInTagval tv e
    Backpermute lab dim f e -> Backpermute lab <$> eCheckAClosedInTagval tv dim <*> efCheckAClosedInTagval tv f <*> aCheckClosedInTagval tv e
    Permute lab cf def pf e -> Permute lab <$> efCheckAClosedInTagval tv cf <*> aCheckClosedInTagval tv def <*> efCheckAClosedInTagval tv pf <*> aCheckClosedInTagval tv e
    Sum lab e -> Sum lab <$> aCheckClosedInTagval tv e
    Generate lab e f -> Generate lab <$> eCheckAClosedInTagval tv e <*> traversePlain (efCheckAClosedInTagval tv) f
    Replicate lab slt sle e -> Replicate lab slt <$> eCheckAClosedInTagval tv sle <*> aCheckClosedInTagval tv e
    Slice lab slt e sle -> Slice lab slt <$> aCheckClosedInTagval tv e <*> eCheckAClosedInTagval tv sle
    Reduce lab slt f e -> Reduce lab slt <$> efCheckAClosedInTagval tv f <*> aCheckClosedInTagval tv e
    Reshape lab sle e -> Reshape lab <$> eCheckAClosedInTagval tv sle <*> aCheckClosedInTagval tv e
    Aget lab ti e -> Aget lab ti <$> aCheckClosedInTagval tv e
    Alet lhs rhs e
      | A.Exists lhs' <- rebuildLHS lhs ->
          Alet lhs' <$> aCheckClosedInTagval tv rhs <*> aCheckClosedInTagval (valPushLHS lhs' tv) e
    Avar lab var referLab -> Avar lab <$> aCheckLocal var tv <*> return referLab
    Aarg lab idx -> Just (Aarg lab idx)

valPushLHS :: A.LeftHandSide s t env env' -> TagVal s env -> TagVal s env'
valPushLHS (A.LeftHandSideWildcard _) tv = tv
valPushLHS (A.LeftHandSideSingle sty) tv = TPush tv sty
valPushLHS (A.LeftHandSidePair lhs1 lhs2) tv = valPushLHS lhs2 (valPushLHS lhs1 tv)

data ExpandLHS s t env env1
    = forall env2. ExpandLHS (A.LeftHandSide s t env env2) (env1 A.:> env2)

-- Eliminates all Wildcard bindings.
expandLHS :: A.LeftHandSide s t env0 env1 -> ExpandLHS s t env0 env1
expandLHS lhs@(A.LeftHandSideSingle _) = ExpandLHS lhs A.weakenId
expandLHS (A.LeftHandSidePair lhs1 lhs2)
  | ExpandLHS lhs1' weaken1 <- expandLHS lhs1
  , A.Exists lhs2gen <- rebuildLHS lhs2
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
