{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Accelerate.Trafo.AD.Translate (
    translateAcc, translateAfun, translateExp, translateFun,
    untranslateLHSboundExp, UntranslateResultE(..),
    untranslateLHSboundAcc, UntranslateResultA(..)
) where

import Data.List (sort, sortBy)
import Data.Maybe (fromJust)
import Data.Ord (comparing)

import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Environment as A
import qualified Data.Array.Accelerate.AST.LeftHandSide as A
import qualified Data.Array.Accelerate.AST.Idx as A
import qualified Data.Array.Accelerate.AST.Var as A
import qualified Data.Array.Accelerate.Trafo.Substitution as A
import Data.Array.Accelerate.Analysis.Match (matchScalarType, matchArrayR, matchShapeR, (:~:)(Refl))
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape hiding (zip)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.Trafo.AD.Acc as D
import qualified Data.Array.Accelerate.Trafo.AD.Additive as D (zeroForType)
import qualified Data.Array.Accelerate.Trafo.AD.Common as D
import Data.Array.Accelerate.Trafo.AD.Common (labelType, magicLabel, nilLabel, scalarLabel)
import qualified Data.Array.Accelerate.Trafo.AD.Exp as D


-- Partial environments
-- --------------------
--
-- The point of these partial environments is that the top of the reified
-- enviroment is not (), but instead a tracked type variable. PartialVal' has
-- two synchronous tracked type-level environments because we need to do
-- translation between differing top environments at some point.

data PartialVal' s topenv env env2 where
    PTEmpty :: PartialVal' s topenv topenv env2
    PTPush :: PartialVal' s topenv env env2 -> s t -> PartialVal' s topenv (env, t) (env2, t)

type PartialVal s topenv env = PartialVal' s topenv env env

data PushedLHS prf s t topenv env' env2 =
    forall env2'.
        PushedLHS (A.LeftHandSide s t env2 env2') (PartialVal' s topenv env' env2') (FMaybe prf (env' :~: env2'))

-- Fixed Maybe: the branch is fixed by its type
data FMaybe (b :: Bool) a where
    FJust    :: a -> FMaybe 'True a
    FNothing ::      FMaybe 'False a

pvalPushLHS' :: A.LeftHandSide s t env env' -> PartialVal' s topenv env env2 -> FMaybe prf (env :~: env2) -> PushedLHS prf s t topenv env' env2
pvalPushLHS' toplhs toppv FNothing = pvalPushLHS'1 toplhs toppv
  where
    pvalPushLHS'1 :: A.LeftHandSide s t env env' -> PartialVal' s topenv env env2 -> PushedLHS 'False s t topenv env' env2
    pvalPushLHS'1 (A.LeftHandSideWildcard ty) pv = PushedLHS (A.LeftHandSideWildcard ty) pv FNothing
    pvalPushLHS'1 (A.LeftHandSideSingle sty) pv = PushedLHS (A.LeftHandSideSingle sty) (PTPush pv sty) FNothing
    pvalPushLHS'1 (A.LeftHandSidePair lhs1 lhs2) pv
      | PushedLHS lhs1' pv1 FNothing <- pvalPushLHS'1 lhs1 pv
      , PushedLHS lhs2' pv2 FNothing <- pvalPushLHS'1 lhs2 pv1
      = PushedLHS (A.LeftHandSidePair lhs1' lhs2') pv2 FNothing
pvalPushLHS' toplhs toppv (FJust topprf) = pvalPushLHS'2 toplhs toppv topprf
  where
    pvalPushLHS'2 :: A.LeftHandSide s t env env' -> PartialVal' s topenv env env2 -> env :~: env2 -> PushedLHS 'True s t topenv env' env2
    pvalPushLHS'2 (A.LeftHandSideWildcard ty) pv Refl = PushedLHS (A.LeftHandSideWildcard ty) pv (FJust Refl)
    pvalPushLHS'2 (A.LeftHandSideSingle sty) pv Refl = PushedLHS (A.LeftHandSideSingle sty) (PTPush pv sty) (FJust Refl)
    pvalPushLHS'2 (A.LeftHandSidePair lhs1 lhs2) pv prf
      | PushedLHS lhs1' pv1 (FJust prf1) <- pvalPushLHS'2 lhs1 pv prf
      , PushedLHS lhs2' pv2 prf2 <- pvalPushLHS'2 lhs2 pv1 prf1
      = PushedLHS (A.LeftHandSidePair lhs1' lhs2') pv2 prf2

pvalPushLHS :: A.LeftHandSide s t env env' -> PartialVal s topenv env -> PartialVal s topenv env'
pvalPushLHS lhs pv
  | PushedLHS _ pv' (FJust Refl) <- pvalPushLHS' lhs pv (FJust Refl)
  = pv'

-- If the variable is local within the known portion of the PartialVal, returns
-- the variable unchanged; else, returns a reference in the topenv of the
-- PartialVal.
checkLocalP' :: (forall t1 t2. s t1 -> s t2 -> Maybe (t1 :~: t2)) -> A.Var s env t -> PartialVal' s topenv env env2 -> Either (A.Var s topenv t) (A.Var s env2 t)
checkLocalP' _ var PTEmpty = Left var
checkLocalP' match (A.Var sty A.ZeroIdx) (PTPush _ sty')
  | Just Refl <- match sty sty' =
      Right (A.Var sty A.ZeroIdx)
  | otherwise = error "Idx/env types do not match up in checkLocalP'"
checkLocalP' match (A.Var sty (A.SuccIdx idx)) (PTPush tagval _) =
  case checkLocalP' match (A.Var sty idx) tagval of
    Right (A.Var sty' idx') -> Right (A.Var sty' (A.SuccIdx idx'))
    Left topvar -> Left topvar

-- Check if the variable can be re-localised under the known part of the
-- PartialVal. If so, returns the variable with the re-localised environment.
-- If not, e.g. if it refers to the unknown portion, returns Nothing.
checkLocalPFallible :: (forall t1 t2. s t1 -> s t2 -> Maybe (t1 :~: t2)) -> A.Var s env2 t -> PartialVal s topenv env -> Maybe (A.Var s env t)
checkLocalPFallible _ _ PTEmpty = Nothing
checkLocalPFallible match (A.Var sty A.ZeroIdx) (PTPush _ sty')
  | Just Refl <- match sty sty' =
      Just (A.Var sty A.ZeroIdx)
  | otherwise = Nothing
checkLocalPFallible match (A.Var sty (A.SuccIdx idx)) (PTPush tagval _)
  | Just (A.Var sty' idx') <- checkLocalPFallible match (A.Var sty idx) tagval =
      Just (A.Var sty' (A.SuccIdx idx'))
  | otherwise = Nothing


-- Translate implementation
-- ------------------------

translateAfun :: A.OpenAfun aenv t -> D.OpenAfun topaenv () () args aenv t
translateAfun = translateAfunInPVal PTEmpty

translateAfunInPVal :: PartialVal' ArrayR taenv aenv aenv2 -> A.OpenAfun aenv t -> D.OpenAfun aenv2 () () args taenv t
translateAfunInPVal pv (A.Alam lhs fun)
  | PushedLHS lhs' pv' _ <- pvalPushLHS' lhs pv FNothing
  = D.Alam lhs' (translateAfunInPVal pv' fun)
translateAfunInPVal pv (A.Abody e) =
  D.Abody (translateAccInPVal (\_ pv' var@(A.Var ArrayR{} _) -> checkLocalP' matchArrayR var pv') pv FNothing e)

translateAcc :: A.OpenAcc aenv t -> D.OpenAcc aenv () () args aenv t
translateAcc = translateAccInPVal (\(FJust Refl) _ var@(A.Var ArrayR{} _) -> Right var) PTEmpty (FJust Refl)

translateAccInPVal :: forall aenv aenv2 taenv args t prf.
                      (forall aenv' aenv2' t'.
                          FMaybe prf (aenv' :~: aenv2')
                       -> PartialVal' ArrayR taenv aenv' aenv2'
                       -> A.ArrayVar aenv' t'
                       -> Either (A.ArrayVar taenv t') (A.ArrayVar aenv2' t'))
                   -> PartialVal' ArrayR taenv aenv aenv2
                   -> FMaybe prf (aenv :~: aenv2)
                   -> A.OpenAcc aenv t
                   -> D.OpenAcc aenv2 () () args taenv t
translateAccInPVal vt pv prf (A.OpenAcc expr) = case expr of
    A.Use ty arr              -> D.Aconst (nilLabel ty) arr
    A.Apair e1 e2             -> D.Apair (nilLabel (A.arraysR expr)) (trA e1) (trA e2)
    A.Anil                    -> D.Anil (nilLabel TupRunit)
    A.Acond c t e             -> D.Acond (nilLabel (A.arraysR expr)) (trE c) (trA t) (trA e)
    A.Map _ f e               -> D.Map (nilLabel (A.arrayR expr)) (D.ELPlain $ trF f) (trA e)
    A.ZipWith _ f e1 e2       -> D.ZipWith (nilLabel (A.arrayR expr)) (D.ELPlain $ toPairedBinop $ trF f) (trA e1) (trA e2)
    A.Fold (A.Lam (A.LeftHandSideSingle t) (A.Lam (A.LeftHandSideSingle _)
              (A.Body (A.PrimApp (A.PrimAdd _)
                                 (A.Pair (A.Evar (A.Var _ (A.SuccIdx A.ZeroIdx)))
                                         (A.Evar (A.Var _ A.ZeroIdx)))))))
           initval e
      | Just (A.Const _ x) <- initval, isZeroConstant t x ->
          D.Sum (nilLabel (A.arrayR expr)) (trA e)
      | Nothing <- initval ->
          D.Sum (nilLabel (A.arrayR expr)) (trA e)
    A.Fold f me0 e            -> D.Fold (nilLabel (A.arrayR expr)) (toPairedBinop $ trF f) (trE <$> me0) (trA e)
    A.Scan dir f me0 e        -> D.Scan (nilLabel (A.arrayR expr)) dir (toPairedBinop $ trF f) (trE <$> me0) (trA e)
    A.Scan' dir f e0 e        -> D.Scan' (nilLabel (A.arraysR expr)) dir (toPairedBinop $ trF f) (trE e0) (trA e)
    A.Generate ty she f       -> D.Generate (nilLabel ty) (trE she) (D.ELPlain $ trF f)
    A.Replicate slt sle e     -> D.Replicate (nilLabel (A.arrayR expr)) slt (trE sle) (trA e)
    A.Slice slt e sle         -> D.Slice (nilLabel (A.arrayR expr)) slt (trA e) (trE sle)
    A.Reshape _ sle e         -> D.Reshape (nilLabel (A.arrayR expr)) (trE sle) (trA e)
    A.Backpermute shr dim f e -> D.Backpermute (nilLabel (ArrayR shr (arrayRtype (A.arrayR e)))) (trE dim) (trF f) (trA e)
    A.AcustomDeriv t f g a    ->
      let t' = A.arraysR a
      in D.Acustom (nilLabel t) (nilLabel t') (trAF f) (nilLabel t') (nilLabel t) (trAF (curryAfun g)) (trA a)
    A.Alet lhs def body
      | PushedLHS lhs' pv' prf' <- pvalPushLHS' lhs pv prf
      -> D.Alet lhs' (trA def) (translateAccInPVal vt pv' prf' body)
    A.Avar var                -> either D.smartAfreeVar D.smartAvar (vt prf pv var)
    _ -> internalError ("AD.translateAccInPVal: Cannot perform AD on Acc node <" ++ A.showPreAccOp expr ++ ">")
  where
    trE :: A.OpenExp env aenv t' -> D.OpenExp env aenv2 () () args' env taenv t'
    trE = translateExp' (vt prf pv)

    trF :: A.OpenFun env aenv t' -> D.OpenFun env aenv2 () () args' env taenv t'
    trF = translateFun' (vt prf pv)

    trA :: A.OpenAcc aenv t' -> D.OpenAcc aenv2 () () args taenv t'
    trA = translateAccInPVal vt pv prf

    trAF :: A.OpenAfun aenv t' -> D.OpenAfun aenv2 () () args taenv t'
    trAF = translateAfunInPVal pv

    toPairedBinop :: D.OpenFun env aenv' lab alab args' tenv taenv' (t1 -> t2 -> t3) -> D.OpenFun env aenv' lab alab args' tenv taenv' ((t1, t2) -> t3)
    toPairedBinop (D.Lam lhs1 (D.Lam lhs2 (D.Body ex))) = D.Lam (A.LeftHandSidePair lhs1 lhs2) (D.Body ex)
    toPairedBinop _ = error "Impossible GADTs"

    isZeroConstant :: ScalarType t' -> t' -> Bool
    isZeroConstant (SingleScalarType (NumSingleType (FloatingNumType TypeFloat))) 0 = True
    isZeroConstant _ _ = False

translateFun :: A.OpenFun env aenv t -> D.OpenFun topenv aenv () alab args env taenv t
translateFun = translateFun' Right

translateFun' :: (forall t'.
                     A.ArrayVar aenv t'
                  -> Either (A.ArrayVar taenv t') (A.ArrayVar aenv2 t'))
              -> A.OpenFun env aenv t
              -> D.OpenFun topenv aenv2 () alab args env taenv t
translateFun' avt = translateFunInPVal avt PTEmpty

translateFunInPVal :: (forall t'.
                          A.ArrayVar aenv t'
                       -> Either (A.ArrayVar taenv t') (A.ArrayVar aenv2 t'))
                   -> PartialVal' ScalarType tenv env env2
                   -> A.OpenFun env aenv t
                   -> D.OpenFun env2 aenv2 () alab args tenv taenv t
translateFunInPVal arrvartrans pv (A.Lam lhs fun)
  | PushedLHS lhs' pv' _ <- pvalPushLHS' lhs pv FNothing
  = D.Lam lhs' (translateFunInPVal arrvartrans pv' fun)
translateFunInPVal arrvartrans pv (A.Body e) =
  let vartrans _ pv' var = case checkLocalP' matchScalarType var pv' of
                             Right var'@(A.Var _ _) -> D.smartVar var'
                             Left topvar@(A.Var ty _) -> D.FreeVar (nilLabel ty) topvar
  in D.Body (translateExpInPVal vartrans arrvartrans pv FNothing e)

translateExp :: A.OpenExp env aenv t -> D.OpenExp env aenv () alab args env taenv t
translateExp = translateExp' Right

translateExp' :: (forall t'.
                     A.ArrayVar aenv t'
                  -> Either (A.ArrayVar taenv t') (A.ArrayVar aenv2 t'))
              -> A.OpenExp env aenv t
              -> D.OpenExp env aenv2 () alab args env taenv t
translateExp' avt = translateExpInPVal (\(FJust Refl) _ var -> D.smartVar var) avt PTEmpty (FJust Refl)

translateExpInPVal :: (forall env' env2' t'.
                          FMaybe prf (env' :~: env2')
                       -> PartialVal' ScalarType tenv env' env2'
                       -> A.ExpVar env' t'
                       -> D.OpenExp env2' aenv2 () alab args tenv taenv t')
                   -> (forall t'.
                          A.ArrayVar aenv t'
                       -> Either (A.ArrayVar taenv t') (A.ArrayVar aenv2 t'))
                   -> PartialVal' ScalarType tenv env env2
                   -> FMaybe prf (env :~: env2)
                   -> A.OpenExp env aenv t
                   -> D.OpenExp env2 aenv2 () alab args tenv taenv t
translateExpInPVal vt avt pv prf expr = case expr of
    A.Const ty con -> D.Const (nilLabel ty) con
    A.PrimApp f e -> D.PrimApp (nilLabel (A.expType expr)) f (translateExpInPVal vt avt pv prf e)
    A.PrimConst c -> D.PrimConst (nilLabel (SingleScalarType (A.primConstType c))) c
    A.Evar var -> vt prf pv var
    A.Let lhs def body
      | PushedLHS lhs' pv' prf' <- pvalPushLHS' lhs pv prf
      -> D.Let lhs' (translateExpInPVal vt avt pv prf def) (translateExpInPVal vt avt pv' prf' body)
    A.Nil -> D.Nil magicLabel
    A.Cond c t e -> D.Cond (nilLabel (A.expType t)) (translateExpInPVal vt avt pv prf c) (translateExpInPVal vt avt pv prf t) (translateExpInPVal vt avt pv prf e)
    A.Pair e1 e2 -> D.Pair (nilLabel (A.expType expr)) (translateExpInPVal vt avt pv prf e1) (translateExpInPVal vt avt pv prf e2)
    A.Shape var@(A.Var (ArrayR sht _) _) -> D.Shape (nilLabel (shapeType sht)) (either D.ARFree D.ARVar (avt var))
    A.Index var@(A.Var (ArrayR _ ty) _) e -> D.Index (nilLabel ty) (either D.ARFree D.ARVar (avt var)) scalarLabel (translateExpInPVal vt avt pv prf e)
    A.ShapeSize sht e -> D.ShapeSize scalarLabel sht (translateExpInPVal vt avt pv prf e)
    A.Undef ty -> D.Undef (nilLabel ty)
    A.EcustomDeriv t f g e ->
      let t' = A.expType e
      in D.Ecustom (nilLabel t) (nilLabel t') (translateFunInPVal avt pv f) (nilLabel t') (nilLabel t) (translateFunInPVal avt pv (curryFun g)) (translateExpInPVal vt avt pv prf e)
    _ -> internalError ("AD.translateExp: Cannot perform AD on Exp node <" ++ A.showExpOp expr ++ ">")

data UntranslateResultE a env aenv t =
    forall env'. UntranslateResultE (A.ELeftHandSide a env env') (A.OpenExp env' aenv t)

untranslateLHSboundExp :: A.ELeftHandSide a () env
                       -> D.OpenExp env aenv lab alab args tenv taenv t
                       -> taenv A.:> aenv
                       -> tenv A.:> env1
                       -> UntranslateResultE a env1 aenv t
untranslateLHSboundExp toplhs topexpr topaweak topweak
  | A.Exists toplhs' <- A.rebuildLHS toplhs =
      UntranslateResultE toplhs' (go topaweak (A.weakenWithLHS toplhs' A..> topweak) (pvalPushLHS toplhs' PTEmpty) topexpr)
  where
    go :: taenv A.:> aenv -> tenv A.:> env2 -> PartialVal ScalarType topenv env2 -> D.OpenExp env aenv lab alab args tenv taenv t -> A.OpenExp env2 aenv t
    go aw w pv expr = case expr of
        D.Const lab con -> A.Const (labelType lab) con
        D.PrimApp _ f e -> A.PrimApp f (go aw w pv e)
        D.PrimConst _ c -> A.PrimConst c
        -- TODO: Don't use a fallible call here, perhaps something with the double-tracking of PartialVal' ?
        D.Var _ var _ -> A.Evar (fromJust (checkLocalPFallible matchScalarType var pv))
        D.FreeVar _ var -> A.Evar (A.weaken w var)
        D.Let lhs def body
          | A.Exists lhs' <- A.rebuildLHS lhs
          -> A.Let lhs' (go aw w pv def) (go aw (A.weakenWithLHS lhs' A..> w) (pvalPushLHS lhs' pv) body)
        D.Nil _ -> A.Nil
        D.Pair _ e1 e2 -> A.Pair (go aw w pv e1) (go aw w pv e2)
        D.Cond _ e1 e2 e3 -> A.Cond (go aw w pv e1) (go aw w pv e2) (go aw w pv e3)
        D.Shape _ (D.ARVar avar) -> A.Shape avar
        D.Shape _ (D.ARFree avar) -> A.Shape (A.weaken aw avar)
        D.Shape _ (D.ARLab _) -> internalError "AD.untranslateLHSboundExp: Cannot translate label (Shape) in array var position"
        D.Index _ (D.ARVar avar) _ e -> A.Index avar (go aw w pv e)
        D.Index _ (D.ARFree avar) _ e -> A.Index (A.weaken aw avar) (go aw w pv e)
        D.Index _ (D.ARLab _) _ _ -> internalError "AD.untranslateLHSboundExp: Cannot translate label (Index) in array var position"
        D.ShapeSize _ sht e -> A.ShapeSize sht (go aw w pv e)
        D.Get _ path e
          | D.LetBoundVars lhs vars <- euntranslateGet (D.etypeOf e) path
          -> A.Let lhs (go aw w pv e) (a_evars vars)
        D.Undef lab -> A.Undef (labelType lab)
        D.Arg _ _ _ -> internalError "AD.untranslateLHSboundExp: Unexpected Arg in untranslate!"
        D.Ecustom lab _ f _ _ g e -> A.EcustomDeriv (labelType lab) (goF aw w pv f) (uncurryFun (goF aw w pv g)) (go aw w pv e)

    goF :: taenv A.:> aenv -> tenv A.:> env2 -> PartialVal ScalarType topenv env2 -> D.OpenFun env aenv lab alab args tenv taenv t -> A.OpenFun env2 aenv t
    goF aw w pv (D.Lam lhs fun)
      | A.Exists lhs' <- A.rebuildLHS lhs
      = A.Lam lhs' (goF aw (A.weakenWithLHS lhs' A..> w) (pvalPushLHS lhs' pv) fun)
    goF aw w pv (D.Body e) = A.Body (go aw w pv e)

untranslateLHSboundExpA :: forall a env env1 lab alab args tenv taenv t aenv topaenv aenv2.
                           A.ELeftHandSide a () env
                        -> D.OpenExp env aenv lab alab args tenv taenv t
                        -> taenv A.:> aenv2
                        -> PartialVal ArrayR topaenv aenv2
                        -> UntranslateResultE a env1 aenv2 t
untranslateLHSboundExpA toplhs topexpr arrweak arrpv
  | A.Exists toplhs' <- A.rebuildLHS toplhs =
      UntranslateResultE toplhs' (go arrweak (pvalPushLHS toplhs' PTEmpty) topexpr)
  where
    go :: taenv A.:> aenv2 -> PartialVal ScalarType topenv env2 -> D.OpenExp env' aenv lab alab args tenv taenv t' -> A.OpenExp env2 aenv2 t'
    go aw pv expr = case expr of
        D.Const lab con -> A.Const (labelType lab) con
        D.PrimApp _ f e -> A.PrimApp f (go aw pv e)
        D.PrimConst _ c -> A.PrimConst c
        -- TODO: Don't use a fallible call here, perhaps something with the double-tracking of PartialVal' ?
        D.Var _ var _ -> A.Evar (fromJust (checkLocalPFallible matchScalarType var pv))
        D.FreeVar _ _ -> internalError "AD.untranslateLHSboundExpA: Unexpected free expression variable in array code"
        D.Let lhs def body
          | A.Exists lhs' <- A.rebuildLHS lhs
          -> A.Let lhs' (go aw pv def) (go aw (pvalPushLHS lhs' pv) body)
        D.Nil _ -> A.Nil
        D.Pair _ e1 e2 -> A.Pair (go aw pv e1) (go aw pv e2)
        D.Cond _ e1 e2 e3 -> A.Cond (go aw pv e1) (go aw pv e2) (go aw pv e3)
        D.Shape _ (D.ARVar avar) -> A.Shape (fromJust (checkLocalPFallible matchArrayR avar arrpv))
        D.Shape _ (D.ARFree avar) -> A.Shape (A.weaken aw avar)
        D.Shape _ (D.ARLab _) -> internalError "AD.untranslateLHSboundExpA: Cannot translate label (Shape) in array var position"
        D.Index _ (D.ARVar avar) _ e -> A.Index (fromJust (checkLocalPFallible matchArrayR avar arrpv)) (go aw pv e)
        D.Index _ (D.ARFree avar) _ e -> A.Index (A.weaken aw avar) (go aw pv e)
        D.Index _ (D.ARLab _) _ _ -> internalError "AD.untranslateLHSboundExpA: Cannot translate label (Index) in array var position"
        D.ShapeSize _ sht e -> A.ShapeSize sht (go aw pv e)
        D.Get _ path e
          | D.LetBoundVars lhs vars <- euntranslateGet (D.etypeOf e) path
          -> A.Let lhs (go aw pv e) (a_evars vars)
        D.Undef lab -> A.Undef (labelType lab)
        D.Arg _ _ _ -> internalError "AD.untranslateLHSboundExpA: Unexpected Arg in untranslate!"
        D.Ecustom lab _ f _ _ g e -> A.EcustomDeriv (labelType lab) (goF aw pv f) (uncurryFun (goF aw pv g)) (go aw pv e)

    goF :: taenv A.:> aenv2 -> PartialVal ScalarType topenv env2 -> D.OpenFun env' aenv lab alab args tenv taenv t' -> A.OpenFun env2 aenv2 t'
    goF aw pv (D.Lam lhs fun)
      | A.Exists lhs' <- A.rebuildLHS lhs
      = A.Lam lhs' (goF aw (pvalPushLHS lhs' pv) fun)
    goF aw pv (D.Body e) = A.Body (go aw pv e)

untranslateClosedExp :: forall lab alab args t aenv taenv. taenv A.:> aenv -> D.OpenExp () aenv lab alab args () taenv t -> A.OpenExp () aenv t
untranslateClosedExp aweak expr
  | UntranslateResultE A.LeftHandSideUnit res <-
        untranslateLHSboundExp A.LeftHandSideUnit expr aweak A.weakenId
            :: UntranslateResultE () () aenv t
  = res
untranslateClosedExp _ _ = error "unreachable"

untranslateClosedExpA :: forall aenv lab alab args tenv taenv t topaenv aenv2.
                         taenv A.:> aenv2
                      -> PartialVal ArrayR topaenv aenv2
                      -> D.OpenExp () aenv lab alab args tenv taenv t
                      -> A.OpenExp () aenv2 t
untranslateClosedExpA arrweak arrpv expr
  | UntranslateResultE A.LeftHandSideUnit res <-
        untranslateLHSboundExpA A.LeftHandSideUnit expr arrweak arrpv
            :: UntranslateResultE () () aenv2 t
  = res
untranslateClosedExpA _ _ _ = error "unreachable"

data UntranslateFunResultE a env aenv t =
    forall env'. UntranslateFunResultE (A.ELeftHandSide a env env') (A.OpenFun env' aenv t)

untranslateClosedFunA :: forall lab alab t args tenv taenv topaenv aenv aenv2.
                         D.OpenFun () aenv lab alab args tenv taenv t
                      -> taenv A.:> aenv2
                      -> PartialVal ArrayR topaenv aenv2
                      -> A.OpenFun () aenv2 t
untranslateClosedFunA topfun arrweak arrpv
  | UntranslateFunResultE A.LeftHandSideUnit fun' <- go A.LeftHandSideUnit topfun
  = fun'
  where
    go :: A.ELeftHandSide a () env -> D.OpenFun env aenv lab alab args tenv taenv t' -> UntranslateFunResultE a () aenv2 t'
    go lhs (D.Lam bindings fun)
      | UntranslateFunResultE (A.LeftHandSidePair lhs' bindings') res
          <- go (A.LeftHandSidePair lhs bindings) fun
      = UntranslateFunResultE lhs' (A.Lam bindings' res)
    go lhs (D.Body body)
      | UntranslateResultE lhs' res <- untranslateLHSboundExpA lhs body arrweak arrpv
      = UntranslateFunResultE lhs' (A.Body res)
    go _ _ = error "unreachable"
untranslateClosedFunA _ _ _ = error "unreachable"

data UntranslateResultA a aenv t =
    forall aenv'. UntranslateResultA (A.ALeftHandSide a aenv aenv') (A.OpenAcc aenv' t)

untranslateLHSboundAcc :: A.ALeftHandSide a () aenv
                       -> D.OpenAcc aenv lab alab args taenv t
                       -> taenv A.:> aenv1
                       -> UntranslateResultA a aenv1 t
untranslateLHSboundAcc toplhs topexpr topweak
  | A.Exists toplhs' <- A.rebuildLHS toplhs =
      UntranslateResultA toplhs' (go (A.weakenWithLHS toplhs' A..> topweak) (pvalPushLHS toplhs' PTEmpty) topexpr)
  where
    go :: taenv A.:> aenv2 -> PartialVal ArrayR topenv aenv2 -> D.OpenAcc aenv lab args alab taenv t -> A.OpenAcc aenv2 t
    go w pv expr = A.OpenAcc $ case expr of
        D.Aconst lab con -> A.Use (D.labelType lab) con
        D.Avar _ var _ -> A.Avar (fromJust (checkLocalPFallible matchArrayR var pv))
        D.AfreeVar _ var -> A.Avar (A.weaken w var)
        D.Alet lhs def body
          | A.Exists lhs' <- A.rebuildLHS lhs
          -> A.Alet lhs' (go w pv def) (go (A.weakenWithLHS lhs' A..> w) (pvalPushLHS lhs' pv) body)
        D.Anil _ -> A.Anil
        D.Apair _ e1 e2 -> A.Apair (go w pv e1) (go w pv e2)
        D.Acond _ e1 e2 e3 -> A.Acond (untranslateClosedExpA w pv e1) (go w pv e2) (go w pv e3)
        D.Map (labelType -> ArrayR _ ty) (D.ELPlain f) e -> A.Map ty (untranslateClosedFunA f w pv) (go w pv e)
        D.ZipWith (labelType -> ArrayR _ ty) (D.ELPlain f) e1 e2 -> A.ZipWith ty (untranslateClosedFunA (fromPairedBinop f) w pv) (go w pv e1) (go w pv e2)
        D.Fold _ f me0 e -> A.Fold (untranslateClosedFunA (fromPairedBinop f) w pv) (untranslateClosedExpA w pv <$> me0) (go w pv e)
        D.Scan _ dir f me0 e -> A.Scan dir (untranslateClosedFunA (fromPairedBinop f) w pv) (untranslateClosedExpA w pv <$> me0) (go w pv e)
        D.Scan' _ dir f e0 e -> A.Scan' dir (untranslateClosedFunA (fromPairedBinop f) w pv) (untranslateClosedExpA w pv e0) (go w pv e)
        D.Sum (labelType -> ArrayR _ (TupRsingle ty@(SingleScalarType (NumSingleType nt)))) e ->
            A.Fold (A.Lam (A.LeftHandSideSingle ty) (A.Lam (A.LeftHandSideSingle ty)
                      (A.Body (A.PrimApp (A.PrimAdd nt)
                                         (A.Pair (A.Evar (A.Var ty (A.SuccIdx A.ZeroIdx)))
                                                 (A.Evar (A.Var ty A.ZeroIdx)))))))
                   (Just (untranslateClosedExp w (D.zeroForType ty)))
                   (go w pv e)
        D.Generate (labelType -> ty) e (D.ELPlain f) -> A.Generate ty (untranslateClosedExpA w pv e) (untranslateClosedFunA f w pv)
        D.Replicate _ slt sle e -> A.Replicate slt (untranslateClosedExpA w pv sle) (go w pv e)
        D.Slice _ slt e sle -> A.Slice slt (go w pv e) (untranslateClosedExpA w pv sle)
        D.Reduce _ spec combfun e
          | ReduceConvert shtype sortedSpec shlhs fullToSorted sortedToFull <- reduceConvert spec
          , TupRsingle argtype@(ArrayR shtype' _) <- D.atypeOf e
          , Just Refl <- matchShapeR shtype shtype' ->
              A.Alet (A.LeftHandSideSingle argtype) (go w pv e)
                     (let shexp = A.Let shlhs (A.Shape (A.Var argtype A.ZeroIdx)) (a_evars fullToSorted)
                          pv' = pvalPushLHS (A.LeftHandSideSingle argtype) pv
                          reshapeExp = A.Let shlhs shexp (multiplyReduced sortedSpec)
                      in A.OpenAcc $ A.Fold (untranslateClosedFunA combfun (A.weakenSucc' w) pv') Nothing $
                             A.OpenAcc $ A.Reshape (ShapeRsnoc (D.rsReducedShapeR spec)) reshapeExp $
                                 A.OpenAcc $ A.Backpermute shtype shexp (A.Lam shlhs (A.Body (a_evars sortedToFull)))
                                                           (A.OpenAcc $ A.Avar (A.Var argtype A.ZeroIdx)))
        D.Reshape (labelType -> ArrayR sht _) she e -> A.Reshape sht (untranslateClosedExpA w pv she) (go w pv e)
        D.Backpermute (labelType -> ArrayR sht _) dim f e -> A.Backpermute sht (untranslateClosedExpA w pv dim) (untranslateClosedFunA f w pv) (go w pv e)
        D.Permute _ cf def pf e -> A.Permute (untranslateClosedFunA cf w pv) (go w pv def) (untranslateClosedFunA pf w pv) (go w pv e)
        D.Aget _ path e
          | D.LetBoundVars lhs vars <- auntranslateGet (D.atypeOf e) path
          -> A.Alet lhs (go w pv e) (a_avars vars)
        D.Acustom lab _ f _ _ g e -> A.AcustomDeriv (labelType lab) (goAF w pv f) (uncurryAfun (goAF w pv g)) (go w pv e)
        D.Aarg _ _ _ -> internalError "AD.untranslateLHSboundAcc: Unexpected Arg in untranslate!"
        D.Map _ _ _ -> error "Unexpected Map shape in untranslate"
        D.ZipWith _ _ _ _ -> error "Unexpected ZipWith shape in untranslate"
        D.Sum _ _ -> error "Unexpected Sum shape in untranslate"
        D.Generate _ _ _ -> error "Unexpected Generate shape in untranslate"
        D.Reduce _ _ _ _ -> error "Unexpected Reduce shape in untranslate"

    goAF :: taenv A.:> aenv2 -> PartialVal ArrayR topenv aenv2 -> D.OpenAfun aenv lab args alab taenv t -> A.OpenAfun aenv2 t
    goAF w pv (D.Alam lhs fun)
      | A.Exists lhs' <- A.rebuildLHS lhs
      = A.Alam lhs' (goAF (A.weakenWithLHS lhs' A..> w) (pvalPushLHS lhs' pv) fun)
    goAF w pv (D.Abody acc) = A.Abody (go w pv acc)

    fromPairedBinop :: D.OpenFun env aenv lab alab args tenv taenv ((t1, t2) -> t3) -> D.OpenFun env aenv lab alab args tenv taenv (t1 -> t2 -> t3)
    fromPairedBinop (D.Lam (A.LeftHandSidePair lhs1 lhs2) (D.Body ex)) = D.Lam lhs1 (D.Lam lhs2 (D.Body ex))
    fromPairedBinop (D.Lam (A.LeftHandSideWildcard (TupRpair t1 t2)) (D.Body ex)) =
        D.Lam (A.LeftHandSideWildcard t1) (D.Lam (A.LeftHandSideWildcard t2) (D.Body ex))
    fromPairedBinop _ = error "Impossible GADTs"

-- Notable is that the index list is always a list of integers, and a list of
-- integers sorted is still a list of integers, of the same length. Thus the
-- sorted index sequence _type_ is exactly equal to the original one. This is
-- why there is no 'sorted' equivalent to 'full'; both are the same type.
data ReduceConvert red full =
    forall spec.
        ReduceConvert (ShapeR full)
                      (D.ReduceSpec spec red full)
                      (A.ELeftHandSide full () full)
                      (A.ExpVars full ({- sorted -} full))
                      (A.ExpVars ({- sorted -} full) full)

data SomeReduceSpec =
    forall spec red full.
        SomeReduceSpec (D.ReduceSpec spec red full)
                       (D.TagVal OnlyInt full)

data OnlyInt a where
    OnlyInt :: OnlyInt Int

-- How does one utterly subvert the Accelerate type safety system to do weird stuff? Like this.
reduceConvert :: D.ReduceSpec spec red full -> ReduceConvert red full
reduceConvert spec
  | let spec' = untypeifySpec spec
        sortedSpec = sort spec'
        -- These two lines are the core transformation implemented here. Nothing more.
        sortedFullIndices = map snd (sortBy (comparing fst) (zip spec' [0..]))
        fullSortedIndices = invertPermutation sortedFullIndices
  , SomeReduceSpec sortedSpec' tagval <- typeifySpec sortedSpec
  , Just (shaper, shapelhs, Refl) <- specSameFull spec sortedSpec'
  , Just Refl <- specSameRed spec sortedSpec'
  , let sortedFullVars = map (enforceLocal tagval) sortedFullIndices
        sortedFullTup = tuplify tagval sortedFullVars
        fullSortedVars = map (enforceLocal tagval) fullSortedIndices
        fullSortedTup = tuplify tagval fullSortedVars
  = ReduceConvert shaper sortedSpec' shapelhs sortedFullTup fullSortedTup
  where
    untypeifySpec :: D.ReduceSpec spec red full -> [Bool]  -- Bool: == Keep
    untypeifySpec D.RSpecNil = []
    untypeifySpec (D.RSpecReduce spec') = False : untypeifySpec spec'
    untypeifySpec (D.RSpecKeep spec') = True : untypeifySpec spec'

    typeifySpec :: [Bool] -> SomeReduceSpec
    typeifySpec [] = SomeReduceSpec D.RSpecNil D.TEmpty
    typeifySpec (True : rest)
      | SomeReduceSpec res val <- typeifySpec rest = SomeReduceSpec (D.RSpecKeep res) (D.TPush val OnlyInt)
    typeifySpec (False : rest)
      | SomeReduceSpec res val <- typeifySpec rest = SomeReduceSpec (D.RSpecReduce res) (D.TPush val OnlyInt)

    specSameFull :: D.ReduceSpec spec red full
                 -> D.ReduceSpec spec' red' full'
                 -> Maybe (ShapeR full, A.ELeftHandSide full () full, full :~: full')
    specSameFull D.RSpecNil D.RSpecNil = Just (ShapeRz, A.LeftHandSideWildcard TupRunit, Refl)
    specSameFull (D.RSpecReduce s1) (D.RSpecReduce s2)
      | Just (sh, lhs, Refl) <- specSameFull s1 s2 = Just (ShapeRsnoc sh, A.LeftHandSidePair lhs (A.LeftHandSideSingle scalarType), Refl)
    specSameFull (D.RSpecReduce s1) (D.RSpecKeep s2)
      | Just (sh, lhs, Refl) <- specSameFull s1 s2 = Just (ShapeRsnoc sh, A.LeftHandSidePair lhs (A.LeftHandSideSingle scalarType), Refl)
    specSameFull (D.RSpecKeep s1) (D.RSpecReduce s2)
      | Just (sh, lhs, Refl) <- specSameFull s1 s2 = Just (ShapeRsnoc sh, A.LeftHandSidePair lhs (A.LeftHandSideSingle scalarType), Refl)
    specSameFull (D.RSpecKeep s1) (D.RSpecKeep s2)
      | Just (sh, lhs, Refl) <- specSameFull s1 s2 = Just (ShapeRsnoc sh, A.LeftHandSidePair lhs (A.LeftHandSideSingle scalarType), Refl)
    specSameFull _ _ = Nothing

    specSameRed :: D.ReduceSpec spec red full
                -> D.ReduceSpec spec' red' full'
                -> Maybe (red :~: red')
    specSameRed  D.RSpecNil         D.RSpecNil                                         = Just Refl
    specSameRed (D.RSpecKeep s1)   (D.RSpecKeep s2)   | Just Refl <- specSameRed s1 s2 = Just Refl
    specSameRed (D.RSpecReduce s1)  s2                | Just Refl <- specSameRed s1 s2 = Just Refl
    specSameRed  s1                (D.RSpecReduce s2) | Just Refl <- specSameRed s1 s2 = Just Refl
    specSameRed  _                  _                                                  = Nothing

    invertPermutation :: [Int] -> [Int]
    invertPermutation l = map snd (sortBy (comparing fst) (zip l [0..]))

    enforceLocal :: D.TagVal OnlyInt env -> Int -> A.ExpVar env Int
    enforceLocal D.TEmpty i = error $ "enforceLocal: not local (but " ++ show i ++ ")"
    enforceLocal (D.TPush _ OnlyInt) 0 = A.Var scalarType A.ZeroIdx
    enforceLocal (D.TPush env _) n = A.weaken (A.weakenSucc' A.weakenId) (enforceLocal env (pred n))

    tuplify :: D.TagVal OnlyInt env -> [A.ExpVar topenv Int] -> A.ExpVars topenv env
    tuplify D.TEmpty [] = TupRunit
    tuplify (D.TPush env OnlyInt) (var : vars) = TupRpair (tuplify env vars) (TupRsingle var)
    tuplify _ _ = error "tuplify: lists unequal length"
reduceConvert _ = error "impossible GADTs"

-- Builds expression that takes the runtime array size as environment.
multiplyReduced :: D.ReduceSpec spec red sorted -> A.OpenExp sorted aenv (red, Int)
multiplyReduced = \spec -> let (vars, reduced) = goCollectR spec A.weakenId
                           in A.Pair (a_evars vars) (multiplies (map A.Evar reduced))
  where
    goCollectR :: D.ReduceSpec spec red sorted
               -> sorted A.:> sorted'
               -> (A.ExpVars sorted' red, [A.ExpVar sorted' Int])
    goCollectR (D.RSpecReduce spec) w =
        let var = A.Var scalarType (w A.>:> A.ZeroIdx)
        in (var :) <$> goCollectR spec (A.weakenSucc w)
    goCollectR spec w = (goCollectK spec w, [])

    goCollectK :: D.ReduceSpec spec red sorted
               -> sorted A.:> sorted'
               -> A.ExpVars sorted' red
    goCollectK (D.RSpecKeep spec) w =
        TupRpair (goCollectK spec (A.weakenSucc w))
                 (TupRsingle (A.Var scalarType (w A.>:> A.ZeroIdx)))
    goCollectK D.RSpecNil _ = TupRunit
    goCollectK _ _ = error "multiplyReduced: Specification not sorted!"

    multiply :: NumType t -> A.OpenExp env aenv t -> A.OpenExp env aenv t -> A.OpenExp env aenv t
    multiply ty a b = A.PrimApp (A.PrimMul ty) (A.Pair a b)

    multiplies :: [A.OpenExp env aenv Int] -> A.OpenExp env aenv Int
    multiplies [] = A.Const scalarType 0
    multiplies l = foldl1 (multiply numType) l

a_evars :: A.ExpVars env t -> A.OpenExp env aenv t
a_evars TupRunit = A.Nil
a_evars (TupRsingle var) = A.Evar var
a_evars (TupRpair vars1 vars2) = A.Pair (a_evars vars1) (a_evars vars2)

a_avars :: A.ArrayVars aenv t -> A.OpenAcc aenv t
a_avars TupRunit = A.OpenAcc A.Anil
a_avars (TupRsingle var@(A.Var ArrayR{} _)) = A.OpenAcc (A.Avar var)
a_avars (TupRpair vars1 vars2) = A.OpenAcc (A.Apair (a_avars vars1) (a_avars vars2))

euntranslateGet :: TypeR t -> D.TupleIdx t t' -> D.LetBoundVars ScalarType env t t'
euntranslateGet ty D.TIHere = D.lhsCopy ty
euntranslateGet (TupRpair t1 t2) (D.TILeft path)
  | D.LetBoundVars lhs1 vars1 <- euntranslateGet t1 path
  = D.LetBoundVars (A.LeftHandSidePair lhs1 (A.LeftHandSideWildcard t2)) vars1
euntranslateGet (TupRpair t1 t2) (D.TIRight path)
  | D.LetBoundVars lhs2 vars2 <- euntranslateGet t2 path
  = D.LetBoundVars (A.LeftHandSidePair (A.LeftHandSideWildcard t1) lhs2) vars2
euntranslateGet _ _ = error "euntranslateGet: impossible GADTs"

auntranslateGet :: ArraysR t -> D.TupleIdx t s -> D.LetBoundVars ArrayR aenv t s
auntranslateGet ty D.TIHere = D.lhsCopy ty
auntranslateGet (TupRpair t1 t2) (D.TILeft path)
  | D.LetBoundVars lhs1 ex1 <- auntranslateGet t1 path
  = D.LetBoundVars (A.LeftHandSidePair lhs1 (A.LeftHandSideWildcard t2)) ex1
auntranslateGet (TupRpair t1 t2) (D.TIRight path)
  | D.LetBoundVars lhs2 ex2 <- auntranslateGet t2 path
  = D.LetBoundVars (A.LeftHandSidePair (A.LeftHandSideWildcard t1) lhs2) ex2
auntranslateGet _ _ = error "auntranslateGet: impossible GADTs"

curryAfun :: A.OpenAfun aenv ((((), t1), t2) -> t3) -> A.OpenAfun aenv (t1 -> t2 -> t3)
curryAfun (A.Alam (A.LeftHandSidePair (A.LeftHandSidePair (A.LeftHandSideWildcard _) lhs1) lhs2) fun) = A.Alam lhs1 (A.Alam lhs2 fun)
curryAfun (A.Alam (A.LeftHandSidePair (A.LeftHandSideWildcard (TupRpair _ t1)) lhs2) fun) = A.Alam (A.LeftHandSideWildcard t1) (A.Alam lhs2 fun)
curryAfun (A.Alam (A.LeftHandSideWildcard (TupRpair (TupRpair _ t1) t2)) fun) = A.Alam (A.LeftHandSideWildcard t1) (A.Alam (A.LeftHandSideWildcard t2) fun)
curryAfun _ = error "Impossible GADTs"

uncurryAfun :: A.OpenAfun aenv (t1 -> t2 -> t3) -> A.OpenAfun aenv ((((), t1), t2) -> t3)
uncurryAfun (A.Alam lhs1 (A.Alam lhs2 fun)) = A.Alam (A.LeftHandSidePair (A.LeftHandSidePair A.LeftHandSideUnit lhs1) lhs2) fun
uncurryAfun _ = error "Impossible GADTs"

curryFun :: A.OpenFun env aenv ((((), t1), t2) -> t3) -> A.OpenFun env aenv (t1 -> t2 -> t3)
curryFun (A.Lam (A.LeftHandSidePair (A.LeftHandSidePair (A.LeftHandSideWildcard _) lhs1) lhs2) fun) = A.Lam lhs1 (A.Lam lhs2 fun)
curryFun (A.Lam (A.LeftHandSidePair (A.LeftHandSideWildcard (TupRpair _ t1)) lhs2) fun) = A.Lam (A.LeftHandSideWildcard t1) (A.Lam lhs2 fun)
curryFun (A.Lam (A.LeftHandSideWildcard (TupRpair (TupRpair _ t1) t2)) fun) = A.Lam (A.LeftHandSideWildcard t1) (A.Lam (A.LeftHandSideWildcard t2) fun)
curryFun _ = error "Impossible GADTs"

uncurryFun :: A.OpenFun env aenv (t1 -> t2 -> t3) -> A.OpenFun env aenv ((((), t1), t2) -> t3)
uncurryFun (A.Lam lhs1 (A.Lam lhs2 fun)) = A.Lam (A.LeftHandSidePair (A.LeftHandSidePair A.LeftHandSideUnit lhs1) lhs2) fun
uncurryFun _ = error "Impossible GADTs"
