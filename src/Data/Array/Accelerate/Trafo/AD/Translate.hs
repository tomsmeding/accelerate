{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
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
import Data.Array.Accelerate.Trafo.AD.Common (PartialVal(..), pvalPushLHS)
import qualified Data.Array.Accelerate.Trafo.AD.Exp as D


translateAfun :: A.OpenAfun aenv t -> D.OpenAfun aenv () () aenv t
translateAfun = translateAfunInPVal PTEmpty

translateAfunInPVal :: PartialVal ArrayR taenv aenv -> A.OpenAfun aenv t -> D.OpenAfun aenv () () taenv t
translateAfunInPVal pv (A.Alam lhs fun) = D.Alam lhs (translateAfunInPVal (pvalPushLHS lhs pv) fun)
translateAfunInPVal pv (A.Abody e) =
  let vartrans :: PartialVal ArrayR taenv aenv -> A.ArrayVar aenv t -> D.OpenAcc aenv () () args taenv t
      vartrans pv' var@(A.Var ArrayR{} _) =
        case D.checkLocalP matchArrayR var pv' of
          Right var'@(A.Var _ _) -> D.smartAvar var'
          Left topvar@(A.Var ty _) -> D.AfreeVar (nilLabel ty) topvar
  in D.Abody (translateAccInPVal vartrans pv e)

translateAcc :: A.OpenAcc aenv t -> D.OpenAcc aenv () () args aenv t
translateAcc = translateAccInPVal (\_ var@(A.Var ArrayR{} _) -> D.smartAvar var) PTEmpty

translateAccInPVal :: (forall aenv' t'. PartialVal ArrayR taenv aenv'
                       -> A.ArrayVar aenv' t'
                       -> D.OpenAcc aenv' () () args taenv t')
                   -> PartialVal ArrayR taenv aenv
                   -> A.OpenAcc aenv t
                   -> D.OpenAcc aenv () () args taenv t
translateAccInPVal vt pv (A.OpenAcc expr) = case expr of
    A.Use ty arr -> D.Aconst (nilLabel ty) arr
    A.Apair e1 e2 ->
        D.Apair (nilLabel (A.arraysR expr)) (translateAccInPVal vt pv e1) (translateAccInPVal vt pv e2)
    A.Anil -> D.Anil (nilLabel TupRunit)
    A.Acond c t e ->
        D.Acond (nilLabel (A.arraysR expr)) (translateExp c) (translateAccInPVal vt pv t) (translateAccInPVal vt pv e)
    A.Map _ f e -> D.Map (nilLabel (A.arrayR expr)) (D.ELPlain $ translateFun f) (translateAccInPVal vt pv e)
    A.ZipWith _ f e1 e2 ->
        D.ZipWith (nilLabel (A.arrayR expr)) (D.ELPlain $ toPairedBinop $ translateFun f) (translateAccInPVal vt pv e1) (translateAccInPVal vt pv e2)
    A.Fold (A.Lam (A.LeftHandSideSingle t) (A.Lam (A.LeftHandSideSingle _)
              (A.Body (A.PrimApp (A.PrimAdd _)
                                 (A.Pair (A.Evar (A.Var _ (A.SuccIdx A.ZeroIdx)))
                                         (A.Evar (A.Var _ A.ZeroIdx)))))))
           initval e
      | Just (A.Const _ x) <- initval, isZeroConstant t x ->
          D.Sum (nilLabel (A.arrayR expr)) (translateAccInPVal vt pv e)
      | Nothing <- initval ->
          D.Sum (nilLabel (A.arrayR expr)) (translateAccInPVal vt pv e)
    A.Fold f me0 e ->
        D.Fold (nilLabel (A.arrayR expr)) (toPairedBinop $ translateFun f) (translateExp <$> me0) (translateAccInPVal vt pv e)
    A.Scan dir f me0 e ->
        D.Scan (nilLabel (A.arrayR expr)) dir (toPairedBinop $ translateFun f) (translateExp <$> me0) (translateAccInPVal vt pv e)
    A.Scan' dir f e0 e ->
        D.Scan' (nilLabel (A.arraysR expr)) dir (toPairedBinop $ translateFun f) (translateExp e0) (translateAccInPVal vt pv e)
    A.Generate ty she f ->
        D.Generate (nilLabel ty) (translateExp she) (D.ELPlain $ translateFun f)
    A.Replicate slt sle e ->
        D.Replicate (nilLabel (A.arrayR expr)) slt (translateExp sle) (translateAccInPVal vt pv e)
    A.Slice slt e sle ->
        D.Slice (nilLabel (A.arrayR expr)) slt (translateAccInPVal vt pv e) (translateExp sle)
    A.Reshape _ sle e ->
        D.Reshape (nilLabel (A.arrayR expr)) (translateExp sle) (translateAccInPVal vt pv e)
    A.Backpermute shr dim f e ->
        D.Backpermute (nilLabel (ArrayR shr (arrayRtype (A.arrayR e)))) (translateExp dim) (translateFun f) (translateAccInPVal vt pv e)
    A.Alet lhs def body -> D.Alet lhs (translateAccInPVal vt pv def) (translateAccInPVal vt (pvalPushLHS lhs pv) body)
    A.Avar var -> vt pv var
    _ -> internalError ("AD.translateAccInPVal: Cannot perform AD on Acc node <" ++ A.showPreAccOp expr ++ ">")
  where
    toPairedBinop :: D.OpenFun env aenv lab alab tenv (t1 -> t2 -> t3) -> D.OpenFun env aenv lab alab tenv ((t1, t2) -> t3)
    toPairedBinop (D.Lam lhs1 (D.Lam lhs2 (D.Body ex))) = D.Lam (A.LeftHandSidePair lhs1 lhs2) (D.Body ex)
    toPairedBinop _ = error "Impossible GADTs"

    isZeroConstant :: ScalarType t -> t -> Bool
    isZeroConstant (SingleScalarType (NumSingleType (FloatingNumType TypeFloat))) 0 = True
    isZeroConstant _ _ = False

translateFun :: A.OpenFun env aenv t -> D.OpenFun env aenv () alab env t
translateFun = translateFunInPVal PTEmpty

translateFunInPVal :: PartialVal ScalarType tenv env -> A.OpenFun env aenv t -> D.OpenFun env aenv () alab tenv t
translateFunInPVal pv (A.Lam lhs fun) = D.Lam lhs (translateFunInPVal (pvalPushLHS lhs pv) fun)
translateFunInPVal pv (A.Body e) =
  let vartrans pv' var = case D.checkLocalP matchScalarType var pv' of
                           Right var'@(A.Var _ _) -> D.smartVar var'
                           Left topvar@(A.Var ty _) -> D.FreeVar (nilLabel ty) topvar
  in D.Body (translateExpInPVal vartrans pv e)

translateExp :: A.OpenExp env aenv t -> D.OpenExp env aenv () alab args env t
translateExp = translateExpInPVal (\_ var -> D.smartVar var) PTEmpty

translateExpInPVal :: (forall env' t'. PartialVal ScalarType tenv env'
                       -> A.ExpVar env' t'
                       -> D.OpenExp env' aenv () alab args tenv t')
                   -> PartialVal ScalarType tenv env
                   -> A.OpenExp env aenv t
                   -> D.OpenExp env aenv () alab args tenv t
translateExpInPVal vt pv expr = case expr of
    A.Const ty con -> D.Const (nilLabel ty) con
    A.PrimApp f e -> D.PrimApp (nilLabel (A.expType expr)) f (translateExpInPVal vt pv e)
    A.PrimConst c -> D.PrimConst (nilLabel (SingleScalarType (A.primConstType c))) c
    A.Evar var -> vt pv var
    A.Let lhs def body -> D.Let lhs (translateExpInPVal vt pv def) (translateExpInPVal vt (pvalPushLHS lhs pv) body)
    A.Nil -> D.Nil magicLabel
    A.Cond c t e -> D.Cond (nilLabel (A.expType t)) (translateExpInPVal vt pv c) (translateExpInPVal vt pv t) (translateExpInPVal vt pv e)
    A.Pair e1 e2 -> D.Pair (nilLabel (A.expType expr)) (translateExpInPVal vt pv e1) (translateExpInPVal vt pv e2)
    A.Shape var@(A.Var (ArrayR sht _) _) -> D.Shape (nilLabel (shapeType sht)) (Left var)
    A.Index var@(A.Var (ArrayR _ ty) _) e -> D.Index (nilLabel ty) (Left var) scalarLabel (translateExpInPVal vt pv e)
    A.ShapeSize sht e -> D.ShapeSize scalarLabel sht (translateExpInPVal vt pv e)
    A.Undef ty -> D.Undef (nilLabel ty)
    _ -> internalError ("AD.translateExp: Cannot perform AD on Exp node <" ++ A.showExpOp expr ++ ">")

data UntranslateResultE a env aenv t =
    forall env'. UntranslateResultE (A.ELeftHandSide a env env') (A.OpenExp env' aenv t)

untranslateLHSboundExp :: A.ELeftHandSide a () env
                       -> D.OpenExp env aenv lab alab args tenv t
                       -> tenv A.:> env1
                       -> UntranslateResultE a env1 aenv t
untranslateLHSboundExp toplhs topexpr topweak
  | A.Exists toplhs' <- A.rebuildLHS toplhs =
      UntranslateResultE toplhs' (go topexpr (A.weakenWithLHS toplhs' A..> topweak) (pvalPushLHS toplhs' PTEmpty))
  where
    -- TODO: shuffle arguments so that expr is the last instead of the first
    go :: D.OpenExp env aenv lab alab args tenv t -> tenv A.:> env2 -> PartialVal ScalarType topenv env2 -> A.OpenExp env2 aenv t
    go expr w pv = case expr of
        D.Const lab con -> A.Const (labelType lab) con
        D.PrimApp _ f e -> A.PrimApp f (go e w pv)
        D.PrimConst _ c -> A.PrimConst c
        D.Var _ var _ -> A.Evar (fromJust (D.checkLocalP' matchScalarType var pv))
        D.FreeVar _ var -> A.Evar (A.weaken w var)
        D.Let lhs def body
          | A.Exists lhs' <- A.rebuildLHS lhs
          -> A.Let lhs' (go def w pv) (go body (A.weakenWithLHS lhs' A..> w) (pvalPushLHS lhs' pv))
        D.Nil _ -> A.Nil
        D.Pair _ e1 e2 -> A.Pair (go e1 w pv) (go e2 w pv)
        D.Cond _ e1 e2 e3 -> A.Cond (go e1 w pv) (go e2 w pv) (go e3 w pv)
        D.Shape _ (Left avar) -> A.Shape avar
        D.Shape _ (Right _) -> internalError "AD.untranslateLHSboundExp: Cannot translate label (Shape) in array var position"
        D.Index _ (Left avar) _ e -> A.Index avar (go e w pv)
        D.Index _ (Right _) _ _ -> internalError "AD.untranslateLHSboundExp: Cannot translate label (Index) in array var position"
        D.ShapeSize _ sht e -> A.ShapeSize sht (go e w pv)
        D.Get _ path e
          | D.LetBoundVars lhs vars <- euntranslateGet (D.etypeOf e) path
          -> A.Let lhs (go e w pv) (a_evars vars)
        D.Undef lab -> A.Undef (labelType lab)
        D.Arg _ _ _ -> internalError "AD.untranslateLHSboundExp: Unexpected Arg in untranslate!"

untranslateLHSboundExpA :: forall a env env1 lab alab args tenv t aenv topaenv aenv2.
                           A.ELeftHandSide a () env
                        -> D.OpenExp env aenv lab alab args tenv t
                        -> PartialVal ArrayR topaenv aenv2
                        -> UntranslateResultE a env1 aenv2 t
untranslateLHSboundExpA toplhs topexpr arrpv
  | A.Exists toplhs' <- A.rebuildLHS toplhs =
      UntranslateResultE toplhs' (go topexpr (pvalPushLHS toplhs' PTEmpty))
  where
    go :: D.OpenExp env' aenv lab alab args tenv t' -> PartialVal ScalarType topenv env2 -> A.OpenExp env2 aenv2 t'
    go expr pv = case expr of
        D.Const lab con -> A.Const (labelType lab) con
        D.PrimApp _ f e -> A.PrimApp f (go e pv)
        D.PrimConst _ c -> A.PrimConst c
        D.Var _ var _ -> A.Evar (fromJust (D.checkLocalP' matchScalarType var pv))
        D.FreeVar _ _ -> internalError "AD.untranslateLHSboundExpA: Unexpected free expression variable in array code"
        D.Let lhs def body
          | A.Exists lhs' <- A.rebuildLHS lhs
          -> A.Let lhs' (go def pv) (go body (pvalPushLHS lhs' pv))
        D.Nil _ -> A.Nil
        D.Pair _ e1 e2 -> A.Pair (go e1 pv) (go e2 pv)
        D.Cond _ e1 e2 e3 -> A.Cond (go e1 pv) (go e2 pv) (go e3 pv)
        D.Shape _ (Left avar) -> A.Shape (fromJust (D.checkLocalP' matchArrayR avar arrpv))
        D.Shape _ (Right _) -> internalError "AD.untranslateLHSboundExpA: Cannot translate label (Shape) in array var position"
        D.Index _ (Left avar) _ e -> A.Index (fromJust (D.checkLocalP' matchArrayR avar arrpv)) (go e pv)
        D.Index _ (Right _) _ _ -> internalError "AD.untranslateLHSboundExpA: Cannot translate label (Index) in array var position"
        D.ShapeSize _ sht e -> A.ShapeSize sht (go e pv)
        D.Get _ path e
          | D.LetBoundVars lhs vars <- euntranslateGet (D.etypeOf e) path
          -> A.Let lhs (go e pv) (a_evars vars)
        D.Undef lab -> A.Undef (labelType lab)
        D.Arg _ _ _ -> internalError "AD.untranslateLHSboundExpA: Unexpected Arg in untranslate!"

untranslateClosedExp :: forall lab alab args t aenv. D.OpenExp () aenv lab alab args () t -> A.OpenExp () aenv t
untranslateClosedExp expr
  | UntranslateResultE A.LeftHandSideUnit res <-
        untranslateLHSboundExp A.LeftHandSideUnit expr A.weakenId
            :: UntranslateResultE () () aenv t
  = res
untranslateClosedExp _ = error "unreachable"

untranslateClosedExpA :: forall aenv lab alab args tenv t topaenv aenv2.
                         D.OpenExp () aenv lab alab args tenv t
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

untranslateClosedFunA :: forall lab alab t tenv topaenv aenv aenv2.
                         D.OpenFun () aenv lab alab tenv t
                      -> PartialVal ArrayR topaenv aenv2
                      -> A.OpenFun () aenv2 t
untranslateClosedFunA topfun arrpv
  | UntranslateFunResultE A.LeftHandSideUnit fun' <- go A.LeftHandSideUnit topfun
  = fun'
  where
    go :: A.ELeftHandSide a () env -> D.OpenFun env aenv lab alab tenv t' -> UntranslateFunResultE a () aenv2 t'
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
        D.Avar _ var _ -> A.Avar (fromJust (D.checkLocalP' matchArrayR var pv))
        D.AfreeVar _ var -> A.Avar (A.weaken w var)
        D.Alet lhs def body
          | A.Exists lhs' <- A.rebuildLHS lhs
          -> A.Alet lhs' (go w pv def) (go (A.weakenWithLHS lhs' A..> w) (pvalPushLHS lhs' pv) body)
        D.Anil _ -> A.Anil
        D.Apair _ e1 e2 -> A.Apair (go w pv e1) (go w pv e2)
        D.Acond _ e1 e2 e3 -> A.Acond (untranslateClosedExpA e1 pv) (go w pv e2) (go w pv e3)
        D.Map (labelType -> ArrayR _ ty) (D.ELPlain f) e -> A.Map ty (untranslateClosedFunA f pv) (go w pv e)
        D.ZipWith (labelType -> ArrayR _ ty) (D.ELPlain f) e1 e2 -> A.ZipWith ty (untranslateClosedFunA (fromPairedBinop f) pv) (go w pv e1) (go w pv e2)
        D.Fold _ f me0 e -> A.Fold (untranslateClosedFunA (fromPairedBinop f) pv) (untranslateClosedExpA <$> me0 <*> Just pv) (go w pv e)
        D.Scan _ dir f me0 e -> A.Scan dir (untranslateClosedFunA (fromPairedBinop f) pv) (untranslateClosedExpA <$> me0 <*> Just pv) (go w pv e)
        D.Scan' _ dir f e0 e -> A.Scan' dir (untranslateClosedFunA (fromPairedBinop f) pv) (untranslateClosedExpA e0 pv) (go w pv e)
        D.Sum (labelType -> ArrayR _ (TupRsingle ty@(SingleScalarType (NumSingleType nt)))) e ->
            A.Fold (A.Lam (A.LeftHandSideSingle ty) (A.Lam (A.LeftHandSideSingle ty)
                      (A.Body (A.PrimApp (A.PrimAdd nt)
                                         (A.Pair (A.Evar (A.Var ty (A.SuccIdx A.ZeroIdx)))
                                                 (A.Evar (A.Var ty A.ZeroIdx)))))))
                   (Just (untranslateClosedExp (D.zeroForType ty)))
                   (go w pv e)
        D.Generate (labelType -> ty) e (D.ELPlain f) -> A.Generate ty (untranslateClosedExpA e pv) (untranslateClosedFunA f pv)
        D.Replicate _ slt sle e -> A.Replicate slt (untranslateClosedExpA sle pv) (go w pv e)
        D.Slice _ slt e sle -> A.Slice slt (go w pv e) (untranslateClosedExpA sle pv)
        D.Reduce _ spec combfun e
          | ReduceConvert shtype sortedSpec shlhs fullToSorted sortedToFull <- reduceConvert spec
          , TupRsingle argtype@(ArrayR shtype' _) <- D.atypeOf e
          , Just Refl <- matchShapeR shtype shtype' ->
              A.Alet (A.LeftHandSideSingle argtype) (go w pv e)
                     (let shexp = A.Let shlhs (A.Shape (A.Var argtype A.ZeroIdx)) (a_evars fullToSorted)
                          pv' = pvalPushLHS (A.LeftHandSideSingle argtype) pv
                          reshapeExp = A.Let shlhs shexp (multiplyReduced sortedSpec)
                      in A.OpenAcc $ A.Fold (untranslateClosedFunA combfun pv') Nothing $
                             A.OpenAcc $ A.Reshape (ShapeRsnoc (D.rsReducedShapeR spec)) reshapeExp $
                                 A.OpenAcc $ A.Backpermute shtype shexp (A.Lam shlhs (A.Body (a_evars sortedToFull)))
                                                           (A.OpenAcc $ A.Avar (A.Var argtype A.ZeroIdx)))
        D.Reshape (labelType -> ArrayR sht _) she e -> A.Reshape sht (untranslateClosedExpA she pv) (go w pv e)
        D.Backpermute (labelType -> ArrayR sht _) dim f e -> A.Backpermute sht (untranslateClosedExpA dim pv) (untranslateClosedFunA f pv) (go w pv e)
        D.Permute _ cf def pf e -> A.Permute (untranslateClosedFunA cf pv) (go w pv def) (untranslateClosedFunA pf pv) (go w pv e)
        D.Aget _ path e
          | D.LetBoundVars lhs vars <- auntranslateGet (D.atypeOf e) path
          -> A.Alet lhs (go w pv e) (a_avars vars)
        D.Aarg _ _ _ -> internalError "AD.untranslateLHSboundAcc: Unexpected Arg in untranslate!"
        D.Map _ _ _ -> error "Unexpected Map shape in untranslate"
        D.ZipWith _ _ _ _ -> error "Unexpected ZipWith shape in untranslate"
        D.Sum _ _ -> error "Unexpected Sum shape in untranslate"
        D.Generate _ _ _ -> error "Unexpected Generate shape in untranslate"
        D.Reduce _ _ _ _ -> error "Unexpected Reduce shape in untranslate"

    fromPairedBinop :: D.OpenFun env aenv lab alab tenv ((t1, t2) -> t3) -> D.OpenFun env aenv lab alab tenv (t1 -> t2 -> t3)
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
