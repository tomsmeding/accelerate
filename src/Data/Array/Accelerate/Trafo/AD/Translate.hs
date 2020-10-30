{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.Translate (
    translateAcc, translateExp, translateFun,
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
import Data.Array.Accelerate.Trafo.AD.Common (PartialVal(..), pvalPushLHS)
import qualified Data.Array.Accelerate.Trafo.AD.Exp as D


translateAcc :: A.OpenAcc aenv t -> D.OpenAcc aenv lab alab args t
translateAcc (A.OpenAcc expr) = case expr of
    A.Use ty arr -> D.Aconst ty arr
    A.Apair e1 e2 ->
        D.Apair (A.arraysR expr) (translateAcc e1) (translateAcc e2)
    A.Anil -> D.Anil
    A.Acond c t e ->
        D.Acond (A.arraysR expr) (translateExp c) (translateAcc t) (translateAcc e)
    A.Map _ f e -> D.Map (A.arrayR expr) (D.ELPlain $ translateFun f) (translateAcc e)
    A.ZipWith _ f e1 e2 ->
        D.ZipWith (A.arrayR expr) (D.ELPlain $ toPairedBinop $ translateFun f) (translateAcc e1) (translateAcc e2)
    A.Fold (A.Lam (A.LeftHandSideSingle t) (A.Lam (A.LeftHandSideSingle _)
              (A.Body (A.PrimApp (A.PrimAdd _)
                                 (A.Pair (A.Evar (A.Var _ (A.SuccIdx A.ZeroIdx)))
                                         (A.Evar (A.Var _ A.ZeroIdx)))))))
           initval e
      | Just (A.Const _ x) <- initval, isZeroConstant t x ->
          D.Sum (A.arrayR expr) (translateAcc e)
      | Nothing <- initval ->
          D.Sum (A.arrayR expr) (translateAcc e)
    A.Fold f me0 e ->
        D.Fold (A.arrayR expr) (toPairedBinop $ translateFun f) (translateExp <$> me0) (translateAcc e)
    A.Scan dir f me0 e ->
        D.Scan (A.arrayR expr) dir (toPairedBinop $ translateFun f) (translateExp <$> me0) (translateAcc e)
    A.Scan' dir f e0 e ->
        D.Scan' (A.arraysR expr) dir (toPairedBinop $ translateFun f) (translateExp e0) (translateAcc e)
    A.Generate ty she f ->
        D.Generate ty (translateExp she) (D.ELPlain $ translateFun f)
    A.Replicate slt sle e ->
        D.Replicate (A.arrayR expr) slt (translateExp sle) (translateAcc e)
    A.Slice slt e sle ->
        D.Slice (A.arrayR expr) slt (translateAcc e) (translateExp sle)
    A.Reshape _ sle e ->
        D.Reshape (A.arrayR expr) (translateExp sle) (translateAcc e)
    A.Backpermute shr dim f e ->
        D.Backpermute (ArrayR shr (arrayRtype (A.arrayR e))) (translateExp dim) (translateFun f) (translateAcc e)
    A.Alet lhs def body -> D.Alet lhs (translateAcc def) (translateAcc body)
    A.Avar var -> D.Avar var
    _ -> internalError ("AD.translateAcc: Cannot perform AD on Acc node <" ++ A.showPreAccOp expr ++ ">")
  where
    toPairedBinop :: D.OpenFun env aenv lab alab tenv (t1 -> t2 -> t3) -> D.OpenFun env aenv lab alab tenv ((t1, t2) -> t3)
    toPairedBinop (D.Lam lhs1 (D.Lam lhs2 (D.Body ex))) = D.Lam (A.LeftHandSidePair lhs1 lhs2) (D.Body ex)
    toPairedBinop _ = error "Impossible GADTs"

    isZeroConstant :: ScalarType t -> t -> Bool
    isZeroConstant (SingleScalarType (NumSingleType (FloatingNumType TypeFloat))) 0 = True
    isZeroConstant _ _ = False

translateFun :: A.OpenFun env aenv t -> D.OpenFun env aenv lab alab env t
translateFun = translateFunInPVal PTEmpty

translateFunInPVal :: PartialVal ScalarType tenv env -> A.OpenFun env aenv t -> D.OpenFun env aenv lab alab tenv t
translateFunInPVal pv (A.Lam lhs fun) = D.Lam lhs (translateFunInPVal (pvalPushLHS lhs pv) fun)
translateFunInPVal pv (A.Body e) = D.Body (translateExpInPVal pv e)

translateExp :: A.OpenExp env aenv t -> D.OpenExp env aenv lab alab args tenv t
translateExp expr = case expr of
    A.Const ty con -> D.Const ty con
    A.PrimApp f e -> D.PrimApp (A.expType expr) f (translateExp e)
    A.Evar (A.Var rep idx) -> D.Var (A.Var rep idx)
    A.Let lhs def body -> D.Let lhs (translateExp def) (translateExp body)
    A.Nil -> D.Nil
    A.Cond c t e -> D.Cond (A.expType t) (translateExp c) (translateExp t) (translateExp e)
    A.Pair e1 e2 -> D.Pair (A.expType expr) (translateExp e1) (translateExp e2)
    A.Shape var -> D.Shape (Left var)
    A.Index var e -> D.Index (Left var) (translateExp e)
    A.ShapeSize sht e -> D.ShapeSize sht (translateExp e)
    _ -> internalError ("AD.translateExp: Cannot perform AD on Exp node <" ++ A.showExpOp expr ++ ">")

translateExpInPVal :: PartialVal ScalarType tenv env -> A.OpenExp env aenv t -> D.OpenExp env aenv lab alab args tenv t
translateExpInPVal pv expr = case expr of
    A.Const ty con -> D.Const ty con
    A.PrimApp f e -> D.PrimApp (A.expType expr) f (translateExpInPVal pv e)
    A.Evar var -> case D.eCheckLocalP matchScalarType var pv of
        Right var' -> D.Var var'
        Left topvar -> D.FreeVar topvar
    A.Let lhs def body -> D.Let lhs (translateExpInPVal pv def) (translateExpInPVal (pvalPushLHS lhs pv) body)
    A.Nil -> D.Nil
    A.Cond c t e -> D.Cond (A.expType t) (translateExpInPVal pv c) (translateExpInPVal pv t) (translateExpInPVal pv e)
    A.Pair e1 e2 -> D.Pair (A.expType expr) (translateExpInPVal pv e1) (translateExpInPVal pv e2)
    A.Shape var -> D.Shape (Left var)
    A.Index var e -> D.Index (Left var) (translateExpInPVal pv e)
    A.ShapeSize sht e -> D.ShapeSize sht (translateExpInPVal pv e)
    _ -> internalError ("AD.translateExp: Cannot perform AD on Exp node <" ++ A.showExpOp expr ++ ">")

data UntranslateResultE a env aenv t =
    forall env'. UntranslateResultE (A.ELeftHandSide a env env') (A.OpenExp env' aenv t)

untranslateLHSboundExp :: A.ELeftHandSide a () env
                       -> D.OpenExp env aenv lab alab args tenv t
                       -> Maybe (tenv A.:> env1)
                       -> UntranslateResultE a env1 aenv t
untranslateLHSboundExp toplhs topexpr topweak
  | A.Exists toplhs' <- A.rebuildLHS toplhs =
      UntranslateResultE toplhs' (go topexpr (fmap (A.weakenWithLHS toplhs' A..>) topweak) (pvalPushLHS toplhs' PTEmpty))
  where
    go :: D.OpenExp env aenv lab alab args tenv t -> Maybe (tenv A.:> env2) -> PartialVal ScalarType topenv env2 -> A.OpenExp env2 aenv t
    go expr w pv = case expr of
        D.Const ty con -> A.Const ty con
        D.PrimApp _ f e -> A.PrimApp f (go e w pv)
        D.Var var -> A.Evar (fromJust (D.eCheckLocalP' matchScalarType var pv))
        D.FreeVar var
          | Just w' <- w -> A.Evar (A.weaken w' var)
          | otherwise -> internalError "AD.untranslateLHSboundExp: Unexpected free variable in presumed-closed expression"
        D.Let lhs def body
          | A.Exists lhs' <- A.rebuildLHS lhs
          -> A.Let lhs' (go def w pv) (go body (fmap (A.weakenWithLHS lhs' A..>) w) (pvalPushLHS lhs' pv))
        D.Nil -> A.Nil
        D.Pair _ e1 e2 -> A.Pair (go e1 w pv) (go e2 w pv)
        D.Cond _ e1 e2 e3 -> A.Cond (go e1 w pv) (go e2 w pv) (go e3 w pv)
        D.Shape (Left avar) -> A.Shape avar
        D.Shape (Right _) -> internalError "AD.untranslateLHSboundExp: Cannot translate label in array var position"
        D.Index (Left avar) e -> A.Index avar (go e w pv)
        D.Index (Right _) _ -> internalError "AD.untranslateLHSboundExp: Cannot translate label in array var position"
        D.ShapeSize sht e -> A.ShapeSize sht (go e w pv)
        D.Get _ path e
          | LetBoundExpE lhs body <- euntranslateGet (D.etypeOf e) path
          -> A.Let lhs (go e w pv) body
        D.Arg _ _ -> internalError "AD.untranslateLHSboundExp: Unexpected Arg in untranslate!"
        D.Label _ -> internalError "AD.untranslateLHSboundExp: Unexpected Label in untranslate!"

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
        D.Const ty con -> A.Const ty con
        D.PrimApp _ f e -> A.PrimApp f (go e pv)
        D.Var var -> A.Evar (fromJust (D.eCheckLocalP' matchScalarType var pv))
        D.FreeVar _ -> internalError "AD.untranslateLHSboundExpA: Unexpected free expression variable in array code"
        D.Let lhs def body
          | A.Exists lhs' <- A.rebuildLHS lhs
          -> A.Let lhs' (go def pv) (go body (pvalPushLHS lhs' pv))
        D.Nil -> A.Nil
        D.Pair _ e1 e2 -> A.Pair (go e1 pv) (go e2 pv)
        D.Cond _ e1 e2 e3 -> A.Cond (go e1 pv) (go e2 pv) (go e3 pv)
        D.Shape (Left avar) -> A.Shape (fromJust (D.eCheckLocalP' matchArrayR avar arrpv))
        D.Shape (Right _) -> internalError "AD.untranslateLHSboundExpA: Cannot translate label (Shape) in array var position"
        D.Index (Left avar) e -> A.Index (fromJust (D.eCheckLocalP' matchArrayR avar arrpv)) (go e pv)
        D.Index (Right _) _ -> internalError "AD.untranslateLHSboundExpA: Cannot translate label (Index) in array var position"
        D.ShapeSize sht e -> A.ShapeSize sht (go e pv)
        D.Get _ path e
          | LetBoundExpE lhs body <- euntranslateGet (D.etypeOf e) path
          -> A.Let lhs (go e pv) body
        D.Arg _ _ -> internalError "AD.untranslateLHSboundExp: Unexpected Arg in untranslate!"
        D.Label _ -> internalError "AD.untranslateLHSboundExp: Unexpected Label in untranslate!"

untranslateClosedExp :: forall lab alab args tenv t aenv. D.OpenExp () aenv lab alab args tenv t -> A.OpenExp () aenv t
untranslateClosedExp expr
  | UntranslateResultE A.LeftHandSideUnit res <-
        untranslateLHSboundExp A.LeftHandSideUnit expr Nothing
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
                       -> D.OpenAcc aenv lab alab args t
                       -> UntranslateResultA a aenv1 t
untranslateLHSboundAcc toplhs topexpr
  | A.Exists toplhs' <- A.rebuildLHS toplhs =
      UntranslateResultA toplhs' (go topexpr (pvalPushLHS toplhs' PTEmpty))
  where
    go :: D.OpenAcc aenv lab args alab t -> PartialVal ArrayR topenv aenv2 -> A.OpenAcc aenv2 t
    go expr pv = A.OpenAcc $ case expr of
        D.Aconst ty con -> A.Use ty con
        D.Avar var -> A.Avar (fromJust (D.eCheckLocalP' matchArrayR var pv))
        D.Alet lhs def body
          | A.Exists lhs' <- A.rebuildLHS lhs
          -> A.Alet lhs' (go def pv) (go body (pvalPushLHS lhs' pv))
        D.Anil -> A.Anil
        D.Apair _ e1 e2 -> A.Apair (go e1 pv) (go e2 pv)
        D.Acond _ e1 e2 e3 -> A.Acond (untranslateClosedExpA e1 pv) (go e2 pv) (go e3 pv)
        D.Map (ArrayR _ ty) (D.ELPlain f) e -> A.Map ty (untranslateClosedFunA f pv) (go e pv)
        D.ZipWith (ArrayR _ ty) (D.ELPlain f) e1 e2 -> A.ZipWith ty (untranslateClosedFunA (fromPairedBinop f) pv) (go e1 pv) (go e2 pv)
        D.Fold _ f me0 e -> A.Fold (untranslateClosedFunA (fromPairedBinop f) pv) (untranslateClosedExpA <$> me0 <*> Just pv) (go e pv)
        D.Scan _ dir f me0 e -> A.Scan dir (untranslateClosedFunA (fromPairedBinop f) pv) (untranslateClosedExpA <$> me0 <*> Just pv) (go e pv)
        D.Scan' _ dir f e0 e -> A.Scan' dir (untranslateClosedFunA (fromPairedBinop f) pv) (untranslateClosedExpA e0 pv) (go e pv)
        D.Sum (ArrayR _ (TupRsingle ty@(SingleScalarType (NumSingleType nt)))) e ->
            A.Fold (A.Lam (A.LeftHandSideSingle ty) (A.Lam (A.LeftHandSideSingle ty)
                      (A.Body (A.PrimApp (A.PrimAdd nt)
                                         (A.Pair (A.Evar (A.Var ty (A.SuccIdx A.ZeroIdx)))
                                                 (A.Evar (A.Var ty A.ZeroIdx)))))))
                   (Just (untranslateClosedExp (D.zeroForType ty)))
                   (go e pv)
        D.Generate ty e (D.ELPlain f) -> A.Generate ty (untranslateClosedExpA e pv) (untranslateClosedFunA f pv)
        D.Replicate _ slt sle e -> A.Replicate slt (untranslateClosedExpA sle pv) (go e pv)
        D.Slice _ slt e sle -> A.Slice slt (go e pv) (untranslateClosedExpA sle pv)
        D.Reduce _ spec combfun e
          | ReduceConvert shtype sortedSpec shlhs fullToSorted sortedToFull <- reduceConvert spec
          , TupRsingle argtype@(ArrayR shtype' _) <- D.atypeOf e
          , Just Refl <- matchShapeR shtype shtype' ->
              A.Alet (A.LeftHandSideSingle argtype) (go e pv)
                     (let shexp = A.Let shlhs (A.Shape (A.Var argtype A.ZeroIdx)) (a_evars fullToSorted)
                          pv' = pvalPushLHS (A.LeftHandSideSingle argtype) pv
                          reshapeExp = A.Let shlhs shexp (multiplyReduced sortedSpec)
                      in A.OpenAcc $ A.Fold (untranslateClosedFunA combfun pv') Nothing $
                             A.OpenAcc $ A.Reshape (ShapeRsnoc (D.rsReducedShapeR spec)) reshapeExp $
                                 A.OpenAcc $ A.Backpermute shtype shexp (A.Lam shlhs (A.Body (a_evars sortedToFull)))
                                                           (A.OpenAcc $ A.Avar (A.Var argtype A.ZeroIdx)))
        D.Reshape (ArrayR sht _) she e -> A.Reshape sht (untranslateClosedExpA she pv) (go e pv)
        D.Backpermute (ArrayR sht _) dim f e -> A.Backpermute sht (untranslateClosedExpA dim pv) (untranslateClosedFunA f pv) (go e pv)
        D.Permute _ cf def pf e -> A.Permute (untranslateClosedFunA cf pv) (go def pv) (untranslateClosedFunA pf pv) (go e pv)
        D.Aget _ path e
          | LetBoundExpA lhs body <- auntranslateGet (D.atypeOf e) path
          -> A.Alet lhs (go e pv) body
        D.Aarg _ _ -> internalError "AD.untranslateLHSboundAcc: Unexpected Arg in untranslate!"
        D.Alabel _ -> internalError "AD.untranslateLHSboundAcc: Unexpected Label in untranslate!"
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

-- TODO: AD.Exp exports a similar type with the same name; however, this one is for the Accelerate AST, not the AD AST. Make that clear in the name.
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
