{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Accelerate.Trafo.AD.Simplify (
  simplifyAcc, simplifyExp
) where

import Control.Arrow (second)
import Data.Some

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.LeftHandSide (LeftHandSide(..), Exists(..), lhsToTupR)
import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.Analysis.Match ((:~:)(Refl), matchArrayR, matchScalarType)
import qualified Data.Array.Accelerate.Analysis.Match as A (matchOpenExp)
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.Substitution (rebuildLHS, weaken)
import Data.Array.Accelerate.Trafo.AD.Acc
import Data.Array.Accelerate.Trafo.AD.Additive
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Debug
import Data.Array.Accelerate.Trafo.AD.Pretty
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.Sink


-- TODO: This Simplify module is quadratic in the program size.


simplifyAcc :: OpenAcc aenv () () args taenv t -> OpenAcc aenv () () args taenv t
simplifyAcc a = let res = snd (goAcc a SNil)
                in trace ("simplify input:\n" ++ prettyPrint a) $ trace ("simplify result:\n" ++ prettyPrint res) res
-- simplifyAcc = snd . flip goAcc SNil
-- simplifyAcc = id

simplifyExp :: Show alab => OpenExp env aenv () alab args tenv taenv t -> OpenExp env aenv () alab args tenv taenv t
simplifyExp a = let res = snd (goExp a (SNil, SNil))
                in trace ("simplify input:\n" ++ prettyPrint a) $ trace ("simplify result:\n" ++ prettyPrint res) res
-- simplifyExp = snd . flip goExp (SNil, SNil)
-- simplifyExp = id

goAcc :: OpenAcc aenv () () args taenv t -> Stats aenv -> (Stats aenv, OpenAcc aenv () () args taenv t)
goAcc = \case
    -- Let rotation
    Alet lhs1 (Alet lhs2 rhs2 bd2) bd1
      | Exists lhs1' <- rebuildLHS lhs1 ->
          goAcc $ Alet lhs2 rhs2 $ Alet lhs1' bd2 $ sinkAcc (sinkWithLHS lhs1 lhs1' (weakenWithLHS lhs2)) bd1

    -- Let split
    Alet (LeftHandSidePair lhs1 lhs2) (Apair _ a1 a2) bd
      | Exists lhs2' <- rebuildLHS lhs2 ->
          goAcc $ Alet lhs1 a1 $ Alet lhs2' (sinkAcc (weakenWithLHS lhs1) a2) (sinkAcc (sinkWithLHS lhs2 lhs2' weakenId) bd)

    -- Redundant wildcard binding elimination
    Alet (LeftHandSideWildcard _) _ a ->
        goAcc a

    -- Linear inlining, and inlining of duplicable programs.
    -- Variable references may always be inlined; non-variable but nevertheless
    -- duplicable programs may be inlined if they are never used in an
    -- expression. Other programs may only be inlined if they are used at most
    -- once, outside an expression.
    Alet lhs@(LeftHandSideSingle ty) a1 a2 ->
      \s -> let (s1, a1') = goAcc a1 s
                (SPush s2 n, a2') = goAcc a2 (SPush s1 (Finite 0))
                isAvar :: OpenAcc aenv lab alab args taenv t -> Bool
                isAvar Avar{} = True
                isAvar _ = False
            in if isAvar a1' || n <= Finite 1 || (n < AccInExp && duplicableAcc a1')
                   then -- Note that we need to re-simplify again using s1, because we need to
                        -- get the actual counts from _after_ the inlining we've done here.
                        goAcc (inlineA (InlinerA (\case A.Var ty' ZeroIdx
                                                          | Just Refl <- matchArrayR ty ty' -> a1'
                                                          | otherwise -> error "Invalid GADTs"
                                                        A.Var ty'@ArrayR{} (SuccIdx idx)
                                                          -> smartAvar (A.Var ty' idx)))
                                       a2')
                              s1
                   else (s2, Alet lhs a1' a2')

    -- Pruning of wildcard bindings
    Alet lhs rhs e
      | lhsHasWildcard lhs
      , PrunedLHS lhs' rj <- pruneLHS lhs ->
          goAcc $ Alet lhs' (reprojectA rj rhs) e

    Aconst lab x -> returnS $ Aconst lab x
    Apair lab a1 a2 -> Apair lab !$! goAcc a1 !**! goAcc a2
    Anil lab -> returnS (Anil lab)
    Acond lab e a1 a2 -> Acond lab !$! goExp' e !**! goAcc a1 !**! goAcc a2
    Map lab lam a -> Map lab !$! simplifyLam1 lam !**! goAcc a
    ZipWith lab lam a1 a2 -> ZipWith lab !$! simplifyLam1 lam !**! goAcc a1 !**! goAcc a2
    Generate lab e lam -> Generate lab !$! goExp' e !**! simplifyLam1 lam
    Fold lab f me0 a -> Fold lab !$! simplifyFun f
                                 !**! (case me0 of Just e0 -> Just !$! goExp' e0
                                                   Nothing -> returnS Nothing)
                                 !**! goAcc a
    Scan lab dir f me0 a -> Scan lab dir !$! simplifyFun f
                                         !**! (case me0 of Just e0 -> Just !$! goExp' e0
                                                           Nothing -> returnS Nothing)
                                         !**! goAcc a
    Scan' lab dir f e0 a -> Scan' lab dir !$! simplifyFun f !**! goExp' e0 !**! goAcc a
    Sum lab a -> Sum lab !$! goAcc a
    Replicate lab slt she a -> Replicate lab slt !$! goExp' she !**! goAcc a
    Slice lab slt a she -> Slice lab slt !$! goAcc a !**! goExp' she
    Reduce lab spec f a -> Reduce lab spec !$! simplifyFun f !**! goAcc a
    Reshape lab she a -> Reshape lab !$! goExp' she !**! goAcc a
    Backpermute lab she f a -> Backpermute lab !$! goExp' she !**! simplifyFun f !**! goAcc a
    Permute lab f a1 pf a2 -> Permute lab !$! simplifyFun f !**! goAcc a1 !**! simplifyFun pf !**! goAcc a2
    Aget lab tidx a -> Aget lab tidx !$! goAcc a
    Aarg lab argsty tidx -> returnS $ Aarg lab argsty tidx
    Alet lhs a1 a2 ->
      \s -> let (s1, a1') = goAcc a1 s
                (s2, a2') = goAcc a2 (spushLHS0 s1 lhs)
            in case spopLHS' lhs s2 of
                 (s', Some lhs')
                   | PrunedLHS lhs'' rj <- pruneLHS lhs'
                   -> (s', Alet lhs'' (reprojectA rj a1') (sinkAcc (sinkWithLHSAllowDrop lhs lhs' weakenId) a2'))
    Avar lab var referLab ->
      \s -> (statAddV var (Finite 1) s, Avar lab var referLab)
    AfreeVar lab var -> returnS $ AfreeVar lab var

goExp' :: OpenExp env aenv () alab args tenv taenv t -> Stats aenv -> (Stats aenv, OpenExp env aenv () alab args tenv taenv t)
goExp' e s = let ((s', SNil), e') = goExp e (s, SNil) in (s', e')

goExp :: OpenExp env aenv () alab args tenv taenv t -> (Stats aenv, Stats env) -> ((Stats aenv, Stats env), OpenExp env aenv () alab args tenv taenv t)
goExp = \case
    -- Let rotation
    Let lhs1 (Let lhs2 rhs2 bd2) bd1
      | Exists lhs1' <- rebuildLHS lhs1 ->
          goExp $ Let lhs2 rhs2 $ Let lhs1' bd2 $ sinkExp (sinkWithLHS lhs1 lhs1' (weakenWithLHS lhs2)) bd1

    -- Let split
    Let (LeftHandSidePair lhs1 lhs2) (Pair _ a1 a2) bd
      | Exists lhs2' <- rebuildLHS lhs2 ->
          goExp $ Let lhs1 a1 $ Let lhs2' (sinkExp (weakenWithLHS lhs1) a2) (sinkExp (sinkWithLHS lhs2 lhs2' weakenId) bd)

    -- Redundant wildcard binding elimination
    Let (LeftHandSideWildcard _) _ e ->
        goExp e

    -- Trivial expression inlining
    Let (LeftHandSideSingle ty) rhs e
      | duplicableExp rhs ->
          goExp $
              inlineE (InlinerE (\case A.Var ty' ZeroIdx
                                         | Just Refl <- matchScalarType ty ty' -> rhs
                                         | otherwise -> error "Invalid GADTs"
                                       A.Var ty' (SuccIdx idx)
                                         -> smartVar (A.Var ty' idx)))
                      e

    -- Linear inlining
    Let lhs@(LeftHandSideSingle ty) rhs e ->
      \s -> let ((s1a, s1e), rhs') = goExp rhs s
                ((s2a, SPush s2e n), e') = goExp e (s1a, SPush s1e (Finite 0))
            in ((s2a, s2e),
                if n <= Finite 1
                    then inlineE (InlinerE (\case A.Var ty' ZeroIdx
                                                    | Just Refl <- matchScalarType ty ty' -> rhs'
                                                    | otherwise -> error "Invalid GADTs"
                                                  A.Var ty' (SuccIdx idx)
                                                    -> smartVar (A.Var ty' idx)))
                                 e'
                    else Let lhs rhs' e')

    -- Pruning of wildcard bindings
    -- Let lhs rhs e
    --   | lhsHasWildcard lhs
    --   , PrunedLHS lhs' rj <- pruneLHS lhs ->
    --       goExp $ Let lhs' (reprojectE rj rhs) e

    -- Get elimination
    Get lab ti e ->
      \s -> case (ti, goExp e s) of
              (TILeft ti', (s', Pair _ e1 _)) -> (s', elimEmptyTI lab ti' e1)
              (TIRight ti', (s', Pair _ _ e2)) -> (s', elimEmptyTI lab ti' e2)
              (_, (s', e')) -> (s', Get lab ti e')
      where
        elimEmptyTI :: EDLabelN lab t' -> TupleIdx t t' -> OpenExp env aenv lab alab args tenv taenv t -> OpenExp env aenv lab alab args tenv taenv t'
        elimEmptyTI _ TIHere e' = e'
        elimEmptyTI ty' ti' e' = Get ty' ti' e'

    -- Algebraic simplifications
    -- TODO: the returned stats are from _before_ the algebraic simplification, if any. This means we overcount, which may be suboptimal but should never be unsound.
    PrimApp lab (A.PrimMul nty) (Pair pairty e1 e2) ->
      \s -> case ((,) !$! goExp e1 !**! goExp e2) s of
              (s', (e1', e2'))
                | isNumConstant 0 e1' || isNumConstant 0 e2' -> (s', zeroForType nty)
                | isNumConstant 1 e1' -> (s', e2')
                | isNumConstant 1 e2' -> (s', e1')
                | otherwise -> (s', PrimApp lab (A.PrimMul nty) (Pair pairty e1' e2'))
    PrimApp lab (A.PrimAdd nty) (Pair pairty e1 e2) ->
      \s -> case ((,) !$! goExp e1 !**! goExp e2) s of
              (s', (e1', e2'))
                | isNumConstant 0 e1' -> (s', e2')
                | isNumConstant 0 e2' -> (s', e1')
                | otherwise -> (s', PrimApp lab (A.PrimAdd nty) (Pair pairty e1' e2'))

    Const lab x -> returnS $ Const lab x
    PrimApp lab op e -> PrimApp lab op !$! goExp e
    PrimConst lab c -> returnS $ PrimConst lab c
    Pair lab e1 e2 -> Pair lab !$! goExp e1 !**! goExp e2
    Nil lab -> returnS (Nil lab)
    Cond lab e1 e2 e3 -> Cond lab !$! goExp e1 !**! goExp e2 !**! goExp e3
    Shape lab ref -> Shape lab !$! goArrayRef ref
    Index lab ref execLab e -> Index lab !$! goArrayRef ref !**! returnS execLab !**! goExp e
    ShapeSize lab sht e -> ShapeSize lab sht !$! goExp e
    Undef ty -> returnS $ Undef ty  -- TODO: undef poisons, and can be propagated; however we currently don't generate code where that would help.
    Let lhs rhs e ->
      \s -> let ((s1a, s1e), rhs') = goExp rhs s
                ((s2a, s2e), e') = goExp e (s1a, spushLHS0 s1e lhs)
            in case spopLHS' lhs s2e of
                 (s', Some lhs')
                   | PrunedLHS lhs'' rj <- pruneLHS lhs'
                   -> ((s2a, s'), Let lhs'' (reprojectE rj rhs') (sinkExp (sinkWithLHSAllowDrop lhs lhs' weakenId) e'))
    Arg lab argsty tidx -> returnS $ Arg lab argsty tidx
    Var lab var referLab -> \s -> (second (statAddV var (Finite 1)) s, Var lab var referLab)
    FreeVar lab var -> returnS $ FreeVar lab var
  where
    isNumConstant :: (forall a. Num a => a) -> OpenExp env aenv lab alab args tenv taenv t -> Bool
    isNumConstant cnst (Const (DLabel { labelType = ty }) val)
      | Const _ val' <- zeroForType' cnst ty
      , Just Refl <- A.matchOpenExp (A.Const ty val) (A.Const ty val')
      = True
    isNumConstant _ _ = False

goArrayRef :: ArrayRef aenv taenv alab t -> (Stats aenv, Stats env) -> ((Stats aenv, Stats env), ArrayRef aenv taenv alab t)
goArrayRef (ARVar var) (sa, se) = ((statAddV var AccInExp sa, se), ARVar var)
goArrayRef (ARFree var) s = (s, ARFree var)
goArrayRef (ARLab lab) s = (s, ARLab lab)

simplifyFun :: OpenFun env aenv () alab tenv taenv t -> Stats aenv -> (Stats aenv, OpenFun env aenv () alab tenv taenv t)
simplifyFun (Lam lhs fun) = Lam lhs !$! simplifyFun fun
simplifyFun (Body ex) = Body !$! goExp' ex

simplifyLam1 :: ExpLambda1 aenv () alab tenv taenv sh t1 t2 -> Stats aenv -> (Stats aenv, ExpLambda1 aenv () alab tenv taenv sh t1 t2)
simplifyLam1 (ELSplit lam lab) = returnS (ELSplit lam lab)
simplifyLam1 (ELPlain fun) = \s -> ELPlain <$> simplifyFun fun s

duplicableAcc :: OpenAcc aenv lab alab args taenv t -> Bool
duplicableAcc Avar{} = True
duplicableAcc (Replicate _ _ _ a) = duplicableAcc a
duplicableAcc _ = False

duplicableExp :: OpenExp env aenv lab alab args tenv taenv t -> Bool
duplicableExp (Var _ _ _) = True
duplicableExp (Const _ _) = True
duplicableExp (PrimConst _ _) = True  -- TODO: depending on the backend this might not be true?
duplicableExp _ = False

data InlinerA aenv aenv' lab alab args taenv =
    InlinerA { unInlinerA :: forall t. A.ArrayVar aenv t -> OpenAcc aenv' lab alab args taenv t }

sinkInlinerASucc :: InlinerA aenv aenv' lab () args taenv -> InlinerA (aenv, a) (aenv', a) lab () args taenv
sinkInlinerASucc (InlinerA f) =
    InlinerA (\case A.Var ty@ArrayR{} ZeroIdx -> smartAvar (A.Var ty ZeroIdx)
                    A.Var ty (SuccIdx idx) -> sinkAcc (weakenSucc' weakenId) (f (A.Var ty idx)))

sinkInlinerALHS :: A.ALeftHandSide t aenv aenv2 -> A.ALeftHandSide t aenv' aenv2' -> InlinerA aenv aenv' lab () args taenv -> InlinerA aenv2 aenv2' lab () args taenv
sinkInlinerALHS (LeftHandSideWildcard _) (LeftHandSideWildcard _) = id
sinkInlinerALHS (LeftHandSideSingle _) (LeftHandSideSingle _) = sinkInlinerASucc
sinkInlinerALHS (LeftHandSidePair lhs1 lhs2) (LeftHandSidePair lhs1' lhs2') = sinkInlinerALHS lhs2 lhs2' . sinkInlinerALHS lhs1 lhs1'
sinkInlinerALHS _ _ = error "sinkInlinerALHS: Unequal LHS's"

inlineA :: InlinerA aenv aenv' lab () args taenv -> OpenAcc aenv lab () args taenv t -> OpenAcc aenv' lab () args taenv t
inlineA f = \case
    Aconst lab x -> Aconst lab x
    Apair lab a1 a2 -> Apair lab (inlineA f a1) (inlineA f a2)
    Anil lab -> Anil lab
    Acond lab e a1 a2 -> Acond lab (inlineAE f e) (inlineA f a1) (inlineA f a2)
    Map lab lam a -> Map lab (inlineALam f lam) (inlineA f a)
    ZipWith lab lam a1 a2 -> ZipWith lab (inlineALam f lam) (inlineA f a1) (inlineA f a2)
    Generate lab e lam -> Generate lab (inlineAE f e) (inlineALam f lam)
    Fold lab fun me0 a -> Fold lab (inlineAEF f fun) (inlineAE f <$> me0) (inlineA f a)
    Scan lab dir fun me0 a -> Scan lab dir (inlineAEF f fun) (inlineAE f <$> me0) (inlineA f a)
    Scan' lab dir fun e0 a -> Scan' lab dir (inlineAEF f fun) (inlineAE f e0) (inlineA f a)
    Sum lab a -> Sum lab (inlineA f a)
    Replicate lab slt she a -> Replicate lab slt (inlineAE f she) (inlineA f a)
    Slice lab slt a she -> Slice lab slt (inlineA f a) (inlineAE f she)
    Reduce lab spec f' a -> Reduce lab spec (inlineAEF f f') (inlineA f a)
    Reshape lab she a -> Reshape lab (inlineAE f she) (inlineA f a)
    Backpermute lab she f' a -> Backpermute lab (inlineAE f she) (inlineAEF f f') (inlineA f a)
    Permute lab f' a1 pf a2 -> Permute lab (inlineAEF f f') (inlineA f a1) (inlineAEF f pf) (inlineA f a2)
    Aget lab tidx a -> Aget lab tidx (inlineA f a)
    Aarg lab argsty tidx -> Aarg lab argsty tidx
    Alet lhs a1 a2
      | Exists lhs2 <- rebuildLHS lhs
      -> Alet lhs2 (inlineA f a1) (inlineA (sinkInlinerALHS lhs lhs2 f) a2)
    Avar _ var _ -> unInlinerA f var
    AfreeVar lab var -> AfreeVar lab var

inlineAE :: InlinerA aenv aenv' lab alab aargs taenv -> OpenExp env aenv lab alab args tenv taenv t -> OpenExp env aenv' lab alab args tenv taenv t
inlineAE f = \case
    Const lab x -> Const lab x
    PrimApp lab op e -> PrimApp lab op (inlineAE f e)
    PrimConst lab c -> PrimConst lab c
    Pair lab e1 e2 -> Pair lab (inlineAE f e1) (inlineAE f e2)
    Nil lab -> Nil lab
    Cond lab e1 e2 e3 -> Cond lab (inlineAE f e1) (inlineAE f e2) (inlineAE f e3)
    Shape lab ref -> Shape lab (inlineAE_ArrayRef f ref)
    Index lab ref execLab e -> Index lab (inlineAE_ArrayRef f ref) execLab (inlineAE f e)
    ShapeSize lab sht e -> ShapeSize lab sht (inlineAE f e)
    Get lab ti e -> Get lab ti (inlineAE f e)
    Undef lab -> Undef lab
    Let lhs rhs e -> Let lhs (inlineAE f rhs) (inlineAE f e)
    Arg lab argsty tidx -> Arg lab argsty tidx
    Var lab var referLab -> Var lab var referLab
    FreeVar lab var -> FreeVar lab var
  where
    inlineAE_ArrayRef :: InlinerA aenv aenv' lab alab args taenv -> ArrayRef aenv taenv alab t -> ArrayRef aenv' taenv alab t
    inlineAE_ArrayRef f' (ARVar var)
      | Avar _ var' _ <- unInlinerA f' var = ARVar var'
      | otherwise = error ("inlineAE: Non-array-variable inlined in expression: " ++
                              showsAcc (ShowEnv (const "L?") (const "L?") 0 () []) 0 (unInlinerA f' var) "")
    inlineAE_ArrayRef _ (ARFree var) = ARFree var
    inlineAE_ArrayRef _ (ARLab lab) = ARLab lab

inlineAEF :: InlinerA aenv aenv' lab alab args taenv -> OpenFun env aenv lab alab tenv taenv t -> OpenFun env aenv' lab alab tenv taenv t
inlineAEF f (Lam lhs fun) = Lam lhs (inlineAEF f fun)
inlineAEF f (Body e) = Body (inlineAE f e)

inlineALam :: InlinerA aenv aenv' lab alab args taenv -> ExpLambda1 aenv lab alab tenv taenv sh t t' -> ExpLambda1 aenv' lab alab tenv taenv sh t  t'
inlineALam f = fmapPlain (inlineAEF f)

data InlinerE env env' aenv lab alab args tenv taenv =
    InlinerE { unInlinerE :: forall t. A.ExpVar env t -> OpenExp env' aenv lab alab args tenv taenv t }

sinkInlinerESucc :: InlinerE env env' aenv () alab args tenv taenv -> InlinerE (env, a) (env', a) aenv () alab args tenv taenv
sinkInlinerESucc (InlinerE f) =
    InlinerE (\case A.Var ty ZeroIdx -> smartVar (A.Var ty ZeroIdx)
                    A.Var ty (SuccIdx idx) -> sinkExp (weakenSucc' weakenId) (f (A.Var ty idx)))

sinkInlinerELHS :: A.ELeftHandSide t env env2 -> A.ELeftHandSide t env' env2' -> InlinerE env env' aenv () alab args tenv taenv -> InlinerE env2 env2' aenv () alab args tenv taenv
sinkInlinerELHS (LeftHandSideWildcard _) (LeftHandSideWildcard _) = id
sinkInlinerELHS (LeftHandSideSingle _) (LeftHandSideSingle _) = sinkInlinerESucc
sinkInlinerELHS (LeftHandSidePair lhs1 lhs2) (LeftHandSidePair lhs1' lhs2') = sinkInlinerELHS lhs2 lhs2' . sinkInlinerELHS lhs1 lhs1'
sinkInlinerELHS _ _ = error "sinkInlinerELHS: Unequal LHS's"

inlineE :: InlinerE env env' aenv () alab args tenv taenv -> OpenExp env aenv () alab args tenv taenv t -> OpenExp env' aenv () alab args tenv taenv t
inlineE f = \case
    Const lab x -> Const lab x
    PrimApp lab op e -> PrimApp lab op (inlineE f e)
    PrimConst lab c -> PrimConst lab c
    Pair lab e1 e2 -> Pair lab (inlineE f e1) (inlineE f e2)
    Nil lab -> Nil lab
    Cond lab e1 e2 e3 -> Cond lab (inlineE f e1) (inlineE f e2) (inlineE f e3)
    Shape lab ref -> Shape lab ref
    Index lab ref execLab e -> Index lab ref execLab (inlineE f e)
    ShapeSize lab sht e -> ShapeSize lab sht (inlineE f e)
    Get lab ti e -> Get lab ti (inlineE f e)
    Undef lab -> Undef lab
    Let lhs rhs e
      | Exists lhs' <- rebuildLHS lhs
      -> Let lhs' (inlineE f rhs) (inlineE (sinkInlinerELHS lhs lhs' f) e)
    Arg lab argsty tidx -> Arg lab argsty tidx
    Var _ var _ -> unInlinerE f var
    FreeVar lab var -> FreeVar lab var

lhsHasWildcard :: LeftHandSide s t env env' -> Bool
lhsHasWildcard (LeftHandSideWildcard _) = True
lhsHasWildcard (LeftHandSideSingle _) = False
lhsHasWildcard (LeftHandSidePair lhs1 lhs2) = lhsHasWildcard lhs1 || lhsHasWildcard lhs2

data Reprojection s from to where
  RjKeep :: TupR s t -> Reprojection s t t
  RjNil :: Reprojection s t ()
  RjFst :: TupR s a' -> Reprojection s a a' -> Reprojection s (a, b) a'
  RjSnd :: TupR s b' -> Reprojection s b b' -> Reprojection s (a, b) b'
  RjPair :: TupR s (a', b') -> Reprojection s a a' -> Reprojection s b b' -> Reprojection s (a, b) (a', b')

rjType2 :: Reprojection s t t' -> TupR s t'
rjType2 (RjKeep ty) = ty
rjType2 RjNil = TupRunit
rjType2 (RjFst ty _) = ty
rjType2 (RjSnd ty _) = ty
rjType2 (RjPair ty _ _) = ty

data PrunedLHS s t env env' =
    forall t'.
        PrunedLHS (LeftHandSide s t' env env') (Reprojection s t t')

pruneLHS :: LeftHandSide s t env env' -> PrunedLHS s t env env'
pruneLHS (LeftHandSideWildcard _) = PrunedLHS (LeftHandSideWildcard TupRunit) RjNil
pruneLHS lhs@(LeftHandSideSingle ty) = PrunedLHS lhs (RjKeep (TupRsingle ty))
pruneLHS (LeftHandSidePair lhs1 lhs2)
  | PrunedLHS lhs1' rj1 <- pruneLHS lhs1
  , PrunedLHS lhs2' rj2 <- pruneLHS lhs2
  = case (lhs1', rj1, lhs2', rj2) of
      (LeftHandSideWildcard TupRunit, RjNil, LeftHandSideWildcard TupRunit, RjNil) ->
        PrunedLHS (LeftHandSideWildcard TupRunit) RjNil
      (LeftHandSideWildcard TupRunit, RjNil, _, _) ->
        PrunedLHS lhs2' (RjSnd (lhsToTupR lhs2') rj2)
      (_, _, LeftHandSideWildcard TupRunit, RjNil) ->
        PrunedLHS lhs1' (RjFst (lhsToTupR lhs1') rj1)
      _ ->
        let lhs' = LeftHandSidePair lhs1' lhs2'
        in PrunedLHS lhs' (RjPair (lhsToTupR lhs') rj1 rj2)

reprojectA :: Reprojection ArrayR t t' -> OpenAcc aenv lab () args taenv t -> OpenAcc aenv lab () args taenv t'
reprojectA RjNil _ = Anil (nilLabel TupRunit)
reprojectA (RjKeep _) a = a
reprojectA rj@(RjFst resty rj1) acc = case acc of
    Apair _ a _ -> reprojectA rj1 a
    Acond _ e a1 a2 -> Acond (DLabel resty ()) e (reprojectA rj a1) (reprojectA rj a2)
    Scan' lab@(labelType -> TupRpair _ ty2) dir fun e0 a
      | RjKeep (TupRsingle resty') <- rj1
      -> Alet (LeftHandSidePair (LeftHandSideSingle resty') (LeftHandSideWildcard ty2))
              (Scan' lab dir fun e0 a)
              (smartAvar (A.Var resty' ZeroIdx))
    Scan' _ _ _ _ _ -> error "Invalid GADTs"
    Aget lab tidx a -> reprojectA rj1 (smartFstA (Aget lab tidx a))
    Alet lhs a1 a2 -> Alet lhs a1 (reprojectA rj a2)
reprojectA rj@(RjSnd resty rj1) acc = case acc of
    Apair _ _ b -> reprojectA rj1 b
    Acond _ e a1 a2 -> Acond (DLabel resty ()) e (reprojectA rj a1) (reprojectA rj a2)
    Scan' lab@(labelType -> TupRpair ty1 _) dir fun e0 a
      | RjKeep (TupRsingle resty') <- rj1
      -> Alet (LeftHandSidePair (LeftHandSideWildcard ty1) (LeftHandSideSingle resty'))
              (Scan' lab dir fun e0 a)
              (smartAvar (A.Var resty' ZeroIdx))
    Scan' _ _ _ _ _ -> error "Invalid GADTs"
    Aget lab tidx a -> reprojectA rj1 (smartSndA (Aget lab tidx a))
    Alet lhs a1 a2 -> Alet lhs a1 (reprojectA rj a2)
reprojectA rj@(RjPair resty rj1 rj2) acc = case acc of
    Apair _ a b ->
        let a' = reprojectA rj1 a
            b' = reprojectA rj2 b
        in Apair (nilLabel (TupRpair (atypeOf a') (atypeOf b'))) (reprojectA rj1 a) (reprojectA rj2 b)
    Acond _ e a1 a2 -> Acond (DLabel resty ()) e (reprojectA rj a1) (reprojectA rj a2)
    Scan' lab dir fun e0 a
      | RjKeep _ <- rj1
      , RjKeep _ <- rj2
      -> Scan' lab dir fun e0 a
    Scan' _ _ _ _ _ -> error "Invalid GADTs"
    Aget _ tidx a -> reprojectA (addTidxToReproject (atypeOf a) tidx rj) a
    Alet lhs a1 a2 -> Alet lhs a1 (reprojectA rj a2)

reprojectE :: Reprojection ScalarType t t' -> OpenExp env aenv () alab args tenv taenv t -> OpenExp env aenv () alab args tenv taenv t'
reprojectE RjNil _ = Nil (nilLabel TupRunit)
reprojectE (RjKeep _) a = a
reprojectE rj@(RjFst resty rj1) expr = case expr of
    Pair _ a _ -> reprojectE rj1 a
    Cond _ e a1 a2 -> Cond (DLabel resty ()) e (reprojectE rj a1) (reprojectE rj a2)
    Get lab tidx a -> reprojectE rj1 (smartFst (Get lab tidx a))
    Let lhs a1 a2 -> Let lhs a1 (reprojectE rj a2)
    _ | LetBoundVars lhs' vars <- rjToLHS (etypeOf expr) rj
      -> Let lhs' expr (evars vars)
reprojectE rj@(RjSnd resty rj1) expr = case expr of
    Pair _ _ b -> reprojectE rj1 b
    Cond _ e a1 a2 -> Cond (DLabel resty ()) e (reprojectE rj a1) (reprojectE rj a2)
    Get lab tidx a -> reprojectE rj1 (smartSnd (Get lab tidx a))
    Let lhs a1 a2 -> Let lhs a1 (reprojectE rj a2)
    _ | LetBoundVars lhs' vars <- rjToLHS (etypeOf expr) rj
      -> Let lhs' expr (evars vars)
reprojectE rj@(RjPair resty rj1 rj2) expr = case expr of
    Pair _ a b ->
        let a' = reprojectE rj1 a
            b' = reprojectE rj2 b
        in Pair (nilLabel (TupRpair (etypeOf a') (etypeOf b'))) (reprojectE rj1 a) (reprojectE rj2 b)
    Cond _ e a1 a2 -> Cond (DLabel resty ()) e (reprojectE rj a1) (reprojectE rj a2)
    Get _ tidx a -> reprojectE (addTidxToReproject (etypeOf a) tidx rj) a
    Let lhs a1 a2 -> Let lhs a1 (reprojectE rj a2)
    _ | LetBoundVars lhs' vars <- rjToLHS (etypeOf expr) rj
      -> Let lhs' expr (evars vars)

addTidxToReproject :: TupR s t1 -> TupleIdx t1 t2 -> Reprojection s t2 t3 -> Reprojection s t1 t3
addTidxToReproject _ TIHere rj = rj
addTidxToReproject (TupRpair t1 _) (TILeft ti) rj =
  let rj' = addTidxToReproject t1 ti rj
  in RjFst (rjType2 rj') (addTidxToReproject t1 ti rj)
addTidxToReproject (TupRpair _ t2) (TIRight ti) rj =
  let rj' = addTidxToReproject t2 ti rj
  in RjSnd (rjType2 rj') (addTidxToReproject t2 ti rj)
addTidxToReproject _ _ _ = error "Invalid GADTs"

rjToLHS :: TupR s t -> Reprojection s t t' -> LetBoundVars s env t t'
rjToLHS ty (RjKeep _) = lhsCopy ty
rjToLHS ty RjNil = LetBoundVars (LeftHandSideWildcard ty) TupRunit
rjToLHS (TupRpair t1 t2) (RjFst _ rj)
  | LetBoundVars lhs vars <- rjToLHS t1 rj
  = LetBoundVars (LeftHandSidePair lhs (LeftHandSideWildcard t2)) vars
rjToLHS (TupRpair t1 t2) (RjSnd _ rj)
  | LetBoundVars lhs vars <- rjToLHS t2 rj
  = LetBoundVars (LeftHandSidePair (LeftHandSideWildcard t1) lhs) vars
rjToLHS (TupRpair t1 t2) (RjPair _ rj1 rj2)
  | LetBoundVars lhs1 vars1 <- rjToLHS t1 rj1
  , LetBoundVars lhs2 vars2 <- rjToLHS t2 rj2
  = LetBoundVars (LeftHandSidePair lhs1 lhs2)
                 (TupRpair (fmapTupR (weaken (weakenWithLHS lhs2)) vars1) vars2)
rjToLHS _ _ = error "Invalid GADTs"

-- If an array variable is used in an expression in an Index or Shape node, a
-- non-variable array program can never be inlined for that variable. Hence,
-- AccInExp works as an infinite value.
-- Note that the generated Ord instance is consistent with AccInExp being
-- infinite.
data UsageCount = Finite Int | AccInExp
  deriving (Show, Eq, Ord)

instance Semigroup UsageCount where
  Finite a <> Finite b = Finite (a + b)
  AccInExp <> _ = AccInExp
  _ <> AccInExp = AccInExp

data Stats env where
    SNil :: Stats env
    SPush :: Stats env -> UsageCount -> Stats (env, t)

statAdd :: Idx env t -> UsageCount -> Stats env -> Stats env
statAdd ZeroIdx m (SPush stats n) = SPush stats (n <> m)
statAdd (SuccIdx idx) m (SPush stats n) = SPush (statAdd idx m stats) n
statAdd _ _ SNil = SNil  -- increment on above-scope variable; ignore

statAddV :: A.Var s env t -> UsageCount -> Stats env -> Stats env
statAddV (A.Var _ idx) = statAdd idx

spushLHS0 :: Stats env -> LeftHandSide s t env env' -> Stats env'
spushLHS0 stats (LeftHandSideWildcard _) = stats
spushLHS0 stats (LeftHandSideSingle _) = SPush stats (Finite 0)
spushLHS0 stats (LeftHandSidePair lhs1 lhs2) = spushLHS0 (spushLHS0 stats lhs1) lhs2

spopLHS' :: LeftHandSide s t env env' -> Stats env' -> (Stats env, Some (LeftHandSide s t env))
spopLHS' (LeftHandSideWildcard ty) stats = (stats, Some (LeftHandSideWildcard ty))
spopLHS' (LeftHandSideSingle ty) (SPush stats (Finite 0)) =
    (stats, Some (LeftHandSideWildcard (TupRsingle ty)))
spopLHS' (LeftHandSideSingle ty) (SPush stats _) =
    (stats, Some (LeftHandSideSingle ty))
spopLHS' (LeftHandSidePair lhs1 lhs2) stats
  | (stats2, Some lhs2') <- spopLHS' lhs2 stats
  , (stats1, Some lhs1') <- spopLHS' lhs1 stats2
  , Exists lhs2'' <- rebuildLHS lhs2'
  = (stats1, Some (LeftHandSidePair lhs1' lhs2''))
spopLHS' (LeftHandSideSingle _) SNil = error "spopLHS': Stats pop on empty stack"

sinkWithLHSAllowDrop :: LeftHandSide s t env1 env1' -> LeftHandSide s t env2 env2' -> env1 :> env2 -> env1' :> env2'
sinkWithLHSAllowDrop (LeftHandSideWildcard _) (LeftHandSideWildcard _) k = k
sinkWithLHSAllowDrop (LeftHandSideSingle _)   (LeftHandSideSingle _)   k = sink k
sinkWithLHSAllowDrop (LeftHandSideSingle _)   (LeftHandSideWildcard _) k =
    Weaken (\case ZeroIdx -> error "Variable with zero usage count is referenced"
                  SuccIdx i -> k >:> i)
sinkWithLHSAllowDrop (LeftHandSidePair a1 b1) (LeftHandSidePair a2 b2) k =
    sinkWithLHSAllowDrop b1 b2 $ sinkWithLHSAllowDrop a1 a2 k
sinkWithLHSAllowDrop _ _ _ = error "left hand sides do not match in sinkWithLHSAllowDrop"

-- TODO: This is kind of like the State monad. If possible, make it an actual monad (and if not, document why it's impossible).
infixl 4 !$!
(!$!) :: (a -> b) -> (s -> (s, a)) -> (s -> (s, b))
(!$!) = fmap . fmap

infixl 4 !**!
(!**!) :: (s -> (s, a -> b)) -> (s -> (s, a)) -> (s -> (s, b))
ff !**! xf = \s -> let (s1, f) = ff s in f <$> xf s1

returnS :: a -> s -> (s, a)
returnS x s = (s, x)
