{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Data.Array.Accelerate.Trafo.AD.Simplify (
  simplifyAcc, simplifyExp
) where

import Control.Arrow (second)

import Data.Array.Accelerate.AST.Environment (sinkWithLHS, weakenWithLHS, weakenId, weakenSucc')
import Data.Array.Accelerate.AST.LeftHandSide (LeftHandSide(..), Exists(..))
import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.Analysis.Match ((:~:)(Refl), matchArrayR, matchScalarType)
import qualified Data.Array.Accelerate.Analysis.Match as A (matchOpenExp)
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Trafo.Substitution (rebuildLHS)
import Data.Array.Accelerate.Trafo.AD.Acc
import Data.Array.Accelerate.Trafo.AD.Additive
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Debug
import Data.Array.Accelerate.Trafo.AD.Pretty
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.Sink


-- TODO: This Simplify module is quadratic in the program size.


simplifyAcc :: OpenAcc aenv () () args t -> OpenAcc aenv () () args t
simplifyAcc a = let res = snd (goAcc a SNil)
                in trace ("simplify input:\n" ++ prettyPrint a) $ trace ("simplify result:\n" ++ prettyPrint res) res
-- simplifyAcc = snd . flip goAcc SNil
-- simplifyAcc = id

simplifyExp :: Show alab => OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t
simplifyExp a = let res = snd (goExp a (SNil, SNil))
                in trace ("simplify input:\n" ++ prettyPrint a) $ trace ("simplify result:\n" ++ prettyPrint res) res
-- simplifyExp = snd . flip goExp (SNil, SNil)
-- simplifyExp = id

goAcc :: OpenAcc aenv () () args t -> Stats aenv -> (Stats aenv, OpenAcc aenv () () args t)
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

    -- Variable equation inlining
    Alet (LeftHandSideSingle ty) (Avar _ var _) a2 ->
        goAcc $
            inlineA (InlinerA (\case A.Var ty' ZeroIdx
                                       | Just Refl <- matchArrayR ty ty' -> smartAvar var
                                       | otherwise -> error "Invalid GADTs"
                                     A.Var ty'@ArrayR{} (SuccIdx idx)
                                       -> smartAvar (A.Var ty' idx)))
                    a2

    -- Linear inlining
    Alet lhs@(LeftHandSideSingle ty) a1 a2 ->
      \s -> let (s1, a1') = goAcc a1 s
                (SPush s2 n, a2') = goAcc a2 (SPush s1 0)
            in (s2, if n <= 1
                        then inlineA (InlinerA (\case A.Var ty' ZeroIdx
                                                        | Just Refl <- matchArrayR ty ty' -> a1'
                                                        | otherwise -> error "Invalid GADTs"
                                                      A.Var ty'@ArrayR{} (SuccIdx idx)
                                                        -> smartAvar (A.Var ty' idx)))
                                     a2'
                        else Alet lhs a1' a2')

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
            in (spopLHS lhs s2, Alet lhs a1' a2')
    Avar lab var referLab ->
      \s -> (statAddV var 1 s, Avar lab var referLab)

goExp' :: OpenExp env aenv () alab args tenv t -> Stats aenv -> (Stats aenv, OpenExp env aenv () alab args tenv t)
goExp' e s = let ((s', SNil), e') = goExp e (s, SNil) in (s', e')

goExp :: OpenExp env aenv () alab args tenv t -> (Stats aenv, Stats env) -> ((Stats aenv, Stats env), OpenExp env aenv () alab args tenv t)
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
      | noCostCopy rhs ->
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
                ((s2a, SPush s2e n), e') = goExp e (s1a, SPush s1e 0)
            in ((s2a, s2e),
                if n <= 1
                    then inlineE (InlinerE (\case A.Var ty' ZeroIdx
                                                    | Just Refl <- matchScalarType ty ty' -> rhs'
                                                    | otherwise -> error "Invalid GADTs"
                                                  A.Var ty' (SuccIdx idx)
                                                    -> smartVar (A.Var ty' idx)))
                                 e'
                    else Let lhs rhs' e')

    -- Get elimination
    Get lab ti e ->
      \s -> case (ti, goExp e s) of
              (TILeft ti', (s', Pair _ e1 _)) -> (s', elimEmptyTI lab ti' e1)
              (TIRight ti', (s', Pair _ _ e2)) -> (s', elimEmptyTI lab ti' e2)
              (_, (s', e')) -> (s', Get lab ti e')
      where
        elimEmptyTI :: EDLabelN lab t' -> TupleIdx t t' -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv t'
        elimEmptyTI _ TIHere e' = e'
        elimEmptyTI ty' ti' e' = Get ty' ti' e'

    -- Algebraic simplifications
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
    Shape lab ref -> Shape lab !$! goVarOrLab ref
    Index lab ref execLab e -> Index lab !$! goVarOrLab ref !**! returnS execLab !**! goExp e
    ShapeSize lab sht e -> ShapeSize lab sht !$! goExp e
    Undef ty -> returnS $ Undef ty  -- TODO: undef poisons, and can be propagated; however we currently don't generate code where that would help.
    Let lhs rhs e ->
      \s -> let ((s1a, s1e), rhs') = goExp rhs s
                (s2, e') = goExp e (s1a, spushLHS0 s1e lhs)
            in (second (spopLHS lhs) s2, Let lhs rhs' e')
    Arg lab argsty tidx -> returnS $ Arg lab argsty tidx
    Var lab var referLab -> \s -> (second (statAddV var 1) s, Var lab var referLab)
    FreeVar lab var -> returnS $ FreeVar lab var
  where
    isNumConstant :: (forall a. Num a => a) -> OpenExp env aenv lab alab args tenv t -> Bool
    isNumConstant cnst (Const (DLabel { labelType = ty }) val)
      | Const _ val' <- zeroForType' cnst ty
      , Just Refl <- A.matchOpenExp (A.Const ty val) (A.Const ty val')
      = True
    isNumConstant _ _ = False

goVarOrLab :: Either (A.ArrayVar aenv t) (AAnyPartLabelN alab (Array sh e)) -> (Stats aenv, Stats env) -> ((Stats aenv, Stats env), Either (A.ArrayVar aenv t) (AAnyPartLabelN alab (Array sh e)))
goVarOrLab (Left var) (sa, se) = ((statAddV var 2 sa, se), Left var)
goVarOrLab (Right lab) s = (s, Right lab)

simplifyFun :: OpenFun env aenv () alab tenv t -> Stats aenv -> (Stats aenv, OpenFun env aenv () alab tenv t)
simplifyFun (Lam lhs fun) = Lam lhs !$! simplifyFun fun
simplifyFun (Body ex) = Body !$! goExp' ex

simplifyLam1 :: ExpLambda1 aenv () alab tenv sh t1 t2 -> Stats aenv -> (Stats aenv, ExpLambda1 aenv () alab tenv sh t1 t2)
simplifyLam1 (ELSplit lam lab) = returnS (ELSplit lam lab)
simplifyLam1 (ELPlain fun) = \s -> ELPlain <$> simplifyFun fun s

noCostCopy :: OpenExp env aenv lab alab args tenv t -> Bool
noCostCopy (Var _ _ _) = True
noCostCopy (Const _ _) = True
noCostCopy (PrimConst _ _) = True  -- TODO: depending on the backend this might not be true?
noCostCopy _ = False

data InlinerA aenv aenv' lab alab args =
    InlinerA { unInlinerA :: forall t. A.ArrayVar aenv t -> OpenAcc aenv' lab alab args t }

sinkInlinerASucc :: InlinerA aenv aenv' lab () args -> InlinerA (aenv, a) (aenv', a) lab () args
sinkInlinerASucc (InlinerA f) =
    InlinerA (\case A.Var ty@ArrayR{} ZeroIdx -> smartAvar (A.Var ty ZeroIdx)
                    A.Var ty (SuccIdx idx) -> sinkAcc (weakenSucc' weakenId) (f (A.Var ty idx)))

sinkInlinerALHS :: A.ALeftHandSide t aenv aenv2 -> A.ALeftHandSide t aenv' aenv2' -> InlinerA aenv aenv' lab () args -> InlinerA aenv2 aenv2' lab () args
sinkInlinerALHS (LeftHandSideWildcard _) (LeftHandSideWildcard _) = id
sinkInlinerALHS (LeftHandSideSingle _) (LeftHandSideSingle _) = sinkInlinerASucc
sinkInlinerALHS (LeftHandSidePair lhs1 lhs2) (LeftHandSidePair lhs1' lhs2') = sinkInlinerALHS lhs2 lhs2' . sinkInlinerALHS lhs1 lhs1'
sinkInlinerALHS _ _ = error "sinkInlinerALHS: Unequal LHS's"

inlineA :: InlinerA aenv aenv' lab () args -> OpenAcc aenv lab () args t -> OpenAcc aenv' lab () args t
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

inlineAE :: InlinerA aenv aenv' lab alab aargs -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv' lab alab args tenv t
inlineAE f = \case
    Const lab x -> Const lab x
    PrimApp lab op e -> PrimApp lab op (inlineAE f e)
    PrimConst lab c -> PrimConst lab c
    Pair lab e1 e2 -> Pair lab (inlineAE f e1) (inlineAE f e2)
    Nil lab -> Nil lab
    Cond lab e1 e2 e3 -> Cond lab (inlineAE f e1) (inlineAE f e2) (inlineAE f e3)
    Shape lab ref -> Shape lab (inlineAE_VarOrLab f ref)
    Index lab ref execLab e -> Index lab (inlineAE_VarOrLab f ref) execLab (inlineAE f e)
    ShapeSize lab sht e -> ShapeSize lab sht (inlineAE f e)
    Get lab ti e -> Get lab ti (inlineAE f e)
    Undef lab -> Undef lab
    Let lhs rhs e -> Let lhs (inlineAE f rhs) (inlineAE f e)
    Arg lab argsty tidx -> Arg lab argsty tidx
    Var lab var referLab -> Var lab var referLab
    FreeVar lab var -> FreeVar lab var
  where
    inlineAE_VarOrLab :: InlinerA aenv aenv' lab alab args -> Either (A.ArrayVar aenv t) (AAnyPartLabelN alab (Array sh e)) -> Either (A.ArrayVar aenv' t) (AAnyPartLabelN alab (Array sh e))
    inlineAE_VarOrLab f' (Left var)
      | Avar _ var' _ <- unInlinerA f' var = Left var'
      | otherwise = error "inlineAE: Inlining array variable referenced in expression"
    inlineAE_VarOrLab _ (Right lab) = Right lab

inlineAEF :: InlinerA aenv aenv' lab alab args -> OpenFun env aenv lab alab tenv t -> OpenFun env aenv' lab alab tenv t
inlineAEF f (Lam lhs fun) = Lam lhs (inlineAEF f fun)
inlineAEF f (Body e) = Body (inlineAE f e)

inlineALam :: InlinerA aenv aenv' lab alab args -> ExpLambda1 aenv lab alab tenv sh t t' -> ExpLambda1 aenv' lab alab tenv sh t  t'
inlineALam f = fmapPlain (inlineAEF f)

data InlinerE env env' aenv lab alab args tenv =
    InlinerE { unInlinerE :: forall t. A.ExpVar env t -> OpenExp env' aenv lab alab args tenv t }

sinkInlinerESucc :: InlinerE env env' aenv () alab args tenv -> InlinerE (env, a) (env', a) aenv () alab args tenv
sinkInlinerESucc (InlinerE f) =
    InlinerE (\case A.Var ty ZeroIdx -> smartVar (A.Var ty ZeroIdx)
                    A.Var ty (SuccIdx idx) -> sinkExp (weakenSucc' weakenId) (f (A.Var ty idx)))

sinkInlinerELHS :: A.ELeftHandSide t env env2 -> A.ELeftHandSide t env' env2' -> InlinerE env env' aenv () alab args tenv -> InlinerE env2 env2' aenv () alab args tenv
sinkInlinerELHS (LeftHandSideWildcard _) (LeftHandSideWildcard _) = id
sinkInlinerELHS (LeftHandSideSingle _) (LeftHandSideSingle _) = sinkInlinerESucc
sinkInlinerELHS (LeftHandSidePair lhs1 lhs2) (LeftHandSidePair lhs1' lhs2') = sinkInlinerELHS lhs2 lhs2' . sinkInlinerELHS lhs1 lhs1'
sinkInlinerELHS _ _ = error "sinkInlinerELHS: Unequal LHS's"

inlineE :: InlinerE env env' aenv () alab args tenv -> OpenExp env aenv () alab args tenv t -> OpenExp env' aenv () alab args tenv t
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

data Stats env where
    SNil :: Stats env
    SPush :: Stats env -> Int -> Stats (env, t)

statAdd :: Idx env t -> Int -> Stats env -> Stats env
statAdd ZeroIdx m (SPush stats n) = SPush stats (n + m)
statAdd (SuccIdx idx) m (SPush stats n) = SPush (statAdd idx m stats) n
statAdd _ _ SNil = SNil  -- increment on above-scope variable; ignore

statAddV :: A.Var s env t -> Int -> Stats env -> Stats env
statAddV (A.Var _ idx) = statAdd idx

spushLHS0 :: Stats env -> LeftHandSide s t env env' -> Stats env'
spushLHS0 stats (LeftHandSideWildcard _) = stats
spushLHS0 stats (LeftHandSideSingle _) = SPush stats 0
spushLHS0 stats (LeftHandSidePair lhs1 lhs2) = spushLHS0 (spushLHS0 stats lhs1) lhs2

spopLHS :: LeftHandSide s t env env' -> Stats env' -> Stats env
spopLHS (LeftHandSideWildcard _) stats = stats
spopLHS (LeftHandSideSingle _) (SPush stats _) = stats
spopLHS (LeftHandSidePair lhs1 lhs2) stats = spopLHS lhs1 (spopLHS lhs2 stats)
spopLHS (LeftHandSideSingle _) SNil = error "spopLHS: Stats pop on empty stack"

-- TODO: This is kind of like the State monad. If possible, make it an actual monad (and if not, document why it's impossible).
infixl 4 !$!
(!$!) :: (a -> b) -> (s -> (s', a)) -> (s -> (s', b))
(!$!) = fmap . fmap

infixl 4 !**!
(!**!) :: (s -> (s', a -> b)) -> (s' -> (s'', a)) -> (s -> (s'', b))
ff !**! xf = \s -> let (s1, f) = ff s in f <$> xf s1

returnS :: a -> s -> (s, a)
returnS x s = (s, x)
