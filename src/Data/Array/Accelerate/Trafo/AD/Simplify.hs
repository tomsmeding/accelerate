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
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Substitution (rebuildLHS)
import Data.Array.Accelerate.Trafo.AD.Acc
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Debug
import Data.Array.Accelerate.Trafo.AD.Pretty
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.Sink


-- TODO: This Simplify module is quadratic in the program size.


simplifyAcc :: (Show lab, Show alab) => OpenAcc aenv lab alab args t -> OpenAcc aenv lab alab args t
simplifyAcc a = let res = snd (goAcc a SNil)
                in trace ("simplify result:\n" ++ prettyPrint res) res
-- simplifyAcc = snd . flip goAcc SNil
-- simplifyAcc = id

simplifyExp :: OpenExp env aenv lab alab args t -> OpenExp env aenv lab alab args t
simplifyExp = snd . flip goExp (SNil, SNil)
-- simplifyExp = id

goAcc :: OpenAcc aenv lab alab args t -> Stats aenv -> (Stats aenv, OpenAcc aenv lab alab args t)
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
    Alet (LeftHandSideSingle ty) (Avar var) a2 ->
        goAcc $
            inlineA (InlinerA (\case A.Var ty' ZeroIdx | Just Refl <- matchArrayR ty ty' -> Avar var
                                                       | otherwise -> error "Invalid GADTs"
                                     A.Var ty'@(ArrayR _ _) (SuccIdx idx) -> Avar (A.Var ty' idx)))
                    a2

    -- Linear inlining
    Alet lhs@(LeftHandSideSingle ty) a1 a2 ->
      \s -> let (s1, a1') = goAcc a1 s
                (SPush s2 n, a2') = goAcc a2 (SPush s1 0)
            in (s2, if n <= 1
                        then inlineA (InlinerA (\case A.Var ty' ZeroIdx | Just Refl <- matchArrayR ty ty' -> a1'
                                                                        | otherwise -> error "Invalid GADTs"
                                                      A.Var ty'@(ArrayR _ _) (SuccIdx idx) -> Avar (A.Var ty' idx)))
                                     a2'
                        else Alet lhs a1' a2')

    Aconst ty x -> returnS $ Aconst ty x
    Apair ty a1 a2 -> Apair ty !$! goAcc a1 !**! goAcc a2
    Anil -> returnS Anil
    Acond ty e a1 a2 -> Acond ty !$! goExp' e !**! goAcc a1 !**! goAcc a2
    Map ty lam a -> Map ty !$! simplifyLam1 lam !**! goAcc a
    ZipWith ty lam a1 a2 -> ZipWith ty !$! simplifyLam1 lam !**! goAcc a1 !**! goAcc a2
    Generate ty e lam -> Generate ty !$! goExp' e !**! simplifyLam1 lam
    Fold ty lam me0 a -> Fold ty !$! simplifyLam1 lam
                                 !**! (case me0 of Just e0 -> Just !$! goExp' e0
                                                   Nothing -> returnS Nothing)
                                 !**! goAcc a
    Sum ty a -> Sum ty !$! goAcc a
    Replicate ty slt she a -> Replicate ty slt !$! goExp' she !**! goAcc a
    Slice ty slt a she -> Slice ty slt !$! goAcc a !**! goExp' she
    Reduce ty spec f a -> Reduce ty spec !$! simplifyFun f !**! goAcc a
    Reshape ty she a -> Reshape ty !$! goExp' she !**! goAcc a
    Backpermute ty she f a -> Backpermute ty !$! goExp' she !**! simplifyFun f !**! goAcc a
    Permute ty f a1 pf a2 -> Permute ty !$! simplifyFun f !**! goAcc a1 !**! simplifyFun pf !**! goAcc a2
    Aget ty tidx a -> Aget ty tidx !$! goAcc a
    Aarg ty idx -> returnS $ Aarg ty idx
    Alabel lab -> returnS $ Alabel lab
    Alet lhs a1 a2 ->
      \s -> let (s1, a1') = goAcc a1 s
                (s2, a2') = goAcc a2 (spushLHS0 s1 lhs)
            in (spopLHS lhs s2, Alet lhs a1' a2')
    Avar var ->
      \s -> (statAddV var 1 s, Avar var)

goExp' :: OpenExp env aenv lab alab args t -> Stats aenv -> (Stats aenv, OpenExp env aenv lab alab args t)
goExp' e s = let ((s', SNil), e') = goExp e (s, SNil) in (s', e')

goExp :: OpenExp env aenv lab alab args t -> (Stats aenv, Stats env) -> ((Stats aenv, Stats env), OpenExp env aenv lab alab args t)
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
              inlineE (InlinerE (\case A.Var ty' ZeroIdx | Just Refl <- matchScalarType ty ty' -> rhs
                                                         | otherwise -> error "Invalid GADTs"
                                       A.Var ty' (SuccIdx idx) -> Var (A.Var ty' idx)))
                      e

    -- Linear inlining
    Let lhs@(LeftHandSideSingle ty) rhs e ->
      \s -> let ((s1a, s1e), rhs') = goExp rhs s
                ((s2a, SPush s2e n), e') = goExp e (s1a, SPush s1e 0)
            in ((s2a, s2e),
                if n <= 1
                    then inlineE (InlinerE (\case A.Var ty' ZeroIdx | Just Refl <- matchScalarType ty ty' -> rhs'
                                                                    | otherwise -> error "Invalid GADTs"
                                                  A.Var ty' (SuccIdx idx) -> Var (A.Var ty' idx)))
                                 e'
                    else Let lhs rhs' e')

    -- Get elimination
    Get ty ti e ->
      \s -> case (ti, goExp e s) of
              (TILeft ti', (s', Pair _ e1 _)) -> (s', elimEmptyTI ty ti' e1)
              (TIRight ti', (s', Pair _ _ e2)) -> (s', elimEmptyTI ty ti' e2)
              (_, (s', e')) -> (s', Get ty ti e')
      where
        elimEmptyTI :: TypeR t' -> TupleIdx t t' -> OpenExp env aenv lab alab args t -> OpenExp env aenv lab alab args t'
        elimEmptyTI _ TIHere e' = e'
        elimEmptyTI ty' ti' e' = Get ty' ti' e'

    Const ty x -> returnS $ Const ty x
    PrimApp ty op e -> PrimApp ty op !$! goExp e
    Pair ty e1 e2 -> Pair ty !$! goExp e1 !**! goExp e2
    Nil -> returnS Nil
    Cond ty e1 e2 e3 -> Cond ty !$! goExp e1 !**! goExp e2 !**! goExp e3
    Shape ref -> Shape !$! goVarOrLab ref
    Index ref e -> Index !$! goVarOrLab ref !**! goExp e
    ShapeSize sht e -> ShapeSize sht !$! goExp e
    Let lhs rhs e ->
      \s -> let ((s1a, s1e), rhs') = goExp rhs s
                (s2, e') = goExp e (s1a, spushLHS0 s1e lhs)
            in (second (spopLHS lhs) s2, Let lhs rhs' e')
    Arg ty idx -> returnS $ Arg ty idx
    Var var -> \s -> (second (statAddV var 1) s, Var var)
    Label lab -> returnS $ Label lab

goVarOrLab :: Either (A.ArrayVar aenv t) (ADLabel lab t) -> (Stats aenv, Stats env) -> ((Stats aenv, Stats env), Either (A.ArrayVar aenv t) (ADLabel lab t))
goVarOrLab (Left var) (sa, se) = ((statAddV var 2 sa, se), Left var)
goVarOrLab (Right lab) s = (s, Right lab)

simplifyFun :: OpenFun env aenv lab alab t -> Stats aenv -> (Stats aenv, OpenFun env aenv lab alab t)
simplifyFun (Lam lhs fun) = Lam lhs !$! simplifyFun fun
simplifyFun (Body ex) = Body !$! goExp' ex

simplifyLam1 :: ExpLambda1 aenv lab alab sh t1 t2 -> Stats aenv -> (Stats aenv, ExpLambda1 aenv lab alab sh t1 t2)
simplifyLam1 (Left lam) = returnS (Left lam)
simplifyLam1 (Right fun) = \s -> Right <$> simplifyFun fun s

noCostCopy :: OpenExp env aenv lab alab args t -> Bool
noCostCopy (Var _) = True
noCostCopy (Const _ _) = True
noCostCopy _ = False

data InlinerA aenv aenv' lab alab args =
    InlinerA { unInlinerA :: forall t. A.ArrayVar aenv t -> OpenAcc aenv' lab alab args t }

sinkInlinerASucc :: InlinerA aenv aenv' lab alab args -> InlinerA (aenv, a) (aenv', a) lab alab args
sinkInlinerASucc (InlinerA f) =
    InlinerA (\case A.Var ty@(ArrayR _ _) ZeroIdx -> Avar (A.Var ty ZeroIdx)
                    A.Var ty (SuccIdx idx) -> sinkAcc (weakenSucc' weakenId) (f (A.Var ty idx)))

sinkInlinerALHS :: A.ALeftHandSide t aenv aenv2 -> A.ALeftHandSide t aenv' aenv2' -> InlinerA aenv aenv' lab alab args -> InlinerA aenv2 aenv2' lab alab args
sinkInlinerALHS (LeftHandSideWildcard _) (LeftHandSideWildcard _) = id
sinkInlinerALHS (LeftHandSideSingle _) (LeftHandSideSingle _) = sinkInlinerASucc
sinkInlinerALHS (LeftHandSidePair lhs1 lhs2) (LeftHandSidePair lhs1' lhs2') = sinkInlinerALHS lhs2 lhs2' . sinkInlinerALHS lhs1 lhs1'
sinkInlinerALHS _ _ = error "sinkInlinerALHS: Unequal LHS's"

inlineA :: InlinerA aenv aenv' lab alab args -> OpenAcc aenv lab alab args t -> OpenAcc aenv' lab alab args t
inlineA f = \case
    Aconst ty x -> Aconst ty x
    Apair ty a1 a2 -> Apair ty (inlineA f a1) (inlineA f a2)
    Anil -> Anil
    Acond ty e a1 a2 -> Acond ty (inlineAE f e) (inlineA f a1) (inlineA f a2)
    Map ty lam a -> Map ty (inlineALam f lam) (inlineA f a)
    ZipWith ty lam a1 a2 -> ZipWith ty (inlineALam f lam) (inlineA f a1) (inlineA f a2)
    Generate ty e lam -> Generate ty (inlineAE f e) (inlineALam f lam)
    Fold ty lam me0 a -> Fold ty (inlineALam f lam) (inlineAE f <$> me0) (inlineA f a)
    Sum ty a -> Sum ty (inlineA f a)
    Replicate ty slt she a -> Replicate ty slt (inlineAE f she) (inlineA f a)
    Slice ty slt a she -> Slice ty slt (inlineA f a) (inlineAE f she)
    Reduce ty spec f' a -> Reduce ty spec (inlineAEF f f') (inlineA f a)
    Reshape ty she a -> Reshape ty (inlineAE f she) (inlineA f a)
    Backpermute ty she f' a -> Backpermute ty (inlineAE f she) (inlineAEF f f') (inlineA f a)
    Permute ty f' a1 pf a2 -> Permute ty (inlineAEF f f') (inlineA f a1) (inlineAEF f pf) (inlineA f a2)
    Aget ty tidx a -> Aget ty tidx (inlineA f a)
    Aarg ty idx -> Aarg ty idx
    Alabel lab -> Alabel lab
    Alet lhs a1 a2
      | Exists lhs2 <- rebuildLHS lhs
      -> Alet lhs2 (inlineA f a1) (inlineA (sinkInlinerALHS lhs lhs2 f) a2)
    Avar var -> unInlinerA f var

inlineAE :: InlinerA aenv aenv' lab alab aargs -> OpenExp env aenv lab alab args t -> OpenExp env aenv' lab alab args t
inlineAE f = \case
    Const ty x -> Const ty x
    PrimApp ty op e -> PrimApp ty op (inlineAE f e)
    Pair ty e1 e2 -> Pair ty (inlineAE f e1) (inlineAE f e2)
    Nil -> Nil
    Cond ty e1 e2 e3 -> Cond ty (inlineAE f e1) (inlineAE f e2) (inlineAE f e3)
    Shape ref -> Shape (inlineAE_VarOrLab f ref)
    Index ref e -> Index (inlineAE_VarOrLab f ref) (inlineAE f e)
    ShapeSize sht e -> ShapeSize sht (inlineAE f e)
    Get ty ti e -> Get ty ti (inlineAE f e)
    Let lhs rhs e -> Let lhs (inlineAE f rhs) (inlineAE f e)
    Arg ty idx -> Arg ty idx
    Var var -> Var var
    Label lab -> Label lab
  where
    inlineAE_VarOrLab :: InlinerA aenv aenv' lab alab args -> Either (A.ArrayVar aenv t) (ADLabel alab t) -> Either (A.ArrayVar aenv' t) (ADLabel alab t)
    inlineAE_VarOrLab f' (Left var)
      | Avar var' <- unInlinerA f' var = Left var'
      | otherwise = error "inlineAE: Inlining array variable referenced in expression"
    inlineAE_VarOrLab _ (Right lab) = Right lab

inlineAEF :: InlinerA aenv aenv' lab alab args -> OpenFun env aenv lab alab t -> OpenFun env aenv' lab alab t
inlineAEF f (Lam lhs fun) = Lam lhs (inlineAEF f fun)
inlineAEF f (Body e) = Body (inlineAE f e)

inlineALam :: InlinerA aenv aenv' lab alab args -> ExpLambda1 aenv lab alab sh t t' -> ExpLambda1 aenv' lab alab sh t  t'
inlineALam _ (Left lam) = Left lam
inlineALam f (Right fun) = Right (inlineAEF f fun)

data InlinerE env env' aenv lab alab args =
    InlinerE { unInlinerE :: forall t. A.ExpVar env t -> OpenExp env' aenv lab alab args t }

sinkInlinerESucc :: InlinerE env env' aenv lab alab args -> InlinerE (env, a) (env', a) aenv lab alab args
sinkInlinerESucc (InlinerE f) =
    InlinerE (\case A.Var ty ZeroIdx -> Var (A.Var ty ZeroIdx)
                    A.Var ty (SuccIdx idx) -> sinkExp (weakenSucc' weakenId) (f (A.Var ty idx)))

sinkInlinerELHS :: A.ELeftHandSide t env env2 -> A.ELeftHandSide t env' env2' -> InlinerE env env' aenv lab alab args -> InlinerE env2 env2' aenv lab alab args
sinkInlinerELHS (LeftHandSideWildcard _) (LeftHandSideWildcard _) = id
sinkInlinerELHS (LeftHandSideSingle _) (LeftHandSideSingle _) = sinkInlinerESucc
sinkInlinerELHS (LeftHandSidePair lhs1 lhs2) (LeftHandSidePair lhs1' lhs2') = sinkInlinerELHS lhs2 lhs2' . sinkInlinerELHS lhs1 lhs1'
sinkInlinerELHS _ _ = error "sinkInlinerELHS: Unequal LHS's"

inlineE :: InlinerE env env' aenv lab alab args -> OpenExp env aenv lab alab args t -> OpenExp env' aenv lab alab args t
inlineE f = \case
    Const ty x -> Const ty x
    PrimApp ty op e -> PrimApp ty op (inlineE f e)
    Pair ty e1 e2 -> Pair ty (inlineE f e1) (inlineE f e2)
    Nil -> Nil
    Cond ty e1 e2 e3 -> Cond ty (inlineE f e1) (inlineE f e2) (inlineE f e3)
    Shape ref -> Shape ref
    Index ref e -> Index ref (inlineE f e)
    ShapeSize sht e -> ShapeSize sht (inlineE f e)
    Get ty ti e -> Get ty ti (inlineE f e)
    Let lhs rhs e
      | Exists lhs' <- rebuildLHS lhs
      -> Let lhs' (inlineE f rhs) (inlineE (sinkInlinerELHS lhs lhs' f) e)
    Arg ty idx -> Arg ty idx
    Var var -> unInlinerE f var
    Label lab -> Label lab

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
