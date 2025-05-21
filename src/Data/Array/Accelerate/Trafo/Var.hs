{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Var
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Var
  where

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Substitution


data DeclareVars s t aenv where
  DeclareVars :: LeftHandSide s t env env'
              -> (env :> env')
              -> (forall env''. env' :> env'' -> Vars s env'' t)
              -> DeclareVars s t env

declareVars :: TupR s t -> DeclareVars s t env
declareVars TupRunit
  = DeclareVars LeftHandSideUnit weakenId $ const $ TupRunit
declareVars (TupRsingle s)
  = DeclareVars (LeftHandSideSingle s) (weakenSucc weakenId) $ \k -> TupRsingle $ Var s $ k >:> ZeroIdx
declareVars (TupRpair r1 r2)
  | DeclareVars lhs1 subst1 a1 <- declareVars r1
  , DeclareVars lhs2 subst2 a2 <- declareVars r2
  = DeclareVars (LeftHandSidePair lhs1 lhs2) (subst2 .> subst1) $ \k -> a1 (k .> subst2) `TupRpair` a2 k


type InjectAcc  acc = forall env t. PreOpenAcc acc env t -> acc env t
type ExtractAcc acc = forall env t. acc env t -> Maybe (PreOpenAcc acc env t)

avarIn :: InjectAcc acc
       -> ArrayVar aenv a
       -> acc aenv a
avarIn inject v@(Var ArrayR{} _) = inject (Avar v)

avarsIn :: forall acc aenv arrs.
           InjectAcc acc
        -> ArrayVars aenv arrs
        -> acc aenv arrs
avarsIn inject = avarsIn' inject id

avarsIn' :: forall acc aenv arrs s.
            InjectAcc acc
         -> (forall v. s v -> ArrayR v)
         -> Vars s aenv arrs
         -> acc aenv arrs
avarsIn' inject getType = go
  where
    go :: Vars s aenv t -> acc aenv t
    go TupRunit               = inject Anil
    go (TupRsingle (Var s t)) = avarIn inject (Var (getType s) t)
    go (TupRpair a b)         = inject (go a `Apair` go b)

avarsOut
    :: ExtractAcc acc
    -> PreOpenAcc acc aenv a
    -> Maybe (ArrayVars aenv a)
avarsOut extract = \case
  Anil   -> Just $ TupRunit
  Avar v -> Just $ TupRsingle v
  Apair al ar
    | Just pl <- extract al
    , Just pr <- extract ar
    , Just as <- avarsOut extract pl
    , Just bs <- avarsOut extract pr
    -> Just (TupRpair as bs)
  _ -> Nothing

identity :: TypeR a -> PreOpenFun arr env (a -> a)
identity t
  | DeclareVars lhs _ value <- declareVars t
  = Lam lhs $ Body $ expVars $ value weakenId

-- Used in various analyses
data MaybeVar s env t where
  NoVar     :: MaybeVar s env t
  JustVar   :: Var s env t -> MaybeVar s env t
type MaybeVars s env = TupR (MaybeVar s env)

strengthenMaybeVar :: LeftHandSide s' t env env' -> MaybeVar s env' u -> MaybeVar s env u
strengthenMaybeVar _ NoVar = NoVar
strengthenMaybeVar (LeftHandSideWildcard _) v = v
strengthenMaybeVar (LeftHandSideSingle _) (JustVar (Var t ix)) = case ix of
  SuccIdx ix' -> JustVar $ Var t ix'
  ZeroIdx     -> NoVar
strengthenMaybeVar (LeftHandSidePair l1 l2) v = strengthenMaybeVar l1 $ strengthenMaybeVar l2 v

strengthenMaybeVars :: LeftHandSide s' t env env' -> MaybeVars s env' u -> MaybeVars s env u
strengthenMaybeVars lhs = mapTupR (strengthenMaybeVar lhs)

instance Sink (MaybeVar s) where
  weaken _ NoVar = NoVar
  weaken k (JustVar var) = JustVar $ weaken k var

lhsMaybeVars :: LeftHandSide s t env env' -> MaybeVars s env' t
lhsMaybeVars (LeftHandSideWildcard tp) = mapTupR (const NoVar) tp
lhsMaybeVars (LeftHandSidePair l1 l2)  = mapTupR (weaken $ weakenWithLHS l2) (lhsMaybeVars l1) `TupRpair` lhsMaybeVars l2
lhsMaybeVars (LeftHandSideSingle tp)   = TupRsingle $ JustVar $ Var tp ZeroIdx
