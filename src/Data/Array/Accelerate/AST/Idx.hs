{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.AST.Idx
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Typed de Bruijn indices
--

module Data.Array.Accelerate.AST.Idx (

  Idx, pattern ZeroIdx, pattern SuccIdx, pattern VoidIdx,
  idxToInt,
  rnfIdx, liftIdx,

  PairIdx(..)

) where

import Data.GADT.Compare
import Language.Haskell.TH ( Q, TExp )
import Data.Type.Equality ((:~:)(Refl))

#ifndef ACCELERATE_INTERNAL_CHECKS
import Unsafe.Coerce (unsafeCoerce)
#endif

#ifdef ACCELERATE_INTERNAL_CHECKS

-- | De Bruijn variable index projecting a specific type from a type
-- environment.  Type environments are nested pairs (..((), t1), t2, ..., tn).
--
data Idx env t where
  ZeroIdx ::              Idx (env, t) t
  SuccIdx :: Idx env t -> Idx (env, s) t

idxToInt :: Idx env t -> Int
idxToInt ZeroIdx       = 0
idxToInt (SuccIdx idx) = 1 + idxToInt idx

rnfIdx :: Idx env t -> ()
rnfIdx ZeroIdx      = ()
rnfIdx (SuccIdx ix) = rnfIdx ix

liftIdx :: Idx env t -> Q (TExp (Idx env t))
liftIdx ZeroIdx      = [|| ZeroIdx ||]
liftIdx (SuccIdx ix) = [|| SuccIdx $$(liftIdx ix) ||]

instance GEq (Idx env) where
    geq ZeroIdx ZeroIdx = Just Refl
    geq (SuccIdx i1) (SuccIdx i2)
      | Just Refl <- geq i1 i2
      = Just Refl
    geq _ _ = Nothing

instance GCompare (Idx env) where
    gcompare ZeroIdx ZeroIdx = GEQ
    gcompare (SuccIdx i1) (SuccIdx i2) = gcompare i1 i2
    gcompare ZeroIdx (SuccIdx _) = GLT
    gcompare (SuccIdx _) ZeroIdx = GGT

#else

-- | De Bruijn variable index projecting a specific type from a type
-- environment.  Type environments are nested pairs (..((), t1), t2, ..., tn).
--
-- Outside of this file, pretend that this is an ordinary GADT:
-- data Idx env t where
--   ZeroIdx ::              Idx (env, t) t
--   SuccIdx :: Idx env t -> Idx (env, s) t
--
-- For performance, it uses an Int under the hood.
newtype Idx env t = UnsafeIdxConstructor { unsafeRunIdx :: Int }

{-# COMPLETE ZeroIdx, SuccIdx #-}

pattern ZeroIdx :: forall env envt t. () => (envt ~ (env, t)) => Idx envt t
pattern ZeroIdx <- (\x -> (idxToInt x, unsafeCoerce @(envt :~: envt) @(envt :~: (env, t)) Refl) -> (0, Refl))
  where
    ZeroIdx = UnsafeIdxConstructor 0

pattern SuccIdx :: () => (envs ~ (env, s)) => Idx env t -> Idx envs t
pattern SuccIdx idx <- (unSucc -> Just (idx, Refl))
  where
    SuccIdx (UnsafeIdxConstructor i) = UnsafeIdxConstructor (i+1)

unSucc :: Idx envs t -> Maybe (Idx env t, envs :~: (env, s))
unSucc (UnsafeIdxConstructor i)
  | i < 1     = Nothing
  | otherwise = Just (UnsafeIdxConstructor (i-1), unsafeCoerce Refl)

idxToInt :: Idx env t -> Int
idxToInt = unsafeRunIdx

rnfIdx :: Idx env t -> ()
rnfIdx !_ = ()

liftIdx :: Idx env t -> Q (TExp (Idx env t))
liftIdx (UnsafeIdxConstructor i) = [|| UnsafeIdxConstructor i ||]

instance GEq (Idx env) where
    geq (UnsafeIdxConstructor n) (UnsafeIdxConstructor m)
      | n == m = Just (unsafeCoerce Refl)
      | otherwise = Nothing

instance GCompare (Idx env) where
    gcompare (UnsafeIdxConstructor n) (UnsafeIdxConstructor m) =
      case compare n m of
        LT -> GLT
        EQ -> unsafeCoerce GEQ
        GT -> GGT

#endif

-- | Despite the 'complete' pragma above, GHC can't infer that there is no
-- pattern possible if the environment is empty. This can be used instead.
pattern VoidIdx :: forall env t a. (env ~ ()) => () => a -> Idx env t
pattern VoidIdx a <- (\case{} -> a)

data PairIdx p a where
  PairIdxLeft  :: PairIdx (a, b) a
  PairIdxRight :: PairIdx (a, b) b

