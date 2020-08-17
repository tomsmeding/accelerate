{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TemplateHaskell #-}
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

module Data.Array.Accelerate.AST.Idx
  where

import Language.Haskell.TH

-- De Bruijn variable index projecting a specific type from a type
-- environment.  Type environments are nested pairs (..((), t1), t2, ..., tn).
--
data Idx env t where
  ZeroIdx ::              Idx (env, t) t
  SuccIdx :: Idx env t -> Idx (env, s) t

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

data PairIdx p a where
  PairIdxLeft  :: PairIdx (a, b) a
  PairIdxRight :: PairIdx (a, b) b


idxToInt :: Idx env t -> Int
idxToInt ZeroIdx       = 0
idxToInt (SuccIdx idx) = 1 + idxToInt idx

rnfIdx :: Idx env t -> ()
rnfIdx ZeroIdx      = ()
rnfIdx (SuccIdx ix) = rnfIdx ix

liftIdx :: Idx env t -> Q (TExp (Idx env t))
liftIdx ZeroIdx      = [|| ZeroIdx ||]
liftIdx (SuccIdx ix) = [|| SuccIdx $$(liftIdx ix) ||]

