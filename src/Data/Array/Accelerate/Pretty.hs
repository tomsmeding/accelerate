{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Pretty
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pretty (

  -- ** Pretty printing
  PrettyAcc, ExtractAcc,
  prettyPreOpenAcc,
  prettyPreOpenAfun,
  prettyOpenExp,
  prettyOpenFun,

  -- ** Graphviz
  Graph,
  PrettyGraph(..), Detail(..),
  graphDelayedAcc, graphDelayedAfun,

) where

import Data.Array.Accelerate.Smart                                  ( Acc, Exp )
import Data.Array.Accelerate.Sugar.Array
import Data.Array.Accelerate.Sugar.Elt
import Data.Array.Accelerate.Trafo
import Data.Array.Accelerate.Pretty.NoTrafo

#if ACCELERATE_DEBUG
import Control.DeepSeq
import Data.Array.Accelerate.Debug.Flags
import Data.Array.Accelerate.Debug.Stats
import System.IO.Unsafe
#endif


instance Arrays arrs => Show (Acc arrs) where
  show = withSimplStats . show . convertAcc

instance Afunction (Acc a -> f) => Show (Acc a -> f) where
  show = withSimplStats . show . convertAfun

instance Elt e => Show (Exp e) where
  show = withSimplStats . show . convertExp

instance Function (Exp a -> f) => Show (Exp a -> f) where
  show = withSimplStats . show . convertFun

-- instance Typeable a => Show (Seq a) where
--   show = withSimplStats . show . convertSeq


-- Debugging
-- ---------

-- Attach simplifier statistics to the tail of the given string. Since the
-- statistics rely on fully evaluating the expression this is difficult to do
-- generally (without an additional deepseq), but easy enough for our show
-- instances.
--
-- For now, we just reset the statistics at the beginning of a conversion, and
-- leave it to a backend to choose an appropriate moment to dump the summary.
--
withSimplStats :: String -> String
#ifdef ACCELERATE_DEBUG
withSimplStats x = unsafePerformIO $ do
  when dump_simpl_stats $ x `deepseq` dumpSimplStats
  return x
#else
withSimplStats x = x
#endif

