{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE OverloadedStrings    #-}
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

module Data.Array.Accelerate.Pretty.NoTrafo (

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

import Data.Array.Accelerate.AST                                    hiding ( Acc, Exp )
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Pretty.Graphviz
import Data.Array.Accelerate.Pretty.Print                           hiding ( Keyword(..) )
import Data.Array.Accelerate.Trafo.Delayed

import Data.Maybe
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String
import Data.Text.Prettyprint.Doc.Render.Terminal
import System.Environment
import System.IO
import System.IO.Unsafe
import qualified Data.Text.Lazy                                     as T
import qualified System.Console.ANSI                                as Term
import qualified System.Console.Terminal.Size                       as Term


-- Note: [Show instances]
--
-- Explicitly enumerate Show instances for the Accelerate array AST types.
-- If we instead use a generic instance of the form:
--
--   instance Kit acc => Show (acc aenv a) where
--
-- This matches any type of kind (* -> * -> *), which can cause problems
-- interacting with other packages. See Issue #108.
--

instance PrettyEnv aenv => Show (OpenAcc aenv a) where
  show = renderForTerminal . prettyOpenAcc context0 (prettyEnv (pretty 'a'))

instance PrettyEnv aenv => Show (OpenAfun aenv f) where
  show = renderForTerminal . prettyPreOpenAfun prettyOpenAcc (prettyEnv (pretty 'a'))

instance PrettyEnv aenv => Show (DelayedOpenAcc aenv a) where
  show = renderForTerminal . prettyDelayedOpenAcc context0 (prettyEnv (pretty 'a'))

instance PrettyEnv aenv => Show (DelayedOpenAfun aenv f) where
  show = renderForTerminal . prettyPreOpenAfun prettyDelayedOpenAcc (prettyEnv (pretty 'a'))

instance (PrettyEnv env, PrettyEnv aenv) => Show (OpenExp env aenv e) where
  show = renderForTerminal . prettyOpenExp context0 (prettyEnv (pretty 'x')) (prettyEnv (pretty 'a'))

instance (PrettyEnv env, PrettyEnv aenv) => Show (OpenFun env aenv e) where
  show = renderForTerminal . prettyOpenFun (prettyEnv (pretty 'x')) (prettyEnv (pretty 'a'))


-- Internals
-- ---------

renderForTerminal :: Adoc  -> String
renderForTerminal = render . layoutSmart terminalLayoutOptions
  where
    fancy = terminalSupportsANSI && terminalColourAllowed
    render
      | fancy     = T.unpack . renderLazy . reAnnotateS ansiKeyword
      | otherwise = renderString

{-# NOINLINE terminalColourAllowed #-}
terminalColourAllowed :: Bool
terminalColourAllowed = unsafePerformIO $ isNothing <$> lookupEnv "NO_COLOR"

{-# NOINLINE terminalSupportsANSI #-}
terminalSupportsANSI :: Bool
terminalSupportsANSI = unsafePerformIO $ Term.hSupportsANSI stdout

{-# NOINLINE terminalLayoutOptions #-}
terminalLayoutOptions :: LayoutOptions
terminalLayoutOptions
  = unsafePerformIO
  $ do term <- Term.size
       return $ case term of
                  Nothing -> defaultLayoutOptions
                  Just t  -> LayoutOptions { layoutPageWidth = AvailablePerLine (min w 120) f }
                    where
                      w = Term.width t
                      f | w <= 80   = 1
                        | w <= 100  = 0.9
                        | otherwise = 0.8

prettyOpenAcc :: PrettyAcc OpenAcc
prettyOpenAcc context aenv (OpenAcc pacc) =
  prettyPreOpenAcc context prettyOpenAcc extractOpenAcc aenv pacc

extractOpenAcc :: OpenAcc aenv a -> PreOpenAcc OpenAcc aenv a
extractOpenAcc (OpenAcc pacc) = pacc


prettyDelayedOpenAcc :: HasCallStack => PrettyAcc DelayedOpenAcc
prettyDelayedOpenAcc context aenv (Manifest pacc)
  = prettyPreOpenAcc context prettyDelayedOpenAcc extractDelayedOpenAcc aenv pacc
prettyDelayedOpenAcc _       aenv (Delayed _ sh f _)
  = parens
  $ nest shiftwidth
  $ sep [ delayed "delayed"
        ,          prettyOpenExp app Empty aenv sh
        , parens $ prettyOpenFun     Empty aenv f
        ]

extractDelayedOpenAcc :: HasCallStack => DelayedOpenAcc aenv a -> PreOpenAcc DelayedOpenAcc aenv a
extractDelayedOpenAcc (Manifest pacc) = pacc
extractDelayedOpenAcc Delayed{}       = internalError "expected manifest array"
