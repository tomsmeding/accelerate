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

  -- ** Poor pretty printing
  poorShow,

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

import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Var


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
  = prettyPreOpenAccWithHash context prettyDelayedOpenAcc extractDelayedOpenAcc aenv pacc
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


-- PSE (names in environment) (name generation seed)
data PoorShowEnv = PSE [String] Int

-- PSR (output name generation seed)
data PoorShowRet = PSR Int

poorShow :: OpenAcc aenv t -> String
poorShow = snd . poorShow' (PSE [] 0)

poorShow' :: PoorShowEnv -> OpenAcc aenv t -> (PoorShowRet, String)
poorShow' env (OpenAcc pacc) = poorShowP env pacc

poorShowP :: PoorShowEnv -> PreOpenAcc OpenAcc aenv t -> (PoorShowRet, String)
poorShowP env@(PSE envnames seed) = \pacc -> case pacc of
  Alet lhs bnd body ->
    let (PSE envnames' seed1, lhsS) = poorShowLHS env lhs
        (PSR seed2, bndS) = poorShow' (PSE envnames seed1) bnd
        (PSR seed3, bodyS) = poorShow' (PSE envnames' seed2) body
    in (PSR seed3, "(let " ++ lhsS ++ " = " ++ bndS ++ " in " ++ bodyS ++ ")")

  Avar (Var _ idx) ->
    let i = idxToInt idx
    in case drop i envnames of
         [] -> (PSR seed, "aUP" ++ show (i - length envnames + 1))
         n : _ -> (PSR seed, n)

  Use _ _ ->
    (PSR seed, "(use _)")

  Generate _ _ _ ->
    (PSR seed, "(generate _ _)")

  Map _ _ a ->
    let (PSR seed1, aS) = poorShow' env a
    in (PSR seed1, "(map _ " ++ aS ++ ")")

  ZipWith _ _ a1 a2 ->
    let (PSR seed1, a1S) = poorShow' env a1
        (PSR seed2, a2S) = poorShow' (PSE envnames seed1) a2
    in (PSR seed2, "(zipWith _ " ++ a1S ++ " " ++ a2S ++ ")")

  _ -> (PSR seed, "(" ++ showPreAccOp pacc ++ "??)")

poorShowLHS :: PoorShowEnv -> ALeftHandSide t aenv aenv' -> (PoorShowEnv, String)
poorShowLHS env@(PSE envnames seed) = \lhs -> case lhs of
  LeftHandSideWildcard _ -> (env, "_")
  LeftHandSideSingle _ -> let name = genName seed
                          in (PSE (name : envnames) (seed + 1), name)
  LeftHandSidePair lhs1 lhs2 ->
    let (env1, s1) = poorShowLHS env lhs1
        (env2, s2) = poorShowLHS env1 lhs2
    in (env2, "(" ++ s1 ++ ", " ++ s2 ++ ")")
  where
    genName i = 'a' : show i
