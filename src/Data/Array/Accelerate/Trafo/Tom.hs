{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
module Data.Array.Accelerate.Trafo.Tom (
  convertExp, convertAccWith
) where

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Trafo.Config

import Debug.Trace


convertExp :: PreOpenExp OpenAcc () () e -> PreOpenExp OpenAcc () () e
convertExp e = case e of
  Const ty con -> Const ty con
  _            -> e

convertAccWith :: Config -> Acc arrs -> Acc arrs
convertAccWith _ (OpenAcc (Unit ty e)) = OpenAcc (Unit ty (convertExp e))
convertAccWith _ (OpenAcc acc) =
  $internalError "Tom.convertAccWith" ("Cannot convert Acc node <" ++ showPreAccOp acc ++ ">")
