{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Array.Accelerate.Trafo.AD (
  convertExp, convertAccWith
) where

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Error
-- import Data.Array.Accelerate.Pretty.NoTrafo ()
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Trafo.Config
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import qualified Data.Array.Accelerate.Trafo.AD.ADAcc as AD
import qualified Data.Array.Accelerate.Trafo.AD.ADExp as AD
import qualified Data.Array.Accelerate.Trafo.AD.Exp as AD
import qualified Data.Array.Accelerate.Trafo.AD.Sink as AD
import qualified Data.Array.Accelerate.Trafo.AD.Translate as AD

-- import Debug.Trace


convertExp :: OpenExp env aenv e -> OpenExp env aenv e
convertExp (Const ty con) = Const ty con
convertExp (PrimApp f e) = PrimApp f (convertExp e)
convertExp (Evar (Var rep idx)) = Evar (Var rep idx)
convertExp (Let lhs def body) = Let lhs (convertExp def) (convertExp body)
convertExp Nil = Nil
convertExp (Pair e1 e2) = Pair (convertExp e1) (convertExp e2)
convertExp (Shape var) = Shape var
convertExp (Index var dim) = Index var (convertExp dim)
convertExp (ShapeSize shr e) = ShapeSize shr (convertExp e)
convertExp (GradientE _ sty (Lam lhs (Body body)) arg)
  | SingleScalarType (NumSingleType (FloatingNumType TypeFloat)) <- sty
  , AD.GenLHS lhs' <- AD.generaliseLHS lhs =
      case AD.eCheckClosedInLHS lhs' (AD.translateExp body) of
          Just transBody
            | AD.ReverseADResE lhs'' body' <- AD.reverseAD lhs' (transBody `withAlabType` ())
            , AD.UntranslateResultE lhs''' body'' <- AD.untranslateLHSboundExp lhs'' body' ->
                Let lhs''' arg body''
          Nothing ->
              error "Body of gradientE not a closed expression"
  | otherwise =
      error "gradientE expression must produce Float, other types currently unsupported"
  where
    withAlabType :: AD.OpenExp env aenv lab alab args t -> alab -> AD.OpenExp env aenv lab alab args t
    withAlabType = const
convertExp e =
  internalError ("convertExp: Cannot convert Exp node <" ++ showExpOp e ++ ">")

convertAccWith :: Config -> Acc arrs -> Acc arrs
convertAccWith _ = convertAcc
-- convertAccWith _ a = convertAcc (traceShowId a)

convertAcc :: OpenAcc env arrs -> OpenAcc env arrs
convertAcc (OpenAcc (Unit ty e)) = OpenAcc (Unit ty (convertExp e))
convertAcc (OpenAcc (Map ty f a)) = OpenAcc (Map ty (convertFun f) (convertAcc a))
convertAcc (OpenAcc (Alet lhs def body)) = OpenAcc (Alet lhs (convertAcc def) (convertAcc body))
convertAcc (OpenAcc (Avar (Var rep idx))) = OpenAcc (Avar (Var rep idx))
convertAcc (OpenAcc (Apair a1 a2)) = OpenAcc (Apair (convertAcc a1) (convertAcc a2))
convertAcc (OpenAcc Anil) = OpenAcc Anil
convertAcc (OpenAcc (Apply ty f a)) = OpenAcc (Apply ty (convertAfun f) (convertAcc a))
convertAcc (OpenAcc (Reshape shr she a)) = OpenAcc (Reshape shr (convertExp she) (convertAcc a))
convertAcc (OpenAcc (Use rep a)) = OpenAcc (Use rep a)
convertAcc (OpenAcc (Fold f e a)) = OpenAcc (Fold (convertFun f) (convertExp <$> e) (convertAcc a))
convertAcc (OpenAcc (ZipWith ty f a1 a2)) = OpenAcc (ZipWith ty (convertFun f) (convertAcc a1) (convertAcc a2))
convertAcc (OpenAcc (Permute f a1 fi a2)) = OpenAcc (Permute (convertFun f) (convertAcc a1) (convertFun fi) (convertAcc a2))
convertAcc (OpenAcc (Backpermute rep e f a)) = OpenAcc (Backpermute rep (convertExp e) (convertFun f) (convertAcc a))
convertAcc (OpenAcc (Awhile cond f a)) = OpenAcc (Awhile (convertAfun cond) (convertAfun f) (convertAcc a))
convertAcc (OpenAcc (Replicate rep slice a)) = OpenAcc (Replicate rep (convertExp slice) (convertAcc a))
convertAcc (OpenAcc (Generate rep sz f)) = OpenAcc (Generate rep (convertExp sz) (convertFun f))
convertAcc (OpenAcc (GradientA _ sty (Alam lhs (Abody body)) arg))
  | ArrayR ShapeRz (TupRsingle (SingleScalarType (NumSingleType (FloatingNumType TypeFloat)))) <- sty
  , AD.GenLHS lhs' <- AD.generaliseLHS lhs =
      case AD.aCheckClosedInLHS lhs' (AD.translateAcc body) of
          Just transBody
            | AD.ReverseADResA lhs'' body' <- AD.reverseADA lhs' transBody
            , AD.UntranslateResultA lhs''' body'' <- AD.untranslateLHSboundAcc lhs'' body' ->
                OpenAcc (Alet lhs''' arg body'')
          Nothing ->
              error "Body of gradientA not a closed expression"
  | otherwise =
      error $ "gradientA expression must produce (Array Z Float), other types currently unsupported: " ++ show sty
convertAcc (OpenAcc acc) =
  internalError ("convertAcc: Cannot convert Acc node <" ++ showPreAccOp acc ++ ">")

convertFun :: OpenFun env aenv t -> OpenFun env aenv t
convertFun (Lam lhs f) = Lam lhs (convertFun f)
convertFun (Body e) = Body (convertExp e)

convertAfun :: PreOpenAfun OpenAcc aenv t -> PreOpenAfun OpenAcc aenv t
convertAfun (Alam lhs f) = Alam lhs (convertAfun f)
convertAfun (Abody a) = Abody (convertAcc a)
