{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Array.Accelerate.Trafo.AD (
  convertExp, convertAccWith
) where

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Trafo.Config
import Data.Array.Accelerate.Type
-- import Data.Array.Accelerate.Array.Representation (showArrayR)
import Data.Array.Accelerate.Shows
import qualified Data.Array.Accelerate.Trafo.AD.ADDep as AD
import qualified Data.Array.Accelerate.Trafo.AD.Sink as AD
import qualified Data.Array.Accelerate.Trafo.AD.Translate as AD

import Debug.Trace


convertVar :: Var ArrayR aenv t -> Var ArrayR aenv t
convertVar (Var rep idx) =
  trace ("Exp: Referencing array variable at index: " ++ show (idxToInt idx)) $
    Var rep idx

convertExp :: OpenExp env aenv e -> OpenExp env aenv e
convertExp (Const ty con) = Const ty con
convertExp (PrimApp f e) =
  trace ("Exp: applying primitive " ++ showPrimFun f) $
    PrimApp f (convertExp e)
convertExp (Evar (Var rep idx)) =
  trace ("Exp: Referencing variable at index: " ++ show (idxToInt idx)) $
    Evar (Var rep idx)
convertExp (Let lhs def body) =
  trace ("Exp: Let-assigning to: " ++ showLHS lhs) $
    Let lhs (convertExp def) (convertExp body)
convertExp Nil = Nil
convertExp (Pair e1 e2) = Pair (convertExp e1) (convertExp e2)
convertExp (Shape var) = Shape (convertVar var)
convertExp (Index var dim) = Index (convertVar var) (convertExp dim)
convertExp (GradientE _ sty (Lam lhs (Body body)) arg)
  | SingleScalarType (NumSingleType (FloatingNumType TypeFloat)) <- sty
  , AD.GenLHS lhs' <- AD.generaliseLHS lhs =
      case AD.checkClosedInLHS lhs' (AD.translateExp body) of
          Just transBody
            | AD.ReverseADRes lhs'' body' <- AD.reverseAD lhs' transBody
            , AD.UntranslateResult lhs''' body'' <- AD.untranslateLHSboundExp lhs'' body' ->
                Let lhs''' arg body''
          Nothing ->
              error "Body of gradientE not a closed expression"
  | otherwise =
      error "gradientE expression must produce Float, other types currently unsupported"
convertExp e =
  $internalError "Tom.convertExp" ("Cannot convert Exp node <" ++ showPreExpOp e ++ ">")

convertAccWith :: Config -> Acc arrs -> Acc arrs
convertAccWith _ = convertAcc
-- convertAccWith _ acc@(OpenAcc a) = trace ("ENTRY " ++ showPreAccOp a) $ convertAcc acc

convertAcc :: OpenAcc env arrs -> OpenAcc env arrs
convertAcc (OpenAcc (Unit ty e)) = OpenAcc (Unit ty (convertExp e))
convertAcc (OpenAcc (Map ty f a)) =
  trace "MAP" $
    OpenAcc (Map ty (convertFun f) (convertAcc a))
convertAcc (OpenAcc (Alet lhs def body)) =
  trace ("Let-assigning to: " ++ showLHSA lhs) $
    OpenAcc (Alet lhs (convertAcc def) (convertAcc body))
convertAcc (OpenAcc (Avar (Var rep idx))) =
  trace ("Referencing variable at index: " ++ show (idxToInt idx)) $
    OpenAcc (Avar (Var rep idx))
convertAcc (OpenAcc (Apair a1 a2)) = OpenAcc (Apair (convertAcc a1) (convertAcc a2))
convertAcc (OpenAcc Anil) = OpenAcc Anil
convertAcc (OpenAcc (Use rep a)) = OpenAcc (Use rep a)
convertAcc (OpenAcc (Fold f e a)) = OpenAcc (Fold (convertFun f) (convertExp <$> e) (convertAcc a))
convertAcc (OpenAcc (ZipWith ty f a1 a2)) = OpenAcc (ZipWith ty (convertFun f) (convertAcc a1) (convertAcc a2))
convertAcc (OpenAcc (Permute f a1 fi a2)) = OpenAcc (Permute (convertFun f) (convertAcc a1) (convertFun fi) (convertAcc a2))
convertAcc (OpenAcc (Backpermute rep e f a)) = OpenAcc (Backpermute rep (convertExp e) (convertFun f) (convertAcc a))
convertAcc (OpenAcc (Awhile cond f a)) = OpenAcc (Awhile (convertAfun cond) (convertAfun f) (convertAcc a))
convertAcc (OpenAcc (Replicate rep slice a)) = OpenAcc (Replicate rep (convertExp slice) (convertAcc a))
convertAcc (OpenAcc (Generate rep sz f)) = OpenAcc (Generate rep (convertExp sz) (convertFun f))
convertAcc (OpenAcc acc) =
  $internalError "Tom.convertAcc" ("Cannot convert Acc node <" ++ showPreAccOp acc ++ ">")

convertFun :: OpenFun env aenv t -> OpenFun env aenv t
convertFun (Lam lhs f) = Lam lhs (convertFun f)
convertFun (Body e) = Body (convertExp e)

convertAfun :: PreOpenAfun OpenAcc aenv t -> PreOpenAfun OpenAcc aenv t
convertAfun (Alam lhs f) = Alam lhs (convertAfun f)
convertAfun (Abody a) = Abody (convertAcc a)