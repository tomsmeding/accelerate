{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Array.Accelerate.Trafo.AD (
  convertExp, convertAccEntry, convertAfunEntry
) where

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Pretty.NoTrafo ()
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import qualified Data.Array.Accelerate.Trafo.AD.ADAcc as AD
import qualified Data.Array.Accelerate.Trafo.AD.ADExp as AD
import Data.Array.Accelerate.Trafo.AD.Debug
import qualified Data.Array.Accelerate.Trafo.AD.Exp as AD
import qualified Data.Array.Accelerate.Trafo.AD.Simplify as AD
import qualified Data.Array.Accelerate.Trafo.AD.Sink as AD
import qualified Data.Array.Accelerate.Trafo.AD.Translate as AD
import Data.Array.Accelerate.Trafo.Substitution (rebuildLHS)


convertExp :: OpenExp env aenv e -> OpenExp env aenv e
convertExp (Const ty con) = Const ty con
convertExp (PrimApp f e) = PrimApp f (convertExp e)
convertExp (PrimConst c) = PrimConst c
convertExp (Evar (Var rep idx)) = Evar (Var rep idx)
convertExp (Let lhs def body) = Let lhs (convertExp def) (convertExp body)
convertExp (Foreign ty func alt e) = Foreign ty func (convertFun alt) (convertExp e)
convertExp Nil = Nil
convertExp (Pair e1 e2) = Pair (convertExp e1) (convertExp e2)
convertExp (VecPack ty e) = VecPack ty (convertExp e)
convertExp (VecUnpack ty e) = VecUnpack ty (convertExp e)
convertExp (IndexSlice slty ix e) = IndexSlice slty (convertExp ix) (convertExp e)
convertExp (IndexFull slty ix e) = IndexFull slty (convertExp ix) (convertExp e)
convertExp (ToIndex ty she ixe) = ToIndex ty (convertExp she) (convertExp ixe)
convertExp (FromIndex ty she ixe) = FromIndex ty (convertExp she) (convertExp ixe)
convertExp (Case e es def) =
    Case (convertExp e) (map (fmap convertExp) es) (convertExp <$> def)
convertExp (Cond c e1 e2) = Cond (convertExp c) (convertExp e1) (convertExp e2)
convertExp (While c f e) = While (convertFun c) (convertFun f) (convertExp e)
convertExp (Index var dim) = Index var (convertExp dim)
convertExp (LinearIndex var dim) = LinearIndex var (convertExp dim)
convertExp (Shape var) = Shape var
convertExp (ShapeSize shr e) = ShapeSize shr (convertExp e)
convertExp (Undef ty) = Undef ty
convertExp (Coerce t1 t2 e) = Coerce t1 t2 (convertExp e)
convertExp (GradientE _ sty (Lam lhs (Body body)) arg)
  | SingleScalarType (NumSingleType (FloatingNumType TypeFloat)) <- sty
  , AD.Lam _ (AD.Body transBody) <- AD.translateFun (Lam lhs (Body body))
  , Exists lhs1 <- rebuildLHS lhs =
      case AD.eCheckClosedInLHS lhs1 transBody of
          Just transBody'
            | AD.ReverseADResE lhs2 body' <- AD.reverseAD lhs1 (transBody' `withAlabType` ())
            , AD.UntranslateResultE lhs3 body'' <- AD.untranslateLHSboundExp lhs2 (AD.simplifyExp body') (Just weakenId) ->
                Let lhs3 arg body''
          Nothing ->
              error "Body of gradientE not a closed expression"
  | otherwise =
      error "gradientE expression must produce Float, other types currently unsupported"
  where
    withAlabType :: AD.OpenExp env aenv lab alab args tenv t -> alab -> AD.OpenExp env aenv lab alab args tenv t
    withAlabType = const
convertExp e =
  internalError ("convertExp: Cannot convert Exp node <" ++ showExpOp e ++ ">")

convertAccEntry :: Acc arrs -> Acc arrs
convertAccEntry a =
    let result = convertAcc (trace ("Computation before AD pass:\n" ++ show a) a)
    in trace ("Computation after AD pass:\n" ++ show result ++ "\n") result

convertAfunEntry :: Afun t -> Afun t
convertAfunEntry a =
    let result = convertAfun (trace ("\nComputation before AD pass: [run1 FUNCTION]\n" ++ show a) a)
    in trace ("Computation after AD pass: [run1 FUNCTION]\n" ++ show result ++ "\n") result

convertAcc :: OpenAcc env arrs -> OpenAcc env arrs
convertAcc (OpenAcc a) = OpenAcc (convertPAcc a)

convertPAcc :: PreOpenAcc OpenAcc env arrs -> PreOpenAcc OpenAcc env arrs
convertPAcc (Unit ty e) = Unit ty (convertExp e)
convertPAcc (Map ty f a) = Map ty (convertFun f) (convertAcc a)
convertPAcc (Alet lhs def body) = Alet lhs (convertAcc def) (convertAcc body)
convertPAcc (Avar (Var rep idx)) = Avar (Var rep idx)
convertPAcc (Apair a1 a2) = Apair (convertAcc a1) (convertAcc a2)
convertPAcc Anil = Anil
convertPAcc (Apply ty f a) = Apply ty (convertAfun f) (convertAcc a)
convertPAcc (Aforeign ty func alt a) = Aforeign ty func (convertAfun alt) (convertAcc a)
convertPAcc (Reshape shr she a) = Reshape shr (convertExp she) (convertAcc a)
convertPAcc (Use rep a) = Use rep a
convertPAcc (Fold f e a) = Fold (convertFun f) (convertExp <$> e) (convertAcc a)
convertPAcc (FoldSeg ty f e a1 a2) =
    FoldSeg ty (convertFun f) (convertExp <$> e) (convertAcc a1) (convertAcc a2)
convertPAcc (Scan dir f e a) = Scan dir (convertFun f) (convertExp <$> e) (convertAcc a)
convertPAcc (Scan' dir f e a) = Scan' dir (convertFun f) (convertExp e) (convertAcc a)
convertPAcc (ZipWith ty f a1 a2) = ZipWith ty (convertFun f) (convertAcc a1) (convertAcc a2)
convertPAcc (Permute f a1 fi a2) = Permute (convertFun f) (convertAcc a1) (convertFun fi) (convertAcc a2)
convertPAcc (Backpermute rep e f a) = Backpermute rep (convertExp e) (convertFun f) (convertAcc a)
convertPAcc (Acond cond a1 a2) = Acond (convertExp cond) (convertAcc a1) (convertAcc a2)
convertPAcc (Awhile cond f a) = Awhile (convertAfun cond) (convertAfun f) (convertAcc a)
convertPAcc (Replicate rep slice a) = Replicate rep (convertExp slice) (convertAcc a)
convertPAcc (Slice slix a e) = Slice slix (convertAcc a) (convertExp e)
convertPAcc (Generate rep sz f) = Generate rep (convertExp sz) (convertFun f)
convertPAcc (Transform ty dim ixf vf a) =
    Transform ty (convertExp dim) (convertFun ixf) (convertFun vf) (convertAcc a)
convertPAcc (Stencil rep ty f bnd a) = Stencil rep ty (convertFun f) (convertBoundary bnd) (convertAcc a)
convertPAcc (Stencil2 r1 r2 ty f b1 a1 b2 a2) =
    Stencil2 r1 r2 ty (convertFun f) (convertBoundary b1) (convertAcc a1) (convertBoundary b2) (convertAcc a2)
convertPAcc (GradientA _ sty (Alam lhs (Abody body)) arg)
  | ArrayR ShapeRz (TupRsingle (SingleScalarType (NumSingleType (FloatingNumType TypeFloat)))) <- sty
  , Exists lhs' <- rebuildLHS lhs =
      case AD.aCheckClosedInLHS lhs' (AD.translateAcc body) of
          Just transBody
            | AD.ReverseADResA lhs'' body' <- AD.reverseADA lhs' transBody
            , AD.UntranslateResultA lhs''' body'' <- AD.untranslateLHSboundAcc lhs'' (AD.simplifyAcc body') ->
                Alet lhs''' arg body''
          Nothing ->
              error "Body of gradientA not a closed expression"
  | otherwise =
      error $ "gradientA expression must produce (Array Z Float), other types currently unsupported: " ++ show sty
convertPAcc (GradientA _ _ _ _) = error "GradientA is being worked on!"

convertFun :: OpenFun env aenv t -> OpenFun env aenv t
convertFun (Lam lhs f) = Lam lhs (convertFun f)
convertFun (Body e) = Body (convertExp e)

convertAfun :: PreOpenAfun OpenAcc aenv t -> PreOpenAfun OpenAcc aenv t
convertAfun (Alam lhs f) = Alam lhs (convertAfun f)
convertAfun (Abody a) = Abody (convertAcc a)

convertBoundary :: Boundary aenv (Array sh a) -> Boundary aenv (Array sh a)
convertBoundary bnd@Clamp = bnd
convertBoundary bnd@Mirror = bnd
convertBoundary bnd@Wrap = bnd
convertBoundary bnd@(Constant _) = bnd
convertBoundary (Function f) = Function (convertFun f)
