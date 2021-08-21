{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Accelerate.Trafo.AD (
  convertExpEntry, convertFunEntry,
  convertAccEntry, convertAfunEntry
) where

import Data.String (fromString)
import System.IO.Unsafe (unsafePerformIO)

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Pretty.NoTrafo ()
import Data.Array.Accelerate.Representation.Array
import qualified Data.Array.Accelerate.Trafo.AD.Acc as AD
import qualified Data.Array.Accelerate.Trafo.AD.ADAcc as AD
import qualified Data.Array.Accelerate.Trafo.AD.ADExp as AD
import Data.Array.Accelerate.Trafo.AD.Debug
import qualified Data.Array.Accelerate.Trafo.AD.Common as AD
import qualified Data.Array.Accelerate.Trafo.AD.Config as AD
import qualified Data.Array.Accelerate.Trafo.AD.Exp as AD
import qualified Data.Array.Accelerate.Trafo.AD.Graph as AD
import qualified Data.Array.Accelerate.Trafo.AD.Simplify as AD
import qualified Data.Array.Accelerate.Trafo.AD.Translate as AD
import Data.Array.Accelerate.Trafo.Substitution (weaken, weakenE)
import Data.Array.Accelerate.Trafo.Var


-- Conversion of expressions
-- -------------------------

convertExpEntry :: Exp aenv t -> Exp aenv t
convertExpEntry a = elimCustomsE (convertExp a)

convertFunEntry :: Fun aenv t -> Fun aenv t
convertFunEntry a = elimCustomsFun (convertFun a)

convertExp :: OpenExp env aenv e -> OpenExp env aenv e
convertExp (Const ty con) = Const ty con
convertExp (PrimApp f e) = PrimApp f (convertExp e)
convertExp (PrimConst c) = PrimConst c
convertExp (Evar var) = Evar var
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
convertExp (Evjp _ _ (convertFun -> Lam lhs (Body body)) (convertExp -> arg) (convertExp -> adj))
  -- Target is to replace the Evjp with an expression of the following form:
  --   let _ = adj
  --   in let _ = arg
  --      in gradient_body
  -- We do this because we wish to have the 'let _ = arg in gradient_body' form
  -- that comes out of AD, but we also wish to be able to pass 'adj' to AD
  -- without having to translate it to the AD AST. Hence we bind it and pass a
  -- tuple of FreeVar nodes to AD.

  -- First declare variables for the adjoint...
  | DeclareVars adjlhs _ adjvarsgen <- declareVars (expType adj)
  -- ... and we construct the tuple of FreeVar nodes that will be bound to this LHS.
  , let adj' = AD.RelocatableExp $ AD.untupleExps $
                 AD.fmapTupR (\var@(Var ty _) -> AD.FreeVar (AD.nilLabel ty) var)
                             (adjvarsgen weakenId)
  -- Then we translate the original function, after shifting it under the new adjoint let binding;
  -- the result is suspended under adjlhs and lhs1.
  , AD.Lam lhs1 (AD.Body transBody) <- AD.translateFun (weakenE (weakenWithLHS adjlhs) $ Lam lhs (Body body))
  -- Possibly we simplify beforehand, depending on config.
  , let simplifiedBody = if AD.getConfigVar AD.PreOpt then AD.simplifyExp transBody else transBody
  -- Then we do the actual differentiation on the simplified body; the result is suspended under
  -- adjlhs and lhs2.
  , AD.ReverseADResE lhs2 body' <- AD.reverseAD lhs1 (simplifiedBody `withAlabType` ()) adj'
  -- Finally we translate back to the main AST, suspending under adjlhs and lhs3.
  , AD.UntranslateResultE lhs3 body'' <- AD.untranslateLHSboundExp lhs2 (AD.simplifyExp body') weakenId weakenId
  -- Thus we construct the result.
  = Let adjlhs adj $ Let lhs3 (weakenE (weakenWithLHS adjlhs) arg) body''
  where
    withAlabType :: AD.OpenExp env aenv lab alab args tenv taenv t -> alab -> AD.OpenExp env aenv lab alab args tenv taenv t
    withAlabType = const
convertExp (Evjp _ _ _ _ _) =
  internalError (fromString "convertExp: Invalid GADTs in Evjp")
convertExp (EcustomDeriv ty fun der a) = EcustomDeriv ty (convertFun fun) (convertFun der) (convertExp a)

convertFun :: OpenFun env aenv t -> OpenFun env aenv t
convertFun (Lam lhs f) = Lam lhs (convertFun f)
convertFun (Body e) = Body (convertExp e)


-- Conversion of array programs
-- ----------------------------

convertAccEntry :: Acc arrs -> Acc arrs
convertAccEntry a =
    let result = elimCustomsA (convertAcc (trace ("Computation before AD pass:\n" ++ show a) a))
    in trace ("Computation after AD pass:\n" ++ show result ++ "\n") result

convertAfunEntry :: Afun t -> Afun t
convertAfunEntry a =
    let result = elimCustomsAfun (convertAfun (trace ("\nComputation before AD pass: [run1 FUNCTION]\n" ++ show a) a))
    in trace ("Computation after AD pass: [run1 FUNCTION]\n" ++ show result ++ "\n") result

convertAcc :: OpenAcc env arrs -> OpenAcc env arrs
convertAcc (OpenAcc a) = OpenAcc (convertPAcc a)

convertPAcc :: PreOpenAcc OpenAcc env arrs -> PreOpenAcc OpenAcc env arrs
convertPAcc (Unit ty e) = Unit ty (convertExp e)
convertPAcc (Map ty f a) = Map ty (convertFun f) (convertAcc a)
convertPAcc (Alet lhs def body) = Alet lhs (convertAcc def) (convertAcc body)
convertPAcc (Avar var) = Avar var
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
convertPAcc (Atrace msg a1 a2) = Atrace msg (convertAcc a1) (convertAcc a2)
convertPAcc (Replicate rep slice a) = Replicate rep (convertExp slice) (convertAcc a)
convertPAcc (Slice slix a e) = Slice slix (convertAcc a) (convertExp e)
convertPAcc (Generate rep sz f) = Generate rep (convertExp sz) (convertFun f)
convertPAcc (Transform ty dim ixf vf a) =
    Transform ty (convertExp dim) (convertFun ixf) (convertFun vf) (convertAcc a)
convertPAcc (Stencil rep ty f bnd a) = Stencil rep ty (convertFun f) (convertBoundary bnd) (convertAcc a)
convertPAcc (Stencil2 r1 r2 ty f b1 a1 b2 a2) =
    Stencil2 r1 r2 ty (convertFun f) (convertBoundary b1) (convertAcc a1) (convertBoundary b2) (convertAcc a2)
convertPAcc (Avjp _ _ (convertAfun -> Alam lhs (Abody body)) (convertAcc -> arg) (convertAcc -> adj))
  -- First declare variables for the adjoint...
  | DeclareVars adjlhs _ adjvarsgen <- declareVars (arraysR adj)
  -- ... and we construct the tuple of FreeVar nodes that will be bound to this LHS.
  , let adj' = adjvarsgen weakenId
  -- Then we translate the original function, after shifting it under the new adjoint let binding;
  -- the result is suspended under adjlhs and lhs1.
  , AD.Alam lhs1 (AD.Abody transBody) <- AD.translateAfun (weaken (weakenWithLHS adjlhs) $ Alam lhs (Abody body))
  -- Possibly we simplify beforehand, depending on config.
  , let simplifiedBody = if AD.getConfigVar AD.PreOpt then AD.simplifyAcc transBody else transBody
  -- Possibly we write a graph, depending on config.
  , () <- case AD.getConfigVar AD.Graph of
            "" -> ()
            fname -> unsafePerformIO (AD.writeGraphToFile fname lhs1 simplifiedBody)
  -- Then we do the actual differentiation on the simplified body; the result is suspended under
  -- adjlhs and lhs2.
  , AD.ReverseADResA lhs2 body' <- AD.reverseADA lhs1 simplifiedBody adj'
  -- Finally we translate back to the main AST, suspending under adjlhs and lhs3.
  , AD.UntranslateResultA lhs3 body'' <- AD.untranslateLHSboundAcc lhs2 (AD.simplifyAcc body') weakenId
  -- Thus we construct the result.
  = Alet adjlhs adj $ OpenAcc $ Alet lhs3 (weaken (weakenWithLHS adjlhs) arg) body''
convertPAcc (Avjp _ _ _ _ _) =
  internalError (fromString "convertPAcc: Invalid GADTs in Avjp")
-- Eliminate custom derivative nodes outside an Avjp subtree
convertPAcc (AcustomDeriv t fun der a) = AcustomDeriv t (convertAfun fun) (convertAfun der) (convertAcc a)

convertAfun :: PreOpenAfun OpenAcc aenv t -> PreOpenAfun OpenAcc aenv t
convertAfun (Alam lhs f) = Alam lhs (convertAfun f)
convertAfun (Abody a) = Abody (convertAcc a)

convertBoundary :: Boundary aenv (Array sh a) -> Boundary aenv (Array sh a)
convertBoundary bnd@Clamp = bnd
convertBoundary bnd@Mirror = bnd
convertBoundary bnd@Wrap = bnd
convertBoundary bnd@(Constant _) = bnd
convertBoundary (Function f) = Function (convertFun f)


-- Elimination of remnant custom-derivative nodes
-- ----------------------------------------------

elimCustomsE :: OpenExp env aenv t -> OpenExp env aenv t
elimCustomsE (EcustomDeriv _ (Lam lhs (Body body)) _ a) =
  elimCustomsE (Let lhs a body)
elimCustomsE (EcustomDeriv _ _ _ _) =
  internalError (fromString "elimCustomsE: Invalid GADTs in EcustomDeriv")
elimCustomsE (Evjp _ _ _ _ _) = internalError (fromString "Unexpected Evjp in elimCustomsE")
-- Otherwise we recurse
elimCustomsE (Const ty con) = Const ty con
elimCustomsE (PrimApp f e) = PrimApp f (elimCustomsE e)
elimCustomsE (PrimConst c) = PrimConst c
elimCustomsE (Evar var) = Evar var
elimCustomsE (Let lhs def body) = Let lhs (elimCustomsE def) (elimCustomsE body)
elimCustomsE (Foreign ty func alt e) = Foreign ty func (convertFun alt) (elimCustomsE e)
elimCustomsE Nil = Nil
elimCustomsE (Pair e1 e2) = Pair (elimCustomsE e1) (elimCustomsE e2)
elimCustomsE (VecPack ty e) = VecPack ty (elimCustomsE e)
elimCustomsE (VecUnpack ty e) = VecUnpack ty (elimCustomsE e)
elimCustomsE (IndexSlice slty ix e) = IndexSlice slty (elimCustomsE ix) (elimCustomsE e)
elimCustomsE (IndexFull slty ix e) = IndexFull slty (elimCustomsE ix) (elimCustomsE e)
elimCustomsE (ToIndex ty she ixe) = ToIndex ty (elimCustomsE she) (elimCustomsE ixe)
elimCustomsE (FromIndex ty she ixe) = FromIndex ty (elimCustomsE she) (elimCustomsE ixe)
elimCustomsE (Case e es def) =
    Case (elimCustomsE e) (map (fmap elimCustomsE) es) (elimCustomsE <$> def)
elimCustomsE (Cond c e1 e2) = Cond (elimCustomsE c) (elimCustomsE e1) (elimCustomsE e2)
elimCustomsE (While c f e) = While (convertFun c) (convertFun f) (elimCustomsE e)
elimCustomsE (Index var dim) = Index var (elimCustomsE dim)
elimCustomsE (LinearIndex var dim) = LinearIndex var (elimCustomsE dim)
elimCustomsE (Shape var) = Shape var
elimCustomsE (ShapeSize shr e) = ShapeSize shr (elimCustomsE e)
elimCustomsE (Undef ty) = Undef ty
elimCustomsE (Coerce t1 t2 e) = Coerce t1 t2 (elimCustomsE e)

elimCustomsFun :: OpenFun env aenv t -> OpenFun env aenv t
elimCustomsFun (Lam lhs f) = Lam lhs (elimCustomsFun f)
elimCustomsFun (Body e) = Body (elimCustomsE e)

elimCustomsA :: OpenAcc aenv t -> OpenAcc aenv t
elimCustomsA (OpenAcc a) = OpenAcc (elimCustomsPAcc a)

elimCustomsPAcc :: PreOpenAcc OpenAcc aenv t -> PreOpenAcc OpenAcc aenv t
elimCustomsPAcc (AcustomDeriv _ (Alam lhs (Abody body)) _ a) =
  elimCustomsPAcc (Alet lhs a body)
elimCustomsPAcc (AcustomDeriv _ _ _ _) =
  internalError (fromString "elimCustomsPAcc: Invalid GADTs in AcustomDeriv")
elimCustomsPAcc (Avjp _ _ _ _ _) = internalError (fromString "Unexpected Avjp in elimCustomsPAcc")
-- Otherwise we recurse
elimCustomsPAcc (Alet lhs a b) = Alet lhs (elimCustomsA a) (elimCustomsA b)
elimCustomsPAcc (Avar a) = Avar a
elimCustomsPAcc (Apair a b) = Apair (elimCustomsA a) (elimCustomsA b)
elimCustomsPAcc Anil = Anil
elimCustomsPAcc (Atrace msg a b) = Atrace msg (elimCustomsA a) (elimCustomsA b)
elimCustomsPAcc (Apply t a b) = Apply t (elimCustomsAfun a) (elimCustomsA b)
elimCustomsPAcc (Aforeign t h a b) = Aforeign t h (elimCustomsAfun a) (elimCustomsA b)
elimCustomsPAcc (Acond e a b) = Acond (elimCustomsE e) (elimCustomsA a) (elimCustomsA b)
elimCustomsPAcc (Awhile a b c) = Awhile (elimCustomsAfun a) (elimCustomsAfun b) (elimCustomsA c)
elimCustomsPAcc (Use t a) = Use t a
elimCustomsPAcc (Unit t e) = Unit t (elimCustomsE e)
elimCustomsPAcc (Reshape t e a) = Reshape t (elimCustomsE e) (elimCustomsA a)
elimCustomsPAcc (Generate t e1 e2) = Generate t (elimCustomsE e1) (elimCustomsFun e2)
elimCustomsPAcc (Transform t e1 e2 e3 a) = Transform t (elimCustomsE e1) (elimCustomsFun e2) (elimCustomsFun e3) (elimCustomsA a)
elimCustomsPAcc (Replicate t e a) = Replicate t (elimCustomsE e) (elimCustomsA a)
elimCustomsPAcc (Slice t a e) = Slice t (elimCustomsA a) (elimCustomsE e)
elimCustomsPAcc (Map t e a) = Map t (elimCustomsFun e) (elimCustomsA a)
elimCustomsPAcc (ZipWith t e a b) = ZipWith t (elimCustomsFun e) (elimCustomsA a) (elimCustomsA b)
elimCustomsPAcc (Fold e me a) = Fold (elimCustomsFun e) (elimCustomsE <$> me) (elimCustomsA a)
elimCustomsPAcc (FoldSeg t e me a b) = FoldSeg t (elimCustomsFun e) (elimCustomsE <$> me) (elimCustomsA a) (elimCustomsA b)
elimCustomsPAcc (Scan t e me a) = Scan t (elimCustomsFun e) (elimCustomsE <$> me) (elimCustomsA a)
elimCustomsPAcc (Scan' t e e' a) = Scan' t (elimCustomsFun e) (elimCustomsE e') (elimCustomsA a)
elimCustomsPAcc (Permute e1 a e2 b) = Permute (elimCustomsFun e1) (elimCustomsA a) (elimCustomsFun e2) (elimCustomsA b)
elimCustomsPAcc (Backpermute t e1 e2 a) = Backpermute t (elimCustomsE e1) (elimCustomsFun e2) (elimCustomsA a)
elimCustomsPAcc (Stencil s t e b a) = Stencil s t (elimCustomsFun e) b (elimCustomsA a)
elimCustomsPAcc (Stencil2 s1 s2 t e1 b1 a1 b2 a2) = Stencil2 s1 s2 t (elimCustomsFun e1) b1 (elimCustomsA a1) b2 (elimCustomsA a2)

elimCustomsAfun :: OpenAfun aenv t -> OpenAfun aenv t
elimCustomsAfun (Alam lhs f) = Alam lhs (elimCustomsAfun f)
elimCustomsAfun (Abody e) = Abody (elimCustomsA e)
