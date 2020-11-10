{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.Exp (
    module Data.Array.Accelerate.Trafo.AD.Exp,
    Idx(..), idxToInt
) where

import Data.Dependent.Map (DMap)
import Data.List (intercalate)
import Data.GADT.Show

import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (shapeType, ShapeR)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Environment as A
import qualified Data.Array.Accelerate.AST.Idx as A
import qualified Data.Array.Accelerate.AST.LeftHandSide as A
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Shows
import qualified Data.Array.Accelerate.Sugar.Tag as A
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Orphans ()
import qualified Data.Array.Accelerate.Trafo.Substitution as A (weakenVars, rebuildLHS)


-- Expressions
-- -----------

-- TODO: Check how many reified types can be removed in this AST
data OpenExp env aenv lab alab args tenv t where
    Const   :: ScalarType t
            -> t
            -> OpenExp env aenv lab alab args tenv t

    PrimApp :: TypeR r
            -> A.PrimFun (a -> r)
            -> OpenExp env aenv lab alab args tenv a
            -> OpenExp env aenv lab alab args tenv r

    PrimConst :: A.PrimConst a
              -> OpenExp env aenv lab alab args tenv a

    Pair    :: TypeR (a, b)
            -> OpenExp env aenv lab alab args tenv a
            -> OpenExp env aenv lab alab args tenv b
            -> OpenExp env aenv lab alab args tenv (a, b)

    Nil     :: OpenExp env aenv lab alab args tenv ()

    Cond    :: TypeR a
            -> OpenExp env aenv lab alab args tenv A.PrimBool
            -> OpenExp env aenv lab alab args tenv a
            -> OpenExp env aenv lab alab args tenv a
            -> OpenExp env aenv lab alab args tenv a

    Shape   :: Either (A.ArrayVar aenv (Array sh e))
                      (ADLabelNS alab (Array sh e))
            -> OpenExp env aenv lab alab args tenv sh

    -- The second argument is there in order for conditionally executing an
    -- Index node to work properly. In tree form (before explosion and after
    -- rebuilding) the second argument is Left, and works as usual. In graph
    -- form, the second argument is Right and contains two labels.
    -- - The first label is the usual argument label; normally this is
    --   indicated with a subexpression with head Label.
    -- - The second label is an additional intermediate store for the value of
    --   the index argument. The primal transformation MUST first store the
    --   index argument at the second label, before using that stored value for
    --   the actual indexing operation. This ensures that there is a copy of
    --   the index value available in the same conditional branch as the Index
    --   node itself, which can then safely be used in the dual pass to permute
    --   the adjoint to the right place.
    -- An example where this is necessary, and the dual phase cannot just take
    -- the normal argument label (fmap'ed with P) as the index to permute to,
    -- is if the index argument is computed outside a Cond, and then used
    -- without modification inside a Cond. If the Permute in the dual phase
    -- just used that argument, it would not be -1 as required if the branch
    -- containing the Index is not taken.
    Index   :: Either (A.ArrayVar aenv (Array sh e))
                      (ADLabelNS alab (Array sh e))
            -> Either (OpenExp env aenv lab alab args tenv sh)
                      (EDLabelN lab sh   -- The index argument
                      ,EDLabelN lab sh)  -- Backup location of the index argument
            -> OpenExp env aenv lab alab args tenv e

    ShapeSize :: ShapeR dim
              -> OpenExp env aenv lab alab args tenv dim
              -> OpenExp env aenv lab alab args tenv Int

    -- Use this VERY sparingly. It has no equivalent in the real AST, so must
    -- be laboriously back-converted using Let-bindings.
    Get     :: TypeR s
            -> TupleIdx t s
            -> OpenExp env aenv lab alab args tenv t
            -> OpenExp env aenv lab alab args tenv s

    Undef   :: ScalarType t
            -> OpenExp env aenv lab alab args tenv t

    Let     :: A.ELeftHandSide bnd_t env env'
            -> OpenExp env aenv lab alab args tenv bnd_t
            -> OpenExp env' aenv lab alab args tenv a
            -> OpenExp env aenv lab alab args tenv a

    Var     :: A.ExpVar env t
            -> OpenExp env aenv lab alab args tenv t

    FreeVar :: A.ExpVar tenv t
            -> OpenExp env aenv lab alab args tenv t

    Arg     :: ScalarType t
            -> Idx args t
            -> OpenExp env aenv lab alab args tenv t

    Label   :: EDLabelN lab t
            -> OpenExp env aenv lab alab args tenv t

type Exp = OpenExp ()

-- Expression-level function
data OpenFun env aenv lab alab tenv t where
    Body :: OpenExp env aenv lab alab () tenv t -> OpenFun env aenv lab alab tenv t
    Lam :: A.ELeftHandSide a env env' -> OpenFun env' aenv lab alab tenv t -> OpenFun env aenv lab alab tenv (a -> t)

type Fun = OpenFun ()

-- Closed expression with an unknown type
data AnyExp aenv lab alab args tenv = forall t. AnyExp (Exp aenv lab alab args tenv t)
deriving instance (Show lab, Show alab) => Show (AnyExp aenv lab alab args tenv)

data AnyTypeR = forall t. AnyTypeR (TypeR t)
deriving instance Show AnyTypeR

data AnyScalarType = forall t. AnyScalarType (ScalarType t)
deriving instance Show AnyScalarType

-- Instances
-- ---------

showsExp :: EShowEnv lab alab -> Int -> OpenExp env aenv lab alab args tenv t -> ShowS
showsExp _ _ (Const ty x) = showString (showScalar ty x)
showsExp se d (PrimApp _ f (Pair _ e1 e2)) | isInfixOp f =
    let prec = precedence f
        ops = prettyPrimFun Infix f
    in showParen (d > prec) $
            showsExp se (prec+1) e1 . showString (' ' : ops ++ " ") .
                showsExp se (prec+1) e2
showsExp se d (PrimApp _ f e) =
    let prec = precedence f
        ops = prettyPrimFun Prefix f
    in showParen (d > prec) $
            showString (ops ++ " ") . showsExp se (prec+1) e
showsExp _ _ (PrimConst c) = showString (show c)
showsExp se _ (Pair _ e1 e2) =
    showString "(" . showsExp se 0 e1 . showString ", " .
        showsExp se 0 e2 . showString ")"
showsExp _ _ Nil =
    showString "()"
showsExp se d (Cond _ c t e) =
    showParen (d > 10) $
        showString "cond " .
            showsExp se 11 c . showString " " .
            showsExp se 11 t . showString " " .
            showsExp se 11 e
showsExp se d (Shape (Left (A.Var _ idx))) =
    showParen (d > 10) $
        showString "shape " .
        (case drop (idxToInt idx) (seAenv se) of
            descr : _ -> showString descr
            [] -> showString ("tA_UP" ++ show (1 + idxToInt idx - length (seAenv se))))
showsExp se d (Shape (Right lab)) =
    showParen (d > 10) $
        showString "shape " .
        showString ("(L" ++ seAlabf se (labelLabel lab) ++ " :: " ++ show (labelType lab) ++ ")")
showsExp se d (Index subj e) =
    showParen (d > 10) $
        (case subj of
           Left (A.Var _ idx) ->
              case drop (idxToInt idx) (seAenv se) of
                  descr : _ -> showString descr
                  [] -> showString ("tA_UP" ++ show (1 + idxToInt idx - length (seAenv se)))
           Right lab ->
              showString ('L' : seAlabf se (labelLabel lab) ++ " :: " ++ show (labelType lab)))
        . showString " ! "
        . (case e of
             Left e' -> showsExp se 11 e'
             Right (lab, bklab) ->
                let showLabel = showsExp se 0 . Label
                in showString "(" . showLabel lab . showString " backup->"
                       . showLabel bklab . showString ")")
showsExp se d (ShapeSize _ e) =
    showParen (d > 10) $
        showString "shapeSize " .
        showsExp se 11 e
showsExp se d (Get _ ti e) = showParen (d > 10) $
    showString (tiPrefix ti) . showsExp se 10 e
  where
    tiPrefix :: TupleIdx t t' -> String
    tiPrefix = (++ " ") . intercalate "." . reverse . tiPrefix'

    tiPrefix' :: TupleIdx t t' -> [String]
    tiPrefix' TIHere = []
    tiPrefix' (TILeft ti') = "fst" : tiPrefix' ti'
    tiPrefix' (TIRight ti') = "snd" : tiPrefix' ti'
showsExp _ _ (Undef _) = showString "undef"
showsExp se d (Let lhs rhs body) = showParen (d > 0) $
    let (descr, descrs, seed') = namifyLHS (seSeed se) lhs
        env' = descrs ++ seEnv se
    in showString ("let " ++ descr ++ " = ") . showsExp (se { seSeed = seed' }) 0 rhs .
            showString " in " . showsExp (se { seSeed = seed', seEnv = env' }) 0 body
showsExp _ d (Arg ty idx) = showParen (d > 0) $
    showString ('A' : show (idxToInt idx) ++ " :: " ++ show ty)
showsExp se _ (Var (A.Var _ idx)) =
    case drop (idxToInt idx) (seEnv se) of
        descr : _ -> showString descr
        [] -> showString ("tE_UP" ++ show (1 + idxToInt idx - length (seEnv se)))
showsExp _ d (FreeVar (A.Var ty idx)) = showParen (d > 0) $
    showString ("tFREE" ++ show (1 + idxToInt idx) ++ " :: " ++ show ty)
showsExp se d (Label lab) = showParen (d > 0) $
    showString ('L' : seLabf se (labelLabel lab) ++ " :: " ++ show (labelType lab))

showsFun :: EShowEnv lab alab -> Int -> OpenFun env aenv lab alab tenv t -> ShowS
showsFun se d (Body expr) = showsExp se d expr
showsFun se d (Lam lhs fun) =
    let (descr, descrs, seed') = namifyLHS (seSeed se) lhs
        env' = descrs ++ seEnv se
    in showParen (d > 0) $
        showString "\\" . showString descr .
          showString " -> " . showsFun (se { seSeed = seed', seEnv = env' }) 0 fun

-- instance Show (OpenExp env Int t) where
--     showsPrec = showsExp subscript 0 []

instance (Show lab, Show alab) => Show (OpenExp env aenv lab alab args tenv t) where
    showsPrec = showsExp (ShowEnv show show 0 [] [])

instance (Show lab, Show alab) => GShow (OpenExp env aenv lab alab args tenv) where
    gshowsPrec = showsPrec

instance (Show lab, Show alab) => Show (OpenFun env aenv lab alab tenv t) where
    showsPrec = showsFun (ShowEnv show show 0 [] [])

-- Auxiliary functions
-- -------------------

etypeOf :: OpenExp env aenv lab alab args tenv t -> TypeR t
etypeOf (Const ty _) = TupRsingle ty
etypeOf (PrimApp ty _ _) = ty
etypeOf (PrimConst c) = TupRsingle (SingleScalarType (A.primConstType c))
etypeOf (Pair ty _ _) = ty
etypeOf Nil = TupRunit
etypeOf (Cond ty _ _ _) = ty
etypeOf (Shape (Left (A.Var (ArrayR sht _) _))) = shapeType sht
etypeOf (Shape (Right (DLabel (ArrayR sht _) _))) = shapeType sht
etypeOf (Index (Left (A.Var (ArrayR _ ty) _)) _) = ty
etypeOf (Index (Right (DLabel (ArrayR _ ty) _)) _) = ty
etypeOf (ShapeSize _ _) = TupRsingle scalarType
etypeOf (Get ty _ _) = ty
etypeOf (Undef ty) = TupRsingle ty
etypeOf (Let _ _ body) = etypeOf body
etypeOf (Var (A.Var ty _)) = TupRsingle ty
etypeOf (FreeVar (A.Var ty _)) = TupRsingle ty
etypeOf (Arg ty _) = TupRsingle ty
etypeOf (Label lab) = labelType lab

isInfixOp :: A.PrimFun ((a, b) -> c) -> Bool
isInfixOp (A.PrimAdd _) = True
isInfixOp (A.PrimSub _) = True
isInfixOp (A.PrimMul _) = True
isInfixOp (A.PrimFDiv _) = True
isInfixOp (A.PrimLt _) = True
isInfixOp (A.PrimLtEq _) = True
isInfixOp (A.PrimGt _) = True
isInfixOp (A.PrimGtEq _) = True
isInfixOp (A.PrimIDiv _) = True
isInfixOp (A.PrimEq _) = True
isInfixOp A.PrimLAnd = True
isInfixOp _ = False

precedence :: A.PrimFun sig -> Int
precedence (A.PrimAdd _) = 6
precedence (A.PrimSub _) = 6
precedence (A.PrimMul _) = 7
precedence (A.PrimFDiv _) = 7
precedence (A.PrimNeg _) = 7  -- ?
precedence (A.PrimRecip _) = 10
precedence (A.PrimLog _) = 10
precedence (A.PrimEq _) = 4
precedence (A.PrimLt _) = 4
precedence (A.PrimLtEq _) = 4
precedence (A.PrimGt _) = 4
precedence (A.PrimGtEq _) = 4
precedence A.PrimLAnd = 3
precedence _ = 10  -- ?

data Fixity = Prefix | Infix
  deriving (Show)

prettyPrimFun :: Fixity -> A.PrimFun sig -> String
prettyPrimFun Infix (A.PrimAdd _) = "+"
prettyPrimFun Infix (A.PrimSub _) = "-"
prettyPrimFun Infix (A.PrimMul _) = "*"
prettyPrimFun Infix (A.PrimFDiv _) = "/"
prettyPrimFun Infix (A.PrimNeg _) = "-"
prettyPrimFun Infix (A.PrimEq _) = "=="
prettyPrimFun Infix (A.PrimLt _) = "<"
prettyPrimFun Infix (A.PrimLtEq _) = "<="
prettyPrimFun Infix (A.PrimGt _) = ">"
prettyPrimFun Infix (A.PrimGtEq _) = ">="
prettyPrimFun Infix A.PrimLAnd = "&&!"
prettyPrimFun Infix (A.PrimIDiv _) = "`div`"
prettyPrimFun Prefix (A.PrimRecip _) = "recip"
prettyPrimFun Prefix (A.PrimSqrt _) = "sqrt"
prettyPrimFun Prefix (A.PrimLog _) = "log"
prettyPrimFun Prefix (A.PrimExpFloating _) = "exp"
prettyPrimFun Prefix (A.PrimTanh _) = "tanh"
prettyPrimFun Prefix (A.PrimSin _) = "sin"
prettyPrimFun Prefix (A.PrimCos _) = "cos"
prettyPrimFun Prefix (A.PrimFromIntegral _ _) = "fromIntegral"
prettyPrimFun Prefix (A.PrimToFloating _ _) = "toFloating"
prettyPrimFun Prefix (A.PrimRound _ _) = "round"
prettyPrimFun Prefix (A.PrimFloor _ _) = "floor"
prettyPrimFun Prefix (A.PrimMax _) = "max"
prettyPrimFun Prefix op = '(' : prettyPrimFun Infix op ++ ")"
prettyPrimFun fixity op =
    error ("prettyPrimFun: not defined for " ++ show fixity ++ " " ++ showPrimFun op)

elabValFind :: Eq lab => LabVal lty ScalarType lab env -> DLabel lty ScalarType lab t -> Maybe (Idx env t)
elabValFind LEmpty _ = Nothing
elabValFind (LPush env (DLabel ty lab)) target@(DLabel ty2 lab2)
    | Just Refl <- matchScalarType ty ty2
    , lab == lab2 = Just ZeroIdx
    | otherwise = SuccIdx <$> elabValFind env target

elabValFinds :: Eq lab => LabVal lty ScalarType lab env -> TupR (DLabel lty ScalarType lab) t -> Maybe (A.ExpVars env t)
elabValFinds _ TupRunit = Just TupRunit
elabValFinds labelenv (TupRsingle lab) =
    TupRsingle . A.Var (labelType lab) <$> elabValFind labelenv lab
elabValFinds labelenv (TupRpair labs1 labs2) =
    TupRpair <$> elabValFinds labelenv labs1 <*> elabValFinds labelenv labs2

elabValToList :: ELabVal lab env -> [(AnyScalarType, lab)]
elabValToList LEmpty = []
elabValToList (LPush env (DLabel ty lab)) =
    (AnyScalarType ty, lab) : elabValToList env

evars :: A.ExpVars env t -> OpenExp env aenv lab alab args tenv t
evars = snd . evars'
  where
    evars' :: A.ExpVars env t -> (TypeR t, OpenExp env aenv lab alab args tenv t)
    evars' TupRunit = (TupRunit, Nil)
    evars' (TupRsingle var@(A.Var ty _)) = (TupRsingle ty, Var var)
    evars' (TupRpair vars1 vars2) =
        let (t1, e1) = evars' vars1
            (t2, e2) = evars' vars2
        in (TupRpair t1 t2, Pair (TupRpair t1 t2) e1 e2)

untupleExps :: TupR (OpenExp env aenv lab alab args tenv) t -> OpenExp env aenv lab alab args tenv t
untupleExps TupRunit = Nil
untupleExps (TupRsingle e) = e
untupleExps (TupRpair t1 t2) = smartPair (untupleExps t1) (untupleExps t2)

-- Assumes the expression does not contain Label
generaliseLab :: OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab' alab args tenv t
generaliseLab (Const ty x) = Const ty x
generaliseLab (PrimApp ty op ex) = PrimApp ty op (generaliseLab ex)
generaliseLab (PrimConst c) = PrimConst c
generaliseLab (Pair ty e1 e2) = Pair ty (generaliseLab e1) (generaliseLab e2)
generaliseLab Nil = Nil
generaliseLab (Cond ty e1 e2 e3) = Cond ty (generaliseLab e1) (generaliseLab e2) (generaliseLab e3)
generaliseLab (Shape ref) = Shape ref
generaliseLab (Index ref (Left e)) = Index ref (Left (generaliseLab e))
generaliseLab (Index _ (Right _)) = error "generaliseLab: Index with label index found"
generaliseLab (ShapeSize sht e) = ShapeSize sht (generaliseLab e)
generaliseLab (Get ty path ex) = Get ty path (generaliseLab ex)
generaliseLab (Undef ty) = Undef ty
generaliseLab (Let lhs rhs ex) = Let lhs (generaliseLab rhs) (generaliseLab ex)
generaliseLab (Var v) = Var v
generaliseLab (FreeVar v) = FreeVar v
generaliseLab (Arg ty idx) = Arg ty idx
generaliseLab (Label _) = error "generaliseLab: Label found"

-- Assumes the expression does not contain labeled array variable references
generaliseLabA :: OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab' args tenv t
generaliseLabA (Const ty x) = Const ty x
generaliseLabA (PrimApp ty op ex) = PrimApp ty op (generaliseLabA ex)
generaliseLabA (PrimConst c) = PrimConst c
generaliseLabA (Pair ty e1 e2) = Pair ty (generaliseLabA e1) (generaliseLabA e2)
generaliseLabA Nil = Nil
generaliseLabA (Cond ty e1 e2 e3) = Cond ty (generaliseLabA e1) (generaliseLabA e2) (generaliseLabA e3)
generaliseLabA (Shape (Left avar)) = Shape (Left avar)
generaliseLabA (Shape (Right _)) = error "generaliseLabA: Shape with label found"
generaliseLabA (Index (Left avar) e) = Index (Left avar) (either (Left . generaliseLabA) Right e)
generaliseLabA (Index (Right _) _) = error "generaliseLabA: Index with label found"
generaliseLabA (ShapeSize sht e) = ShapeSize sht (generaliseLabA e)
generaliseLabA (Get ty path ex) = Get ty path (generaliseLabA ex)
generaliseLabA (Undef ty) = Undef ty
generaliseLabA (Let lhs rhs ex) = Let lhs (generaliseLabA rhs) (generaliseLabA ex)
generaliseLabA (Var v) = Var v
generaliseLabA (FreeVar v) = FreeVar v
generaliseLabA (Arg ty idx) = Arg ty idx
generaliseLabA (Label lab) = Label lab

-- Assumes the expression does not contain Label
generaliseLabFun :: OpenFun env aenv lab alab tenv t -> OpenFun env aenv lab' alab tenv t
generaliseLabFun (Lam lhs fun) = Lam lhs (generaliseLabFun fun)
generaliseLabFun (Body ex) = Body (generaliseLab ex)

-- Assumes the expression does not contain labelised array variable references
generaliseLabFunA :: OpenFun env aenv lab alab tenv t -> OpenFun env aenv lab alab' tenv t
generaliseLabFunA (Lam lhs fun) = Lam lhs (generaliseLabFunA fun)
generaliseLabFunA (Body ex) = Body (generaliseLabA ex)

-- TODO: These IndexInstantiators need some documentation
newtype IndexInstantiator idxadj sh t =
    IndexInstantiator
        (forall     env aenv lab alab args tenv.
            OpenExp env aenv lab alab args tenv idxadj
         -> OpenExp env aenv lab alab args tenv (t, sh))

data IndexInstantiators idxadj arr where
    IndexInstantiators
        :: [IndexInstantiator idxadj sh t]
        -> IndexInstantiators idxadj (Array sh t)

instance Semigroup (IndexInstantiators idxadj arr) where
    IndexInstantiators l <> IndexInstantiators l' = IndexInstantiators (l <> l')

data SplitLambdaAD t t' lab alab tenv tmp idxadj =
    forall fv.
        SplitLambdaAD (forall aenv alab'. A.ArrayVars aenv fv -> Fun aenv lab alab' tenv (t -> (t', tmp)))
                      (forall aenv alab'. A.ArrayVars aenv fv -> Fun aenv lab alab' tenv ((t', tmp) -> (t, idxadj)))
                      (TupR (ADLabelNS alab) fv)
                      (TypeR tmp)
                      (TypeR idxadj)
                      (DMap (ADLabelNS alab) (IndexInstantiators idxadj))

data SomeSplitLambdaAD t t' lab alab tenv =
    forall tmp idxadj. SomeSplitLambdaAD (SplitLambdaAD t t' lab alab tenv tmp idxadj)

data LetBoundExpE env t s =
    forall env'. LetBoundExpE (A.ELeftHandSide t env env') (A.ExpVars env' s)

elhsCopy :: TypeR t -> LetBoundExpE env t t
elhsCopy TupRunit = LetBoundExpE (A.LeftHandSideWildcard TupRunit) TupRunit
elhsCopy (TupRsingle sty) = LetBoundExpE (A.LeftHandSideSingle sty) (TupRsingle (A.Var sty A.ZeroIdx))
elhsCopy (TupRpair t1 t2)
  | LetBoundExpE lhs1 vars1 <- elhsCopy t1
  , LetBoundExpE lhs2 vars2 <- elhsCopy t2
  = let vars1' = A.weakenVars (A.weakenWithLHS lhs2) vars1
    in LetBoundExpE (A.LeftHandSidePair lhs1 lhs2) (TupRpair vars1' vars2)

sinkExp :: env A.:> env' -> OpenExp env aenv lab alab args tenv t -> OpenExp env' aenv lab alab args tenv t
sinkExp _ (Const ty x) = Const ty x
sinkExp k (PrimApp ty op e) = PrimApp ty op (sinkExp k e)
sinkExp _ (PrimConst c) = PrimConst c
sinkExp k (Pair ty e1 e2) = Pair ty (sinkExp k e1) (sinkExp k e2)
sinkExp _ Nil = Nil
sinkExp k (Cond ty c t e) = Cond ty (sinkExp k c) (sinkExp k t) (sinkExp k e)
sinkExp _ (Shape var) = Shape var
sinkExp k (Index var idx) = Index var (either (Left . sinkExp k) Right idx)
sinkExp k (ShapeSize sht e) = ShapeSize sht (sinkExp k e)
sinkExp k (Get ty ti e) = Get ty ti (sinkExp k e)
sinkExp _ (Undef ty) = Undef ty
sinkExp k (Let lhs rhs e)
  | A.Exists lhs' <- A.rebuildLHS lhs =
      Let lhs' (sinkExp k rhs) (sinkExp (A.sinkWithLHS lhs lhs' k) e)
sinkExp k (Var (A.Var sty idx)) = Var (A.Var sty (k A.>:> idx))
sinkExp _ (FreeVar var) = FreeVar var
sinkExp _ (Arg ty idx) = Arg ty idx
sinkExp _ (Label lab) = Label lab

-- Check if the variable can be re-localised under the TagVal. If so, returns
-- the variable with the re-localised environment. If not, returns Nothing.
eCheckLocalT :: (forall t1 t2. s t1 -> s t2 -> Maybe (t1 :~: t2)) -> A.Var s env t -> TagVal s env2 -> Maybe (A.Var s env2 t)
eCheckLocalT _ _ TEmpty = Nothing
eCheckLocalT match (A.Var sty A.ZeroIdx) (TPush _ sty')
  | Just Refl <- match sty sty' =
      Just (A.Var sty ZeroIdx)
  | otherwise = Nothing
eCheckLocalT match (A.Var sty (A.SuccIdx idx)) (TPush tagval _)
  | Just (A.Var sty' idx') <- eCheckLocalT match (A.Var sty idx) tagval =
      Just (A.Var sty' (SuccIdx idx'))
  | otherwise = Nothing

-- If the variable is local within the known portion of the PartialVal, returns
-- the variable unchanged; else, returns a reference in the topenv of the
-- PartialVal.
eCheckLocalP :: (forall t1 t2. s t1 -> s t2 -> Maybe (t1 :~: t2)) -> A.Var s env t -> PartialVal s topenv env -> Either (A.Var s topenv t) (A.Var s env t)
eCheckLocalP _ var PTEmpty = Left var
eCheckLocalP match (A.Var sty A.ZeroIdx) (PTPush _ sty')
  | Just Refl <- match sty sty' =
      Right (A.Var sty A.ZeroIdx)
  | otherwise = error "Idx/env types do not match up in eCheckLocalP"
eCheckLocalP match (A.Var sty (A.SuccIdx idx)) (PTPush tagval _) =
  case eCheckLocalP match (A.Var sty idx) tagval of
    Right (A.Var sty' idx') -> Right (A.Var sty' (A.SuccIdx idx'))
    Left topvar -> Left topvar

-- Check if the variable can be re-localised under the known part of the
-- PartialVal. If so, returns the variable with the re-localised environment.
-- If not, e.g. if it refers to the unknown portion, returns Nothing.
eCheckLocalP' :: (forall t1 t2. s t1 -> s t2 -> Maybe (t1 :~: t2)) -> A.Var s env2 t -> PartialVal s topenv env -> Maybe (A.Var s env t)
eCheckLocalP' _ _ PTEmpty = Nothing
eCheckLocalP' match (A.Var sty A.ZeroIdx) (PTPush _ sty')
  | Just Refl <- match sty sty' =
      Just (A.Var sty A.ZeroIdx)
  | otherwise = Nothing
eCheckLocalP' match (A.Var sty (A.SuccIdx idx)) (PTPush tagval _)
  | Just (A.Var sty' idx') <- eCheckLocalP' match (A.Var sty idx) tagval =
      Just (A.Var sty' (SuccIdx idx'))
  | otherwise = Nothing

expALabels :: OpenExp env aenv lab alab args tenv t -> [AAnyLabelNS alab]
expALabels (Const _ _) = []
expALabels (PrimApp _ _ e) = expALabels e
expALabels (PrimConst _) = []
expALabels (Pair _ e1 e2) = expALabels e1 ++ expALabels e2
expALabels Nil = []
expALabels (Cond _ c t e) = expALabels c ++ expALabels t ++ expALabels e
expALabels (Shape var) = either (const []) (pure . AnyLabel) var
expALabels (Index var idx) = either (const []) (pure . AnyLabel) var ++ either expALabels (const []) idx
expALabels (ShapeSize _ e) = expALabels e
expALabels (Get _ _ e) = expALabels e
expALabels (Undef _) = []
expALabels (Let _ rhs e) = expALabels rhs ++ expALabels e
expALabels (Var _) = []
expALabels (FreeVar _) = []
expALabels (Arg _ _) = []
expALabels (Label _) = []

expFunALabels :: OpenFun env aenv lab alab tenv t -> [AAnyLabelNS alab]
expFunALabels (Lam _ fun) = expFunALabels fun
expFunALabels (Body ex) = expALabels ex

expHasIndex :: OpenExp env aenv lab alab args tenv t -> Bool
expHasIndex (Const _ _) = False
expHasIndex (PrimApp _ _ e) = expHasIndex e
expHasIndex (PrimConst _) = False
expHasIndex (Pair _ e1 e2) = expHasIndex e1 || expHasIndex e2
expHasIndex Nil = False
expHasIndex (Cond _ c t e) = expHasIndex c || expHasIndex t || expHasIndex e
expHasIndex (Shape _) = False
expHasIndex (Index _ _) = True
expHasIndex (ShapeSize _ e) = expHasIndex e
expHasIndex (Get _ _ e) = expHasIndex e
expHasIndex (Undef _) = False
expHasIndex (Let _ rhs e) = expHasIndex rhs || expHasIndex e
expHasIndex (Var _) = False
expHasIndex (FreeVar _) = False
expHasIndex (Arg _ _) = False
expHasIndex (Label _) = False


mkNothing :: forall env aenv lab alab args tenv t. TypeR t -> OpenExp env aenv lab alab args tenv (A.PrimMaybe t)
mkNothing ty
  | [tag] <- [tag | ("Nothing", tag) <- A.tags @(Maybe t)] =
      smartPair (Const scalarType tag) (smartPair Nil (untupleExps (fmapTupR Undef ty)))
  | otherwise = error "Maybe does not have a Just constructor?"

mkJust :: forall env aenv lab alab args tenv t. OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv (A.PrimMaybe t)
mkJust ex
  | [tag] <- [tag | ("Just", tag) <- A.tags @(Maybe t)] =
      smartPair (Const scalarType tag) (smartPair Nil ex)
  | otherwise = error "Maybe does not have a Just constructor?"

mkBool :: Bool -> OpenExp env aenv lab alab args tenv A.PrimBool
mkBool b
  | [tag] <- [tag | (name, tag) <- A.tags @Bool, name == constrName] =
      Const scalarType tag
  | otherwise = error $ "Bool does not have a " ++ constrName ++ " constructor?"
  where constrName = if b then "True" else "False"


smartPair :: OpenExp env aenv lab alab args tenv a -> OpenExp env aenv lab alab args tenv b -> OpenExp env aenv lab alab args tenv (a, b)
smartPair a b = Pair (TupRpair (etypeOf a) (etypeOf b)) a b

smartNeg :: NumType t -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv t
smartNeg ty a = PrimApp (TupRsingle (SingleScalarType (NumSingleType ty))) (A.PrimNeg ty) a

smartRecip :: FloatingType t -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv t
smartRecip ty a = PrimApp (TupRsingle (SingleScalarType (NumSingleType (FloatingNumType ty)))) (A.PrimRecip ty) a

smartAdd :: NumType t -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv t
smartAdd ty a b = PrimApp (TupRsingle (SingleScalarType (NumSingleType ty))) (A.PrimAdd ty) (smartPair a b)

smartSub :: NumType t -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv t
smartSub ty a b = PrimApp (TupRsingle (SingleScalarType (NumSingleType ty))) (A.PrimSub ty) (smartPair a b)

smartMul :: NumType t -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv t
smartMul ty a b = PrimApp (TupRsingle (SingleScalarType (NumSingleType ty))) (A.PrimMul ty) (smartPair a b)

smartFDiv :: FloatingType t -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv t
smartFDiv ty a b = PrimApp (TupRsingle (SingleScalarType (NumSingleType (FloatingNumType ty)))) (A.PrimFDiv ty) (smartPair a b)

smartGt :: SingleType t -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args tenv A.PrimBool
smartGt ty a b = PrimApp (TupRsingle scalarType) (A.PrimGt ty) (smartPair a b)

-- TODO: make smartFst and smartSnd non-quadratic
smartFst :: OpenExp env aenv lab alab args tenv (t1, t2) -> OpenExp env aenv lab alab args tenv t1
smartFst (Pair _ ex _) = ex
smartFst (Get (TupRpair t1 _) tidx ex) = Get t1 (insertFst tidx) ex
  where insertFst :: TupleIdx t (t1, t2) -> TupleIdx t t1
        insertFst TIHere = TILeft TIHere
        insertFst (TILeft ti) = TILeft (insertFst ti)
        insertFst (TIRight ti) = TIRight (insertFst ti)
smartFst ex
  | TupRpair t1 _ <- etypeOf ex
  = Get t1 (TILeft TIHere) ex
smartFst _ = error "smartFst: impossible GADTs"

smartSnd :: OpenExp env aenv lab alab args tenv (t1, t2) -> OpenExp env aenv lab alab args tenv t2
smartSnd (Pair _ _ ex) = ex
smartSnd (Get (TupRpair _ t2) tidx ex) = Get t2 (insertSnd tidx) ex
  where insertSnd :: TupleIdx t (t1, t2) -> TupleIdx t t2
        insertSnd TIHere = TIRight TIHere
        insertSnd (TILeft ti) = TILeft (insertSnd ti)
        insertSnd (TIRight ti) = TIRight (insertSnd ti)
smartSnd ex
  | TupRpair _ t2 <- etypeOf ex
  = Get t2 (TIRight TIHere) ex
smartSnd _ = error "smartSnd: impossible GADTs"
