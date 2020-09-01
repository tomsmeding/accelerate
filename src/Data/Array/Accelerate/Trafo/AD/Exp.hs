{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
module Data.Array.Accelerate.Trafo.AD.Exp (
    module Data.Array.Accelerate.Trafo.AD.Exp,
    Idx(..), idxToInt
) where

import Data.List (intercalate)
import Data.GADT.Show

import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (shapeType)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Shows
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Orphans ()


type ELabVal = LabVal ScalarType

type EDLabel = DLabel ScalarType
type EDLabelT = DLabel TypeR


-- Expressions
-- -----------

-- TODO: Check how many reified types can be removed in this AST
data OpenExp env aenv lab args t where
    Const   :: ScalarType t
            -> t
            -> OpenExp env aenv lab args t

    PrimApp :: TypeR r
            -> A.PrimFun (a -> r)
            -> OpenExp env aenv lab args a
            -> OpenExp env aenv lab args r

    Pair    :: TypeR (a, b)
            -> OpenExp env aenv lab args a
            -> OpenExp env aenv lab args b
            -> OpenExp env aenv lab args (a, b)

    Nil     :: OpenExp env aenv lab args ()

    Cond    :: TypeR a
            -> OpenExp env aenv lab args A.PrimBool
            -> OpenExp env aenv lab args a
            -> OpenExp env aenv lab args a
            -> OpenExp env aenv lab args a

    Shape   :: A.ArrayVar aenv (Array dim e)
            -> OpenExp env aenv lab args dim

    -- Use this VERY sparingly. It has no equivalent in the real AST, so must
    -- be laboriously back-converted using Let-bindings.
    Get     :: TypeR s
            -> TupleIdx t s
            -> OpenExp env aenv lab args t
            -> OpenExp env aenv lab args s

    Let     :: A.ELeftHandSide bnd_t env env'
            -> OpenExp env aenv lab args bnd_t
            -> OpenExp env' aenv lab args a
            -> OpenExp env aenv lab args a

    Var     :: A.ExpVar env t
            -> OpenExp env aenv lab args t

    Arg     :: ScalarType t
            -> Idx args t
            -> OpenExp env aenv lab args t

    Label   :: EDLabelT lab t
            -> OpenExp env aenv lab args t

type Exp = OpenExp ()

-- Closed expression with an unknown type
data AnyExp aenv lab args = forall t. AnyExp (Exp aenv lab args t)
deriving instance Show lab => Show (AnyExp aenv lab args)

data AnyTypeR = forall t. AnyTypeR (TypeR t)
deriving instance Show AnyTypeR

data AnyScalarType = forall t. AnyScalarType (ScalarType t)
deriving instance Show AnyScalarType

-- Instances
-- ---------

showsExp :: (lab -> String) -> Int -> [String] -> [String] -> Int -> OpenExp env aenv lab args t -> ShowS
showsExp _ _ _ _ _ (Const ty x) = showString (showScalar ty x)
showsExp labf seed env aenv d (PrimApp _ f (Pair _ e1 e2)) | isInfixOp f =
    let prec = precedence f
        ops = prettyPrimFun Infix f
    in showParen (d > prec) $
            showsExp labf seed env aenv (prec+1) e1 . showString (' ' : ops ++ " ") .
                showsExp labf seed env aenv (prec+1) e2
showsExp labf seed env aenv d (PrimApp _ f e) =
    let prec = precedence f
        ops = prettyPrimFun Prefix f
    in showParen (d > prec) $
            showString (ops ++ " ") . showsExp labf seed env aenv (prec+1) e
showsExp labf seed env aenv _ (Pair _ e1 e2) =
    showString "(" . showsExp labf seed env aenv 0 e1 . showString ", " .
        showsExp labf seed env aenv 0 e2 . showString ")"
showsExp _ _ _ _ _ Nil =
    showString "()"
showsExp labf seed env aenv d (Cond _ c t e) =
    showParen (d > 10) $
        showString "cond " .
            showsExp labf seed env aenv 11 c . showString " " .
            showsExp labf seed env aenv 11 t . showString " " .
            showsExp labf seed env aenv 11 e
showsExp _ _ _ aenv d (Shape (A.Var _ idx)) =
    showParen (d > 10) $
        showString "shape " .
            (case drop (idxToInt idx) aenv of
                descr : _ -> showString descr
                [] -> error $ "Avar out of aenv range in showsExp: " ++
                              show (idxToInt idx) ++ " in " ++ show aenv)
showsExp labf seed env aenv d (Get _ ti e) = showParen (d > 10) $
    showString (tiPrefix ti) . showsExp labf seed env aenv 10 e
  where
    tiPrefix :: TupleIdx t t' -> String
    tiPrefix = (++ " ") . intercalate "." . reverse . tiPrefix'

    tiPrefix' :: TupleIdx t t' -> [String]
    tiPrefix' TIHere = []
    tiPrefix' (TILeft ti') = "fst" : tiPrefix' ti'
    tiPrefix' (TIRight ti') = "snd" : tiPrefix' ti'
showsExp labf seed env aenv d (Let lhs rhs body) = showParen (d > 0) $
    let (descr, descrs, seed') = namifyLHS seed lhs
        env' = descrs ++ env
    in showString ("let " ++ descr ++ " = ") . showsExp labf seed' env aenv 0 rhs .
            showString " in " . showsExp labf seed' env' aenv 0 body
showsExp _ _ _ _ d (Arg ty idx) = showParen (d > 0) $
    showString ('A' : show (idxToInt idx) ++ " :: " ++ show ty)
showsExp _ _ env _ _ (Var (A.Var _ idx)) =
    case drop (idxToInt idx) env of
        descr : _ -> showString descr
        [] -> error $ "Var out of env range in showsExp: " ++
                      show (idxToInt idx) ++ " in " ++ show env
showsExp labf _ _ _ d (Label lab) = showParen (d > 0) $
    showString ('L' : labf (labelLabel lab) ++ " :: " ++ show (labelType lab))

-- instance Show (OpenExp env Int t) where
--     showsPrec = showsExp subscript 0 []

instance Show lab => Show (OpenExp env aenv lab args t) where
    showsPrec = showsExp show 0 [] []

instance Show lab => GShow (OpenExp env aenv lab args) where
    gshowsPrec = showsPrec

-- Auxiliary functions
-- -------------------

etypeOf :: OpenExp env aenv lab args t -> TypeR t
etypeOf (Const ty _) = TupRsingle ty
etypeOf (PrimApp ty _ _) = ty
etypeOf (Pair ty _ _) = ty
etypeOf Nil = TupRunit
etypeOf (Cond ty _ _ _) = ty
etypeOf (Shape (A.Var (ArrayR sht _) _)) = shapeType sht
etypeOf (Get ty _ _) = ty
etypeOf (Let _ _ body) = etypeOf body
etypeOf (Var (A.Var ty _)) = TupRsingle ty
etypeOf (Arg ty _) = TupRsingle ty
etypeOf (Label lab) = labelType lab

isInfixOp :: A.PrimFun ((a, b) -> c) -> Bool
isInfixOp (A.PrimAdd _) = True
isInfixOp (A.PrimMul _) = True
isInfixOp (A.PrimFDiv _) = True
isInfixOp (A.PrimLt _) = True
isInfixOp (A.PrimLtEq _) = True
isInfixOp (A.PrimGt _) = True
isInfixOp (A.PrimGtEq _) = True
isInfixOp (A.PrimIDiv _) = True
isInfixOp _ = False

precedence :: A.PrimFun sig -> Int
precedence (A.PrimAdd _) = 6
precedence (A.PrimMul _) = 7
precedence (A.PrimFDiv _) = 7
precedence (A.PrimNeg _) = 7  -- ?
precedence (A.PrimLog _) = 10
precedence (A.PrimLt _) = 4
precedence (A.PrimLtEq _) = 4
precedence (A.PrimGt _) = 4
precedence (A.PrimGtEq _) = 4
precedence _ = 10  -- ?

data Fixity = Prefix | Infix
  deriving (Show)

prettyPrimFun :: Fixity -> A.PrimFun sig -> String
prettyPrimFun Infix (A.PrimAdd _) = "+"
prettyPrimFun Infix (A.PrimMul _) = "*"
prettyPrimFun Infix (A.PrimFDiv _) = "/"
prettyPrimFun Infix (A.PrimNeg _) = "-"
prettyPrimFun Infix (A.PrimLt _) = "<"
prettyPrimFun Infix (A.PrimLtEq _) = "<="
prettyPrimFun Infix (A.PrimGt _) = ">"
prettyPrimFun Infix (A.PrimGtEq _) = ">="
prettyPrimFun Infix (A.PrimIDiv _) = "`div`"
prettyPrimFun Prefix (A.PrimLog _) = "log"
prettyPrimFun Prefix (A.PrimToFloating _ _) = "toFloating"
prettyPrimFun Prefix (A.PrimRound _ _) = "round"
prettyPrimFun Prefix op = '(' : prettyPrimFun Infix op ++ ")"
prettyPrimFun fixity op =
    error ("prettyPrimFun: not defined for " ++ show fixity ++ " " ++ showPrimFun op)

elabValFind :: Eq lab => ELabVal lab env -> EDLabel lab t -> Maybe (Idx env t)
elabValFind LEmpty _ = Nothing
elabValFind (LPush env (DLabel ty lab)) target@(DLabel ty2 lab2)
    | Just Refl <- matchScalarType ty ty2
    , lab == lab2 = Just ZeroIdx
    | otherwise = SuccIdx <$> elabValFind env target

elabValFinds :: Eq lab => ELabVal lab env -> TupR (DLabel ScalarType lab) t -> Maybe (A.ExpVars env t)
elabValFinds _ TupRunit = Just TupRunit
elabValFinds labelenv (TupRsingle lab) =
    TupRsingle . A.Var (labelType lab) <$> elabValFind labelenv lab
elabValFinds labelenv (TupRpair labs1 labs2) =
    TupRpair <$> elabValFinds labelenv labs1 <*> elabValFinds labelenv labs2

elabValToList :: ELabVal lab env -> [(AnyScalarType, lab)]
elabValToList LEmpty = []
elabValToList (LPush env (DLabel ty lab)) =
    (AnyScalarType ty, lab) : elabValToList env

evars :: A.ExpVars env t -> OpenExp env aenv lab args t
evars = snd . evars'
  where
    evars' :: A.ExpVars env t -> (TypeR t, OpenExp env aenv lab args t)
    evars' TupRunit = (TupRunit, Nil)
    evars' (TupRsingle var@(A.Var ty _)) = (TupRsingle ty, Var var)
    evars' (TupRpair vars1 vars2) =
        let (t1, e1) = evars' vars1
            (t2, e2) = evars' vars2
        in (TupRpair t1 t2, Pair (TupRpair t1 t2) e1 e2)
