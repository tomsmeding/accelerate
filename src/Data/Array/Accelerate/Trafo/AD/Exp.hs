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

import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.LeftHandSide as A
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
data OpenExp env lab args t where
    Const   :: ScalarType t
            -> t
            -> OpenExp env lab args t

    PrimApp :: TypeR r
            -> A.PrimFun (a -> r)
            -> OpenExp env lab args a
            -> OpenExp env lab args r

    Pair    :: TypeR (a, b)
            -> OpenExp env lab args a
            -> OpenExp env lab args b
            -> OpenExp env lab args (a, b)

    Nil     :: OpenExp env lab args ()

    Cond    :: TypeR a
            -> OpenExp env lab args A.PrimBool
            -> OpenExp env lab args a
            -> OpenExp env lab args a
            -> OpenExp env lab args a

    -- Use this VERY sparingly. It has no equivalent in the real AST, so must
    -- be laboriously back-converted using Let-bindings.
    Get     :: TypeR s
            -> TupleIdx t s
            -> OpenExp env lab args t
            -> OpenExp env lab args s

    Let     :: A.ELeftHandSide bnd_t env env'
            -> OpenExp env lab args bnd_t
            -> OpenExp env' lab args a
            -> OpenExp env lab args a

    Var     :: A.ExpVar env t
            -> OpenExp env lab args t

    Arg     :: ScalarType t
            -> Idx args t
            -> OpenExp env lab args t

    Label   :: EDLabelT lab t
            -> OpenExp env lab args t

type Exp = OpenExp ()

-- Closed expression with an unknown type
data AnyExp lab args = forall t. AnyExp (Exp lab args t)
deriving instance Show lab => Show (AnyExp lab args)

data AnyTypeR = forall t. AnyTypeR (TypeR t)
deriving instance Show AnyTypeR

data AnyScalarType = forall t. AnyScalarType (ScalarType t)
deriving instance Show AnyScalarType

-- Instances
-- ---------

showsExpr :: (lab -> String) -> Int -> [String] -> Int -> OpenExp env lab args t -> ShowS
showsExpr _ _ _ _ (Const ty x) = showString (showScalar ty x)
showsExpr labf seed env d (PrimApp _ f (Pair _ e1 e2)) | isInfixOp f =
    let prec = precedence f
        ops = prettyPrimFun Infix f
    in showParen (d > prec) $
            showsExpr labf seed env (prec+1) e1 . showString (' ' : ops ++ " ") .
                showsExpr labf seed env (prec+1) e2
showsExpr labf seed env d (PrimApp _ f e) =
    let prec = precedence f
        ops = prettyPrimFun Prefix f
    in showParen (d > prec) $
            showString (ops ++ " ") . showsExpr labf seed env (prec+1) e
showsExpr labf seed env _ (Pair _ e1 e2) =
    showString "(" . showsExpr labf seed env 0 e1 . showString ", " .
        showsExpr labf seed env 0 e2 . showString ")"
showsExpr _ _ _ _ Nil =
    showString "()"
showsExpr labf seed env d (Cond _ c t e) =
    showParen (d > 10) $
        showString "cond " .
            showsExpr labf seed env 11 c . showString " " .
            showsExpr labf seed env 11 t . showString " " .
            showsExpr labf seed env 11 e
showsExpr labf seed env d (Get _ ti e) = showParen (d > 10) $
    showString (tiPrefix ti) . showsExpr labf seed env 10 e
  where
    tiPrefix :: TupleIdx t t' -> String
    tiPrefix = (++ " ") . intercalate "." . reverse . tiPrefix'

    tiPrefix' :: TupleIdx t t' -> [String]
    tiPrefix' TIHere = []
    tiPrefix' (TILeft ti') = "fst" : tiPrefix' ti'
    tiPrefix' (TIRight ti') = "snd" : tiPrefix' ti'
showsExpr labf topseed env d (Let toplhs rhs body) = showParen (d > 0) $
    let (descr, descrs, seed') = namifyLHS topseed toplhs
        env' = descrs ++ env
    in showString ("let " ++ descr ++ " = ") . showsExpr labf seed' env 0 rhs .
            showString " in " . showsExpr labf seed' env' 0 body
  where
    namifyVar :: Int -> (String, Int)
    namifyVar seed =
      let name = if seed < 26 then [['a'..'z'] !! seed] else 't' : show (seed - 25)
      in (name, seed + 1)

    namifyLHS :: Int -> A.ELeftHandSide v env env' -> (String, [String], Int)
    namifyLHS seed (A.LeftHandSideSingle _) =
      let (n, seed') = namifyVar seed
      in (n, [n], seed')
    namifyLHS seed (A.LeftHandSideWildcard _) = ("_", [], seed)
    namifyLHS seed (A.LeftHandSidePair lhs1 lhs2) =
      let (descr1, descrs1, seed1) = namifyLHS seed lhs1
          (descr2, descrs2, seed2) = namifyLHS seed1 lhs2
      in ("(" ++ descr1 ++ ", " ++ descr2 ++ ")", descrs2 ++ descrs1,seed2)
showsExpr _ _ _ d (Arg ty idx) = showParen (d > 0) $
    showString ('A' : show (idxToInt idx) ++ " :: " ++ show ty)
showsExpr _ _ env _ (Var (A.Var _ idx)) =
    case drop (idxToInt idx) env of
        descr : _ -> showString descr
        [] -> error $ "Var out of env range in showsExpr: " ++
                      show (idxToInt idx) ++ " in " ++ show env
showsExpr labf _ _ d (Label lab) = showParen (d > 0) $
    showString ('L' : labf (labelLabel lab) ++ " :: " ++ show (labelType lab))

-- instance Show (OpenExp env Int t) where
--     showsPrec = showsExpr subscript 0 []

instance Show lab => Show (OpenExp env lab args t) where
    showsPrec = showsExpr show 0 []

instance Show lab => GShow (OpenExp env lab args) where
    gshowsPrec = showsPrec

-- Auxiliary functions
-- -------------------

typeOf :: OpenExp env lab args t -> TypeR t
typeOf (Const ty _) = TupRsingle ty
typeOf (PrimApp ty _ _) = ty
typeOf (Pair ty _ _) = ty
typeOf Nil = TupRunit
typeOf (Cond ty _ _ _) = ty
typeOf (Get ty _ _) = ty
typeOf (Let _ _ body) = typeOf body
typeOf (Var (A.Var ty _)) = TupRsingle ty
typeOf (Arg ty _) = TupRsingle ty
typeOf (Label lab) = labelType lab

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
    | otherwise =
        -- TODO: fmap
        case elabValFind env target of
            Just idx -> Just (SuccIdx idx)
            Nothing -> Nothing

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

evars :: A.ExpVars env t -> OpenExp env lab args t
evars = snd . evars'
  where
    evars' :: A.ExpVars env t -> (TypeR t, OpenExp env lab args t)
    evars' TupRunit = (TupRunit, Nil)
    evars' (TupRsingle var@(A.Var ty _)) = (TupRsingle ty, Var var)
    evars' (TupRpair vars1 vars2) =
        let (t1, e1) = evars' vars1
            (t2, e2) = evars' vars2
        in (TupRpair t1 t2, Pair (TupRpair t1 t2) e1 e2)
