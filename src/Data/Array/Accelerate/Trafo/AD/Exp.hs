{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
module Data.Array.Accelerate.Trafo.AD.Exp (
    module Data.Array.Accelerate.Trafo.AD.Exp,
    Idx(..), Val(..), idxToInt, prj
) where

-- import Data.GADT.Show

import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.AST as A
import Data.Array.Accelerate.AST (Idx(..), Val(..), idxToInt, prj)
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Shows


-- De Bruijn
-- ---------

data TagVal tag env where
    TEmpty :: TagVal tag ()
    TPush :: TagVal tag env -> tag -> TupleType t -> TagVal tag (env, t)

data LabVal lab env where
    LEmpty :: LabVal lab ()
    LPush :: LabVal lab env -> DLabel lab t -> LabVal lab (env, t)

-- Expressions
-- -----------

data DLabel lab t =
    DLabel { labelType :: TupleType t
           , labelLabel :: lab }
  deriving (Show)

-- TODO: Check how many reified types can be removed in this AST
data OpenExp env lab t where
    Const   :: ScalarType t
            -> t
            -> OpenExp env lab t

    PrimApp :: TupleType r
            -> A.PrimFun (a -> r)
            -> OpenExp env lab a
            -> OpenExp env lab r

    Pair    :: TupleType (a, b)
            -> OpenExp env lab a
            -> OpenExp env lab b
            -> OpenExp env lab (a, b)

    Nil     :: OpenExp env lab ()

    Let     :: A.ELeftHandSide bnd_t env env'
            -> OpenExp env lab bnd_t
            -> OpenExp env' lab a
            -> OpenExp env lab a

    Var     :: A.ExpVar env t
            -> OpenExp env lab t

    Label   :: DLabel lab t
            -> OpenExp env lab t

type Exp = OpenExp ()

-- Closed expression with an unknown type
data AnyExp lab = forall t. AnyExp (Exp lab t)
deriving instance Show lab => Show (AnyExp lab)

data AnyTupleType = forall t. AnyTupleType (TupleType t)
deriving instance Show AnyTupleType

-- Instances
-- ---------

showScalar :: ScalarType t -> t -> String
showScalar = \topty -> case topty of
    SingleScalarType ty -> showSingle ty
    VectorScalarType _ -> const "[vector?]"
  where
    showSingle :: SingleType t -> t -> String
    showSingle (NumSingleType ty) = showNum ty
    showSingle (NonNumSingleType ty) = showNonNum ty

    showNum :: NumType t -> t -> String
    showNum (IntegralNumType ty) = showIntegral ty
    showNum (FloatingNumType ty) = showFloating ty

    showIntegral :: IntegralType t -> t -> String
    showIntegral TypeInt = show
    showIntegral TypeInt8 = show
    showIntegral TypeInt16 = show
    showIntegral TypeInt32 = show
    showIntegral TypeInt64 = show
    showIntegral TypeWord = show
    showIntegral TypeWord8 = show
    showIntegral TypeWord16 = show
    showIntegral TypeWord32 = show
    showIntegral TypeWord64 = show

    showFloating :: FloatingType t -> t -> String
    showFloating TypeHalf = show
    showFloating TypeFloat = show
    showFloating TypeDouble = show

    showNonNum :: NonNumType t -> t -> String
    showNonNum TypeBool = show
    showNonNum TypeChar = show

showTuple :: TupleType t -> t -> String
showTuple TupRunit () = "()"
showTuple (TupRsingle ty) s = showScalar ty s
showTuple (TupRpair t1 t2) (a, b) =
    "(" ++ showTuple t1 a ++ ", " ++ showTuple t2 b ++ ")"

showsExpr :: (lab -> String) -> Int -> [String] -> Int -> OpenExp env lab t -> ShowS
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
showsExpr labf topseed env d (Let toplhs rhs body) = showParen (d > 0) $
    let (descr, seed') = namifyLHS topseed toplhs
        env' = descr : env
    in showString ("let " ++ descr ++ " = ") . showsExpr labf seed' env 0 rhs .
            showString " in " . showsExpr labf seed' env' 0 body
  where
    namifyVar :: Int -> (String, Int)
    namifyVar seed =
      let name = if seed < 26 then [['a'..'z'] !! seed] else 't' : show (seed - 25)
      in (name, seed + 1)

    namifyLHS :: Int -> A.ELeftHandSide v env env' -> (String, Int)
    namifyLHS seed (A.LeftHandSideSingle _) = namifyVar seed
    namifyLHS seed (A.LeftHandSideWildcard _) = ("_", seed)
    namifyLHS seed (A.LeftHandSidePair lhs1 lhs2) =
      let (descr1, seed1) = namifyLHS seed lhs1
          (descr2, seed2) = namifyLHS seed1 lhs2
      in ("(" ++ descr1 ++ ", " ++ descr2 ++ ")", seed2)
showsExpr _ _ env _ (Var (A.Var _ idx)) = showString (env !! idxToInt idx)
showsExpr labf _ _ d (Label (DLabel ty lab)) = showParen (d > 0) $
    showString ('L' : labf lab ++ " :: ") . showsPrec 1 ty

-- instance Show (OpenExp env Int t) where
--     showsPrec = showsExpr subscript 0 []

instance Show lab => Show (OpenExp env lab t) where
    showsPrec = showsExpr show 0 []

-- instance Show lab => GShow (DLabel lab) where
--     gshowsPrec = showsPrec

-- instance Show lab => GShow (OpenExp env lab) where
--     gshowsPrec = showsPrec

-- Auxiliary functions
-- -------------------

typeOf :: OpenExp env lab t -> TupleType t
typeOf (Const ty _) = TupRsingle ty
typeOf (PrimApp ty _ _) = ty
typeOf (Pair ty _ _) = ty
typeOf Nil = TupRunit
typeOf (Let _ _ body) = typeOf body
typeOf (Var (A.Var ty _)) = TupRsingle ty
typeOf (Label (DLabel ty _)) = ty

isInfixOp :: A.PrimFun ((a, b) -> c) -> Bool
isInfixOp (A.PrimAdd _) = True
isInfixOp (A.PrimMul _) = True
isInfixOp (A.PrimQuot _) = True
isInfixOp (A.PrimLtEq _) = True
isInfixOp _ = False

precedence :: A.PrimFun sig -> Int
precedence (A.PrimAdd _) = 6
precedence (A.PrimMul _) = 7
precedence (A.PrimQuot _) = 7
precedence (A.PrimNeg _) = 7  -- ?
precedence (A.PrimLog _) = 10
precedence (A.PrimLtEq _) = 4
precedence _ = 10  -- ?

data Fixity = Prefix | Infix
  deriving (Show)

prettyPrimFun :: Fixity -> A.PrimFun sig -> String
prettyPrimFun Infix (A.PrimAdd _) = "+"
prettyPrimFun Infix (A.PrimMul _) = "*"
prettyPrimFun Infix (A.PrimQuot _) = "/"
prettyPrimFun Infix (A.PrimNeg _) = "-"
prettyPrimFun Infix (A.PrimLtEq _) = "<="
prettyPrimFun Prefix (A.PrimLog _) = "log"
prettyPrimFun Prefix op = '(' : prettyPrimFun Infix op ++ ")"
prettyPrimFun fixity op =
    error ("prettyPrimFun: not defined for " ++ show fixity ++ " " ++ showPrimFun op)

prjL :: Idx env t -> LabVal lab env -> DLabel lab t
prjL ZeroIdx (LPush _ x) = x
prjL (SuccIdx idx) (LPush env _) = prjL idx env

mapLabVal :: (lab -> lab') -> LabVal lab env -> LabVal lab' env
mapLabVal _ LEmpty = LEmpty
mapLabVal f (LPush env (DLabel ty lab)) = LPush (mapLabVal f env) (DLabel ty (f lab))

labValContains :: Eq lab => LabVal lab env -> lab -> Bool
labValContains LEmpty _ = False
labValContains (LPush env (DLabel _ lab)) x =
    x == lab || labValContains env x

uniqueLabVal :: Eq lab => LabVal lab env -> Bool
uniqueLabVal LEmpty = True
uniqueLabVal (LPush env (DLabel _ lab)) =
    not (labValContains env lab) && uniqueLabVal env

data FoundTag env = forall t. FoundTag (TupleType t) (Idx env t)

labValFind' :: Eq lab => LabVal lab env -> lab -> Maybe (FoundTag env)
labValFind' LEmpty _ = Nothing
labValFind' (LPush env (DLabel ty lab)) target
    | lab == target = Just (FoundTag ty ZeroIdx)
    | otherwise =
        case labValFind' env target of
            Just (FoundTag ty' idx) -> Just (FoundTag ty' (SuccIdx idx))
            Nothing -> Nothing

labValFind :: Eq lab => LabVal lab env -> DLabel lab t -> Maybe (Idx env t)
labValFind LEmpty _ = Nothing
labValFind (LPush env (DLabel ty lab)) target@(DLabel ty2 lab2)
    | Just Refl <- matchTupleType ty ty2
    , lab == lab2 = Just ZeroIdx
    | otherwise =
        case labValFind env target of
            Just idx -> Just (SuccIdx idx)
            Nothing -> Nothing

fmapLabel :: (lab -> lab') -> DLabel lab t -> DLabel lab' t
fmapLabel f (DLabel ty lab) = DLabel ty (f lab)

labValToList :: LabVal lab env -> [(AnyTupleType, lab)]
labValToList LEmpty = []
labValToList (LPush env (DLabel ty lab)) =
    (AnyTupleType ty, lab) : labValToList env
