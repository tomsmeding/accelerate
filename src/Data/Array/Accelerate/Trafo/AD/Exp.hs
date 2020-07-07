{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
module Data.Array.Accelerate.Trafo.AD.Exp (
    module Data.Array.Accelerate.Trafo.AD.Exp,
    Idx(..), Val(..), idxToInt, prj
) where

import Data.GADT.Compare
import Data.GADT.Show

import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.AST as A
import Data.Array.Accelerate.AST (Idx(..), Val(..), idxToInt, prj)
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Shows
import Data.Array.Accelerate.Trafo.AD.Orphans ()


-- De Bruijn
-- ---------

data TagVal tag env where
    TEmpty :: TagVal tag ()
    TPush :: TagVal tag env -> tag -> TupleType t -> TagVal tag (env, t)

data LabVal lab env where
    LEmpty :: LabVal lab ()
    LPush :: LabVal lab env -> DLabel lab t -> LabVal lab (env, t)

-- Tuples
-- ------

data TupleIdx s t where
    TIHere  :: TupleIdx s s
    TILeft  :: TupleIdx s a -> TupleIdx s (a, b)
    TIRight :: TupleIdx s b -> TupleIdx s (a, b)

-- Expressions
-- -----------

data DLabel lab t =
    DLabel { labelType :: ScalarType t
           , labelLabel :: lab }
  deriving (Show)

data DLabels lab t where
    DLNil :: DLabels lab ()
    DLPair :: DLabels lab t1 -> DLabels lab t2 -> DLabels lab (t1, t2)
    DLScalar :: DLabel lab s -> DLabels lab s

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

    -- Use this VERY sparingly. It has no equivalent in the real AST, so must
    -- be laboriously back-converted using Let-bindings.
    Get     :: TupleType s
            -> TupleIdx s t
            -> OpenExp env lab t
            -> OpenExp env lab s

    Let     :: A.ELeftHandSide bnd_t env env'
            -> OpenExp env lab bnd_t
            -> OpenExp env' lab a
            -> OpenExp env lab a

    Var     :: A.ExpVar env t
            -> OpenExp env lab t

    Label   :: DLabels lab t
            -> OpenExp env lab t

type Exp = OpenExp ()

-- Closed expression with an unknown type
data AnyExp lab = forall t. AnyExp (Exp lab t)
deriving instance Show lab => Show (AnyExp lab)

data AnyTupleType = forall t. AnyTupleType (TupleType t)
deriving instance Show AnyTupleType

data AnyScalarType = forall t. AnyScalarType (ScalarType t)
deriving instance Show AnyScalarType

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

showDLabels :: (lab -> String) -> DLabels lab t -> String
showDLabels _ DLNil = "()"
showDLabels labf (DLScalar (DLabel ty lab)) =
    'L' : labf lab ++ " :: " ++ show ty
showDLabels labf (DLPair labs1 labs2) =
    "(" ++ showDLabels labf labs1 ++ ", " ++ showDLabels labf labs2 ++ ")"

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
showsExpr labf seed env d (Get _ ti e) = showParen (d > 10) $
    showString (tiPrefix ti) . showsExpr labf seed env 10 e
  where
    tiPrefix :: TupleIdx s t -> String
    tiPrefix TIHere = ""
    tiPrefix (TILeft ti') = "fst " ++ tiPrefix ti'
    tiPrefix (TIRight ti') = "snd " ++ tiPrefix ti'
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
showsExpr labf _ _ d (Label labs) = showParen (d > 0) $
    showString (showDLabels labf labs)

-- instance Show (OpenExp env Int t) where
--     showsPrec = showsExpr subscript 0 []

instance Show lab => Show (OpenExp env lab t) where
    showsPrec = showsExpr show 0 []

instance Show lab => GShow (DLabel lab) where
    gshowsPrec = showsPrec

instance Show lab => GShow (OpenExp env lab) where
    gshowsPrec = showsPrec

instance GEq (DLabel lab) where
    geq (DLabel ty1 _) (DLabel ty2 _) = do
        Refl <- geq ty1 ty2
        return Refl

instance Ord lab => GCompare (DLabel lab) where
    gcompare (DLabel ty1 lab1) (DLabel ty2 lab2) =
        case gcompare ty1 ty2 of
          GLT -> GLT
          GGT -> GGT
          GEQ -> case compare lab1 lab2 of
                   LT -> GLT
                   EQ -> GEQ
                   GT -> GGT

-- Auxiliary functions
-- -------------------

typeOf :: OpenExp env lab t -> TupleType t
typeOf (Const ty _) = TupRsingle ty
typeOf (PrimApp ty _ _) = ty
typeOf (Pair ty _ _) = ty
typeOf Nil = TupRunit
typeOf (Get ty _ _) = ty
typeOf (Let _ _ body) = typeOf body
typeOf (Var (A.Var ty _)) = TupRsingle ty
typeOf (Label labs) = dlabelsType labs

dlabelsType :: DLabels lab t -> TupleType t
dlabelsType DLNil = TupRunit
dlabelsType (DLScalar lab) = TupRsingle (labelType lab)
dlabelsType (DLPair t1 t2) = TupRpair (dlabelsType t1) (dlabelsType t2)

isInfixOp :: A.PrimFun ((a, b) -> c) -> Bool
isInfixOp (A.PrimAdd _) = True
isInfixOp (A.PrimMul _) = True
isInfixOp (A.PrimFDiv _) = True
isInfixOp (A.PrimLtEq _) = True
isInfixOp _ = False

precedence :: A.PrimFun sig -> Int
precedence (A.PrimAdd _) = 6
precedence (A.PrimMul _) = 7
precedence (A.PrimFDiv _) = 7
precedence (A.PrimNeg _) = 7  -- ?
precedence (A.PrimLog _) = 10
precedence (A.PrimLtEq _) = 4
precedence _ = 10  -- ?

data Fixity = Prefix | Infix
  deriving (Show)

prettyPrimFun :: Fixity -> A.PrimFun sig -> String
prettyPrimFun Infix (A.PrimAdd _) = "+"
prettyPrimFun Infix (A.PrimMul _) = "*"
prettyPrimFun Infix (A.PrimFDiv _) = "/"
prettyPrimFun Infix (A.PrimNeg _) = "-"
prettyPrimFun Infix (A.PrimLtEq _) = "<="
prettyPrimFun Prefix (A.PrimLog _) = "log"
prettyPrimFun Prefix op = '(' : prettyPrimFun Infix op ++ ")"
prettyPrimFun fixity op =
    error ("prettyPrimFun: not defined for " ++ show fixity ++ " " ++ showPrimFun op)

pickDLabels :: TupleIdx t' t -> DLabels lab t -> DLabels lab t'
pickDLabels TIHere labs = labs
pickDLabels (TILeft path) (DLPair lab _) = pickDLabels path lab
pickDLabels (TIRight path) (DLPair _ lab) = pickDLabels path lab
pickDLabels _ _ = error "pickDLabels: impossible GADTs"

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

data FoundTag env = forall t. FoundTag (ScalarType t) (Idx env t)

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
    | Just Refl <- matchScalarType ty ty2
    , lab == lab2 = Just ZeroIdx
    | otherwise =
        case labValFind env target of
            Just idx -> Just (SuccIdx idx)
            Nothing -> Nothing

labValFinds :: Eq lab => LabVal lab env -> DLabels lab t -> Maybe (A.ExpVars env t)
labValFinds labelenv labs = case labs of
    DLNil -> Just A.VarsNil
    DLScalar lab ->
        A.VarsSingle . A.Var (labelType lab)
            <$> labValFind labelenv lab
    DLPair labs1 labs2 ->
        A.VarsPair <$> labValFinds labelenv labs1
                   <*> labValFinds labelenv labs2

fmapLabel :: (lab -> lab') -> DLabel lab t -> DLabel lab' t
fmapLabel f (DLabel ty lab) = DLabel ty (f lab)

fmapLabels :: (lab -> lab') -> DLabels lab t -> DLabels lab' t
fmapLabels _ DLNil = DLNil
fmapLabels f (DLScalar lab) = DLScalar (fmapLabel f lab)
fmapLabels f (DLPair labs1 labs2) =
    DLPair (fmapLabels f labs1) (fmapLabels f labs2)

labValToList :: LabVal lab env -> [(AnyScalarType, lab)]
labValToList LEmpty = []
labValToList (LPush env (DLabel ty lab)) =
    (AnyScalarType ty, lab) : labValToList env

evars :: A.ExpVars env t -> OpenExp env lab t
evars = snd . evars'
  where
    evars' :: A.ExpVars env t -> (TupleType t, OpenExp env lab t)
    evars' A.VarsNil = (TupRunit, Nil)
    evars' (A.VarsSingle var@(A.Var ty _)) = (TupRsingle ty, Var var)
    evars' (A.VarsPair vars1 vars2) =
        let (t1, e1) = evars' vars1
            (t2, e2) = evars' vars2
        in (TupRpair t1 t2, Pair (TupRpair t1 t2) e1 e2)
