{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.Exp (
    module Data.Array.Accelerate.Trafo.AD.Exp,
    Idx(..), idxToInt
) where

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
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Orphans ()
import qualified Data.Array.Accelerate.Trafo.Substitution as A (weakenVars)


type ELabVal = LabVal ScalarType

type EDLabel = DLabel ScalarType
type EDLabelT = DLabel TypeR


-- Expressions
-- -----------

-- TODO: Check how many reified types can be removed in this AST
data OpenExp env aenv lab alab args t where
    Const   :: ScalarType t
            -> t
            -> OpenExp env aenv lab alab args t

    PrimApp :: TypeR r
            -> A.PrimFun (a -> r)
            -> OpenExp env aenv lab alab args a
            -> OpenExp env aenv lab alab args r

    Pair    :: TypeR (a, b)
            -> OpenExp env aenv lab alab args a
            -> OpenExp env aenv lab alab args b
            -> OpenExp env aenv lab alab args (a, b)

    Nil     :: OpenExp env aenv lab alab args ()

    Cond    :: TypeR a
            -> OpenExp env aenv lab alab args A.PrimBool
            -> OpenExp env aenv lab alab args a
            -> OpenExp env aenv lab alab args a
            -> OpenExp env aenv lab alab args a

    Shape   :: Either (A.ArrayVar aenv (Array sh e))
                      (DLabel ArrayR alab (Array sh e))
            -> OpenExp env aenv lab alab args sh

    Index   :: Either (A.ArrayVar aenv (Array sh e))
                      (DLabel ArrayR alab (Array sh e))
            -> OpenExp env aenv lab alab args sh
            -> OpenExp env aenv lab alab args e

    ShapeSize :: ShapeR dim
              -> OpenExp env aenv lab alab args dim
              -> OpenExp env aenv lab alab args Int

    -- Use this VERY sparingly. It has no equivalent in the real AST, so must
    -- be laboriously back-converted using Let-bindings.
    Get     :: TypeR s
            -> TupleIdx t s
            -> OpenExp env aenv lab alab args t
            -> OpenExp env aenv lab alab args s

    Let     :: A.ELeftHandSide bnd_t env env'
            -> OpenExp env aenv lab alab args bnd_t
            -> OpenExp env' aenv lab alab args a
            -> OpenExp env aenv lab alab args a

    Var     :: A.ExpVar env t
            -> OpenExp env aenv lab alab args t

    Arg     :: ScalarType t
            -> Idx args t
            -> OpenExp env aenv lab alab args t

    Label   :: EDLabelT lab t
            -> OpenExp env aenv lab alab args t

type Exp = OpenExp ()

-- Expression-level function
data OpenFun env aenv lab alab t where
    Body :: OpenExp env aenv lab alab () t -> OpenFun env aenv lab alab t
    Lam :: A.ELeftHandSide a env env' -> OpenFun env' aenv lab alab t -> OpenFun env aenv lab alab (a -> t)

type Fun = OpenFun ()

-- Closed expression with an unknown type
data AnyExp aenv lab alab args = forall t. AnyExp (Exp aenv lab alab args t)
deriving instance (Show lab, Show alab) => Show (AnyExp aenv lab alab args)

data AnyTypeR = forall t. AnyTypeR (TypeR t)
deriving instance Show AnyTypeR

data AnyScalarType = forall t. AnyScalarType (ScalarType t)
deriving instance Show AnyScalarType

-- Instances
-- ---------

showsExp :: EShowEnv lab alab -> Int -> OpenExp env aenv lab alab args t -> ShowS
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
            [] -> error $ "Avar out of aenv range in showsExp: " ++
                          show (idxToInt idx) ++ " in " ++ show (seAenv se))
showsExp se d (Shape (Right lab)) =
    showParen (d > 10) $
        showString "shape " .
        showString ("(L" ++ seAlabf se (labelLabel lab) ++ " :: " ++ show (labelType lab) ++ ")")
showsExp se d (Index (Left (A.Var _ idx)) e) =
    showParen (d > 10) $
        (case drop (idxToInt idx) (seAenv se) of
            descr : _ -> showString descr
            [] -> error $ "Avar out of aenv range in showsExp: " ++
                          show (idxToInt idx) ++ " in " ++ show (seAenv se))
        . showString " ! " . showsExp se 11 e
showsExp se d (Index (Right lab) e) =
    showParen (d > 10) $
        showString ('L' : seAlabf se (labelLabel lab) ++ " :: " ++ show (labelType lab))
        . showString " ! " . showsExp se 11 e
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
        [] -> error $ "Var out of env range in showsExp: " ++
                      show (idxToInt idx) ++ " in " ++ show (seEnv se)
showsExp se d (Label lab) = showParen (d > 0) $
    showString ('L' : seLabf se (labelLabel lab) ++ " :: " ++ show (labelType lab))

-- instance Show (OpenExp env Int t) where
--     showsPrec = showsExp subscript 0 []

instance (Show lab, Show alab) => Show (OpenExp env aenv lab alab args t) where
    showsPrec = showsExp (ShowEnv show show 0 [] [])

instance (Show lab, Show alab) => GShow (OpenExp env aenv lab alab args) where
    gshowsPrec = showsPrec

-- Auxiliary functions
-- -------------------

etypeOf :: OpenExp env aenv lab alab args t -> TypeR t
etypeOf (Const ty _) = TupRsingle ty
etypeOf (PrimApp ty _ _) = ty
etypeOf (Pair ty _ _) = ty
etypeOf Nil = TupRunit
etypeOf (Cond ty _ _ _) = ty
etypeOf (Shape (Left (A.Var (ArrayR sht _) _))) = shapeType sht
etypeOf (Shape (Right (DLabel (ArrayR sht _) _))) = shapeType sht
etypeOf (Index (Left (A.Var (ArrayR _ ty) _)) _) = ty
etypeOf (Index (Right (DLabel (ArrayR _ ty) _)) _) = ty
etypeOf (ShapeSize _ _) = TupRsingle scalarType
etypeOf (Get ty _ _) = ty
etypeOf (Let _ _ body) = etypeOf body
etypeOf (Var (A.Var ty _)) = TupRsingle ty
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
isInfixOp _ = False

precedence :: A.PrimFun sig -> Int
precedence (A.PrimAdd _) = 6
precedence (A.PrimSub _) = 6
precedence (A.PrimMul _) = 7
precedence (A.PrimFDiv _) = 7
precedence (A.PrimNeg _) = 7  -- ?
precedence (A.PrimRecip _) = 10
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
prettyPrimFun Infix (A.PrimSub _) = "-"
prettyPrimFun Infix (A.PrimMul _) = "*"
prettyPrimFun Infix (A.PrimFDiv _) = "/"
prettyPrimFun Infix (A.PrimNeg _) = "-"
prettyPrimFun Infix (A.PrimLt _) = "<"
prettyPrimFun Infix (A.PrimLtEq _) = "<="
prettyPrimFun Infix (A.PrimGt _) = ">"
prettyPrimFun Infix (A.PrimGtEq _) = ">="
prettyPrimFun Infix (A.PrimIDiv _) = "`div`"
prettyPrimFun Prefix (A.PrimRecip _) = "recip"
prettyPrimFun Prefix (A.PrimLog _) = "log"
prettyPrimFun Prefix (A.PrimExpFloating _) = "exp"
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

evars :: A.ExpVars env t -> OpenExp env aenv lab alab args t
evars = snd . evars'
  where
    evars' :: A.ExpVars env t -> (TypeR t, OpenExp env aenv lab alab args t)
    evars' TupRunit = (TupRunit, Nil)
    evars' (TupRsingle var@(A.Var ty _)) = (TupRsingle ty, Var var)
    evars' (TupRpair vars1 vars2) =
        let (t1, e1) = evars' vars1
            (t2, e2) = evars' vars2
        in (TupRpair t1 t2, Pair (TupRpair t1 t2) e1 e2)

-- Assumes the expression does not contain Label
generaliseLab :: OpenExp env aenv lab alab args t -> OpenExp env aenv lab' alab args t
generaliseLab (Const ty x) = Const ty x
generaliseLab (PrimApp ty op ex) = PrimApp ty op (generaliseLab ex)
generaliseLab (Pair ty e1 e2) = Pair ty (generaliseLab e1) (generaliseLab e2)
generaliseLab Nil = Nil
generaliseLab (Cond ty e1 e2 e3) = Cond ty (generaliseLab e1) (generaliseLab e2) (generaliseLab e3)
generaliseLab (Shape (Left avar)) = Shape (Left avar)
generaliseLab (Shape (Right alab)) = Shape (Right alab)
generaliseLab (Index (Left avar) e) = Index (Left avar) (generaliseLab e)
generaliseLab (Index (Right alab) e) = Index (Right alab) (generaliseLab e)
generaliseLab (ShapeSize sht e) = ShapeSize sht (generaliseLab e)
generaliseLab (Get ty path ex) = Get ty path (generaliseLab ex)
generaliseLab (Let lhs rhs ex) = Let lhs (generaliseLab rhs) (generaliseLab ex)
generaliseLab (Var v) = Var v
generaliseLab (Arg ty idx) = Arg ty idx
generaliseLab (Label _) = error "generaliseLab: Label found"

-- Assumes the expression does not contain labeled array variable references
generaliseLabA :: OpenExp env aenv lab alab args t -> OpenExp env aenv lab alab' args t
generaliseLabA (Const ty x) = Const ty x
generaliseLabA (PrimApp ty op ex) = PrimApp ty op (generaliseLabA ex)
generaliseLabA (Pair ty e1 e2) = Pair ty (generaliseLabA e1) (generaliseLabA e2)
generaliseLabA Nil = Nil
generaliseLabA (Cond ty e1 e2 e3) = Cond ty (generaliseLabA e1) (generaliseLabA e2) (generaliseLabA e3)
generaliseLabA (Shape (Left avar)) = Shape (Left avar)
generaliseLabA (Shape (Right _)) = error "generaliseLabA: Shape with label found"
generaliseLabA (Index (Left avar) e) = Index (Left avar) (generaliseLabA e)
generaliseLabA (Index (Right _) _) = error "generaliseLabA: Index with label found"
generaliseLabA (ShapeSize sht e) = ShapeSize sht (generaliseLabA e)
generaliseLabA (Get ty path ex) = Get ty path (generaliseLabA ex)
generaliseLabA (Let lhs rhs ex) = Let lhs (generaliseLabA rhs) (generaliseLabA ex)
generaliseLabA (Var v) = Var v
generaliseLabA (Arg ty idx) = Arg ty idx
generaliseLabA (Label lab) = Label lab

fmapAlabExp :: (forall ty. DLabel ArrayR alab ty -> DLabel ArrayR alab' ty)
            -> OpenExp env aenv lab alab args t
            -> OpenExp env aenv lab alab' args t
fmapAlabExp f ex = case ex of
    Const ty x -> Const ty x
    PrimApp ty op e -> PrimApp ty op (fmapAlabExp f e)
    Pair ty e1 e2 -> Pair ty (fmapAlabExp f e1) (fmapAlabExp f e2)
    Nil -> Nil
    Cond ty e1 e2 e3 -> Cond ty (fmapAlabExp f e1) (fmapAlabExp f e2) (fmapAlabExp f e3)
    Shape ref -> Shape (f <$> ref)
    Index ref e -> Index (f <$> ref) (fmapAlabExp f e)
    ShapeSize sht e -> ShapeSize sht (fmapAlabExp f e)
    Get ty ti e -> Get ty ti (fmapAlabExp f e)
    Let lhs rhs e -> Let lhs (fmapAlabExp f rhs) (fmapAlabExp f e)
    Arg ty idx -> Arg ty idx
    Var var -> Var var
    Label lab -> Label lab

fmapAlabFun :: (forall ty. DLabel ArrayR alab ty -> DLabel ArrayR alab' ty)
            -> OpenFun env aenv lab alab t
            -> OpenFun env aenv lab alab' t
fmapAlabFun f (Lam lhs fun) = Lam lhs (fmapAlabFun f fun)
fmapAlabFun f (Body ex) = Body (fmapAlabExp f ex)

data SplitLambdaAD t t' lab alab sh =
    forall fv tmp.
        SplitLambdaAD (forall aenv. A.ArrayVars aenv fv -> Fun aenv lab alab (t -> (t', tmp)))
                      (forall aenv. A.ArrayVars aenv fv -> Fun aenv lab alab ((t', tmp) -> t))
                      (TupR (DLabel ArrayR alab) fv)
                      (TypeR tmp, DLabel ArrayR alab (Array sh tmp))

fmapAlabSplitLambdaAD :: (forall ty. DLabel ArrayR alab ty -> DLabel ArrayR alab' ty)
                      -> SplitLambdaAD t t' lab alab sh
                      -> SplitLambdaAD t t' lab alab' sh
fmapAlabSplitLambdaAD f (SplitLambdaAD f1 f2 tup (ty, lab)) =
    SplitLambdaAD (fmapAlabFun f . f1) (fmapAlabFun f . f2)
                  (fmapTupR f tup)
                  (ty, f lab)

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

sinkExp :: env A.:> env' -> OpenExp env aenv lab alab args t -> OpenExp env' aenv lab alab args t
sinkExp _ (Const ty x) = Const ty x
sinkExp k (PrimApp ty op e) = PrimApp ty op (sinkExp k e)
sinkExp k (Pair ty e1 e2) = Pair ty (sinkExp k e1) (sinkExp k e2)
sinkExp _ Nil = Nil
sinkExp k (Cond ty c t e) = Cond ty (sinkExp k c) (sinkExp k t) (sinkExp k e)
sinkExp _ (Shape var) = Shape var
sinkExp k (Index var e) = Index var (sinkExp k e)
sinkExp k (ShapeSize sht e) = ShapeSize sht (sinkExp k e)
sinkExp k (Get ty ti e) = Get ty ti (sinkExp k e)
sinkExp k (Let lhs rhs e)
  | GenLHS lhs' <- generaliseLHS lhs =
      Let lhs' (sinkExp k rhs) (sinkExp (A.sinkWithLHS lhs lhs' k) e)
sinkExp k (Var (A.Var sty idx)) = Var (A.Var sty (k A.>:> idx))
sinkExp _ (Arg ty idx) = Arg ty idx
sinkExp _ (Label lab) = Label lab

expALabels :: OpenExp env aenv lab alab args t -> [AnyLabel ArrayR alab]
expALabels (Const _ _) = []
expALabels (PrimApp _ _ e) = expALabels e
expALabels (Pair _ e1 e2) = expALabels e1 ++ expALabels e2
expALabels Nil = []
expALabels (Cond _ c t e) = expALabels c ++ expALabels t ++ expALabels e
expALabels (Shape var) = either (const []) (pure . AnyLabel) var
expALabels (Index var e) = either (const []) (pure . AnyLabel) var ++ expALabels e
expALabels (ShapeSize _ e) = expALabels e
expALabels (Get _ _ e) = expALabels e
expALabels (Let _ rhs e) = expALabels rhs ++ expALabels e
expALabels (Var _) = []
expALabels (Arg _ _) = []
expALabels (Label _) = []

expFunALabels :: OpenFun env aenv lab alab t -> [AnyLabel ArrayR alab]
expFunALabels (Lam _ fun) = expFunALabels fun
expFunALabels (Body ex) = expALabels ex


-- TODO: Don't hard-code 1, but derive it from a non-g version of gtags in Sugar.Elt.
mkJust :: OpenExp env aenv lab alab args t -> OpenExp env aenv lab alab args (A.PrimMaybe t)
mkJust ex =
    let sndty = TupRpair TupRunit (etypeOf ex)
    in Pair (TupRpair (TupRsingle scalarType) sndty) (Const scalarType 1) (Pair sndty Nil ex)
