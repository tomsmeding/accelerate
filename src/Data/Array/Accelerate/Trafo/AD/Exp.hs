{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Accelerate.Trafo.AD.Exp (
    module Data.Array.Accelerate.Trafo.AD.Exp,
    Idx(..), idxToInt
) where

import Data.Dependent.Map (DMap)
import Data.List (intercalate)
import Data.GADT.Show
import Data.Some

import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (ShapeR(..), shapeType)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.AST as A
import Data.Array.Accelerate.AST (ELeftHandSide)
import qualified Data.Array.Accelerate.AST.Environment as A
import qualified Data.Array.Accelerate.AST.Idx as A
import Data.Array.Accelerate.AST.LeftHandSide
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Shows
import qualified Data.Array.Accelerate.Sugar.Tag as A
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Orphans ()
import qualified Data.Array.Accelerate.Trafo.Substitution as A (rebuildLHS)


-- Expressions
-- -----------

data OpenExp env aenv lab alab args tenv t where
    Const     :: EDLabelNS lab t
              -> t
              -> OpenExp env aenv lab alab args tenv t

    PrimApp   :: EDLabelN lab r
              -> A.PrimFun (a -> r)
              -> OpenExp env aenv lab alab args tenv a
              -> OpenExp env aenv lab alab args tenv r

    PrimConst :: EDLabelNS lab a
              -> A.PrimConst a
              -> OpenExp env aenv lab alab args tenv a

    Pair      :: EDLabelN lab (a, b)
              -> OpenExp env aenv lab alab args tenv a
              -> OpenExp env aenv lab alab args tenv b
              -> OpenExp env aenv lab alab args tenv (a, b)

    Nil       :: EDLabelN lab ()
              -> OpenExp env aenv lab alab args tenv ()

    Cond      :: EDLabelN lab a
              -> OpenExp env aenv lab alab args tenv A.PrimBool
              -> OpenExp env aenv lab alab args tenv a
              -> OpenExp env aenv lab alab args tenv a
              -> OpenExp env aenv lab alab args tenv a

    Shape     :: EDLabelN lab sh
              -> Either (A.ArrayVar aenv (Array sh e))
                        (AAnyPartLabelN alab (Array sh e))
              -> OpenExp env aenv lab alab args tenv sh

    -- The Bool label is an additional variable that always gets True
    -- stored in the primal. The point is that if the Index is inside
    -- a Cond, the label will have False if its branch wasn't taken --
    -- because of the default-zero behaviour in the untaken branch.
    -- This then lets the dual know whether the Index was executed.
    Index     :: EDLabelN lab e
              -> Either (A.ArrayVar aenv (Array sh e))
                        (AAnyPartLabelN alab (Array sh e))
              -> EDLabelNS lab A.PrimBool  -- whether the Index was executed
              -> OpenExp env aenv lab alab args tenv sh
              -> OpenExp env aenv lab alab args tenv e

    ShapeSize :: EDLabelNS lab Int
              -> ShapeR dim
              -> OpenExp env aenv lab alab args tenv dim
              -> OpenExp env aenv lab alab args tenv Int

    Get       :: EDLabelN lab s
              -> TupleIdx t s
              -> OpenExp env aenv lab alab args tenv t
              -> OpenExp env aenv lab alab args tenv s

    Undef     :: EDLabelNS lab t
              -> OpenExp env aenv lab alab args tenv t

    Let       :: ELeftHandSide bnd_t env env'
              -> OpenExp env aenv lab alab args tenv bnd_t
              -> OpenExp env' aenv lab alab args tenv a
              -> OpenExp env aenv lab alab args tenv a

    Var       :: EDLabelNS lab t  -- own label
              -> A.ExpVar env t   -- pointer to binding
              -> EPartLabelN lab rhs_t t  -- label of, and index into, referred-to right-hand side
              -> OpenExp env aenv lab alab args tenv t

    FreeVar   :: EDLabelNS lab t
              -> A.ExpVar tenv t
              -> OpenExp env aenv lab alab args tenv t

    Arg       :: EDLabelNS lab t
              -> TypeR args
              -> TupleIdx args t
              -> OpenExp env aenv lab alab args tenv t

type Exp = OpenExp ()

-- Expression-level function
data OpenFun env aenv lab alab tenv t where
    Body :: OpenExp env aenv lab alab () tenv t -> OpenFun env aenv lab alab tenv t
    Lam :: ELeftHandSide a env env' -> OpenFun env' aenv lab alab tenv t -> OpenFun env aenv lab alab tenv (a -> t)

type Fun = OpenFun ()

-- Instances
-- ---------

showsExp :: EShowEnv lab alab -> Int -> OpenExp env aenv lab alab args tenv t -> ShowS
showsExp se _ (Const lab x) =
    showString (showScalar (labelType lab) x) . eshowLabelSuffix se lab
showsExp se d (PrimApp lab f (Pair _ e1 e2))
  | isInfixOp f, "" <- eshowLabelSuffix se lab "" =
      let prec = precedence f
          ops = prettyPrimFun Infix f
      in showParen (d > prec) $
              showsExp se (prec+1) e1 . showString (' ' : ops ++ " ") .
                  showsExp se (prec+1) e2
showsExp se d (PrimApp lab f e) =
    let prec = precedence f
        ops = prettyPrimFun Prefix f
    in showParen (d > prec) $
            showString ops . eshowLabelSuffix se lab . showString " " .
                showsExp se (prec+1) e
showsExp se _ (PrimConst lab c) = showString (show c) . eshowLabelSuffix se lab
showsExp se _ (Pair lab e1 e2) =
    showString "(" . showsExp se 0 e1 . showString ", " .
        showsExp se 0 e2 . showString ")" . eshowLabelSuffix se lab
showsExp se _ (Nil lab) =
    showString "()" . eshowLabelSuffix se lab
showsExp se d (Cond lab c t e) =
    showParen (d > 10) $
        showString "cond" . eshowLabelSuffix se lab . showString " " .
            showsExp se 11 c . showString " " .
            showsExp se 11 t . showString " " .
            showsExp se 11 e
showsExp se d (Shape lab (Left (A.Var _ idx))) =
    showParen (d > 10) $
        showString "shape" . eshowLabelSuffix se lab . showString " " .
        (case drop (idxToInt idx) (seAenv se) of
            descr : _ -> showString descr
            [] -> showString ("tA_UP" ++ show (1 + idxToInt idx - length (seAenv se))))
showsExp se d (Shape lab (Right (AnyPartLabel partl))) =
    showParen (d > 10) $
        showString "shape" . eshowLabelSuffix se lab . showString " " .
        showString ("(" ++ showPartLabelSuffix (seAlabf se) partl "" ++ " :: " ++ show (partLabelSmallType partl) ++ ")")
showsExp se d (Index lab subj execLab e) =
    showParen (d > 10) $
        (case subj of
           Left (A.Var _ idx) ->
              case drop (idxToInt idx) (seAenv se) of
                  descr : _ -> showString descr
                  [] -> showString ("tA_UP" ++ show (1 + idxToInt idx - length (seAenv se)))
           Right (AnyPartLabel partl) ->
              showString (showPartLabelSuffix (seAlabf se) partl "" ++ " :: " ++ show (partLabelSmallType partl)))
        . showString " !" . eshowLabelSuffix se lab
        . case eshowLabelSuffix se execLab "" of
            "" -> showString ""
            str -> showString ("[exec=" ++ str ++ "]")
        . showString " "
        . showsExp se 11 e
showsExp se d (ShapeSize lab _ e) =
    showParen (d > 10) $
        showString "shapeSize" . eshowLabelSuffix se lab . showString " " .
        showsExp se 11 e
showsExp se d (Get lab ti e) =
    showParen (d > 10) $
        showString (tiPrefixExp ti) . eshowLabelSuffix se lab . showString " " .
        showsExp se (case ti of TIHere -> 10 ; _ -> 11) e
showsExp se _ (Undef lab) = showString "undef" . eshowLabelSuffix se lab
showsExp se d (Let lhs rhs body) = showParen (d > 0) $
    let (descr, descrs, seed') = namifyLHS (seSeed se) lhs
        env' = descrs ++ seEnv se
    in showString ("let " ++ descr ++ " = ") . showsExp (se { seSeed = seed' }) 0 rhs .
            showString " in " . showsExp (se { seSeed = seed', seEnv = env' }) 0 body
showsExp se _ (Var lab (A.Var _ idx) referLab) =
    let varstr
          | descr : _ <- drop (idxToInt idx) (seEnv se) = descr
          | otherwise = "tE_UP" ++ show (1 + idxToInt idx - length (seEnv se))
    in eshowVarRef se varstr referLab . eshowLabelSuffix se lab
showsExp se d (FreeVar lab (A.Var ty idx)) = showParen (d > 0) $
    showString ("tFREE" ++ show (1 + idxToInt idx)) . eshowLabelSuffix se lab .
    showString (" :: " ++ show ty)
showsExp se d (Arg lab _ tidx) = showParen (d > 0) $
    showString (case tiPrefixExp tidx of "" -> "A" ; pr -> "(" ++ pr ++ " A)")
    . eshowLabelSuffix se lab . showString (" :: " ++ show (labelType lab))

tiPrefix :: String -> String -> TupleIdx t t' -> String
tiPrefix fststr sndstr = intercalate "." . reverse . tiPrefix'
  where
    tiPrefix' :: TupleIdx t t' -> [String]
    tiPrefix' TIHere = []
    tiPrefix' (TILeft ti') = fststr : tiPrefix' ti'
    tiPrefix' (TIRight ti') = sndstr : tiPrefix' ti'

tiPrefixExp :: TupleIdx t t' -> String
tiPrefixExp = tiPrefix "fst" "snd"

compactTupleIdx :: TupleIdx t t' -> String
compactTupleIdx TIHere = ""
compactTupleIdx (TILeft ti) = 'f' : compactTupleIdx ti
compactTupleIdx (TIRight ti) = 's' : compactTupleIdx ti

showsFun :: EShowEnv lab alab -> Int -> OpenFun env aenv lab alab tenv t -> ShowS
showsFun se d (Body expr) = showsExp se d expr
showsFun se d (Lam lhs fun) =
    let (descr, descrs, seed') = namifyLHS (seSeed se) lhs
        env' = descrs ++ seEnv se
    in showParen (d > 0) $
        showString "\\" . showString descr .
          showString " -> " . showsFun (se { seSeed = seed', seEnv = env' }) 0 fun

showLabelSuffix :: (lab -> String) -> DLabel lty s lab t -> ShowS
showLabelSuffix labf lab =
    showString $ case labf (labelLabel lab) of
                   "" -> ""
                   "()" -> ""
                   res -> "[" ++ res ++ "]"

eshowLabelSuffix :: EShowEnv lab alab -> DLabel lty s lab t -> ShowS
eshowLabelSuffix = showLabelSuffix . seLabf

showPartLabelSuffix :: (lab -> String) -> PartLabel lty s lab t t' -> ShowS
showPartLabelSuffix labf (PartLabel lab part) =
    case showLabelSuffix labf lab "" of
      "" -> showString ""
      labStr -> showString (tiPrefixExp part ++ labStr)

showVarRef :: (lab -> String) -> String -> EPartLabelN lab t t' -> ShowS
showVarRef labf varstr lab =
    case showPartLabelSuffix labf lab "" of
      "" -> showString varstr
      referLabStr -> showString ("(" ++ varstr ++ "->" ++ referLabStr ++ ")")

eshowVarRef :: EShowEnv lab alab -> String -> EPartLabelN lab t t' -> ShowS
eshowVarRef = showVarRef . seLabf

instance (Show lab, Show alab) => Show (OpenExp env aenv lab alab args tenv t) where
    showsPrec = showsExp (ShowEnv show show 0 [] [])

instance (Show lab, Show alab) => GShow (OpenExp env aenv lab alab args tenv) where
    gshowsPrec = showsPrec

instance (Show lab, Show alab) => Show (OpenFun env aenv lab alab tenv t) where
    showsPrec = showsFun (ShowEnv show show 0 [] [])

-- Auxiliary functions
-- -------------------

elabelOf :: OpenExp env aenv lab alab args tenv t -> EDLabelN lab t
elabelOf (Const lab _) = tupleLabel lab
elabelOf (PrimApp lab _ _) = lab
elabelOf (PrimConst lab _) = tupleLabel lab
elabelOf (Pair lab _ _) = lab
elabelOf (Nil lab) = lab
elabelOf (Cond lab _ _ _) = lab
elabelOf (Shape lab _) = lab
elabelOf (Index lab _ _ _) = lab
elabelOf (ShapeSize lab _ _) = tupleLabel lab
elabelOf (Get lab _ _) = lab
elabelOf (Undef lab) = tupleLabel lab
elabelOf (Let _ _ body) = elabelOf body
elabelOf (Var lab _ _) = tupleLabel lab
elabelOf (FreeVar lab _) = tupleLabel lab
elabelOf (Arg lab _ _) = tupleLabel lab

etypeOf :: OpenExp env aenv lab alab args tenv t -> TypeR t
etypeOf = labelType . elabelOf

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
precedence (A.PrimNEq _) = 4
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
prettyPrimFun Infix (A.PrimNEq _) = "/="
prettyPrimFun Infix (A.PrimLt _) = "<"
prettyPrimFun Infix (A.PrimLtEq _) = "<="
prettyPrimFun Infix (A.PrimGt _) = ">"
prettyPrimFun Infix (A.PrimGtEq _) = ">="
prettyPrimFun Infix A.PrimLAnd = "&&!"
prettyPrimFun Infix (A.PrimIDiv _) = "`div`"
prettyPrimFun Prefix (A.PrimMod _) = "`mod`"
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

evars :: A.ExpVars env t -> OpenExp env aenv () alab args tenv t
evars TupRunit = Nil magicLabel
evars (TupRsingle var) = smartVar var
evars (TupRpair vars1 vars2) = smartPair (evars vars1) (evars vars2)

untupleExps :: TupR (OpenExp env aenv () alab args tenv) t -> OpenExp env aenv () alab args tenv t
untupleExps TupRunit = Nil magicLabel
untupleExps (TupRsingle e) = e
untupleExps (TupRpair t1 t2) = smartPair (untupleExps t1) (untupleExps t2)

-- Checks the expression does not contain labelised array variable references
generaliseLabA :: OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab' args tenv t
generaliseLabA (Const lab x) = Const lab x
generaliseLabA (PrimApp lab op ex) = PrimApp lab op (generaliseLabA ex)
generaliseLabA (PrimConst lab c) = PrimConst lab c
generaliseLabA (Pair lab e1 e2) = Pair lab (generaliseLabA e1) (generaliseLabA e2)
generaliseLabA (Nil lab) = Nil lab
generaliseLabA (Cond lab e1 e2 e3) = Cond lab (generaliseLabA e1) (generaliseLabA e2) (generaliseLabA e3)
generaliseLabA (Shape lab (Left avar)) = Shape lab (Left avar)
generaliseLabA (Shape _ (Right _)) = error "generaliseLabA: Shape with label found"
generaliseLabA (Index lab (Left avar) execLab e) = Index lab (Left avar) execLab (generaliseLabA e)
generaliseLabA (Index _ (Right _) _ _) = error "generaliseLabA: Index with label found"
generaliseLabA (ShapeSize lab sht e) = ShapeSize lab sht (generaliseLabA e)
generaliseLabA (Get lab path ex) = Get lab path (generaliseLabA ex)
generaliseLabA (Undef lab) = Undef lab
generaliseLabA (Let lhs rhs ex) = Let lhs (generaliseLabA rhs) (generaliseLabA ex)
generaliseLabA (Var lab v referLab) = Var lab v referLab
generaliseLabA (FreeVar lab v) = FreeVar lab v
generaliseLabA (Arg lab argsty tidx) = Arg lab argsty tidx

-- Checks the expression does not contain labelised array variable references
generaliseLabFunA :: OpenFun env aenv lab alab tenv t -> OpenFun env aenv lab alab' tenv t
generaliseLabFunA (Lam lhs fun) = Lam lhs (generaliseLabFunA fun)
generaliseLabFunA (Body ex) = Body (generaliseLabA ex)

-- Checks the expression does not contain array variables
generaliseAenv :: OpenExp env aenv lab alab args tenv t -> OpenExp env aenv' lab alab args tenv t
generaliseAenv (Const lab x) = Const lab x
generaliseAenv (PrimApp lab op ex) = PrimApp lab op (generaliseAenv ex)
generaliseAenv (PrimConst lab c) = PrimConst lab c
generaliseAenv (Pair lab e1 e2) = Pair lab (generaliseAenv e1) (generaliseAenv e2)
generaliseAenv (Nil lab) = Nil lab
generaliseAenv (Cond lab e1 e2 e3) = Cond lab (generaliseAenv e1) (generaliseAenv e2) (generaliseAenv e3)
generaliseAenv (Shape _ (Left _)) = error "generaliseAenv: Shape with array variable found"
generaliseAenv (Shape lab (Right referLab)) = Shape lab (Right referLab)
generaliseAenv (Index _ (Left _) _ _) = error "generaliseAenv: Index with array variable found"
generaliseAenv (Index lab (Right referLab) execLab e) = Index lab (Right referLab) execLab (generaliseAenv e)
generaliseAenv (ShapeSize lab sht e) = ShapeSize lab sht (generaliseAenv e)
generaliseAenv (Get lab path ex) = Get lab path (generaliseAenv ex)
generaliseAenv (Undef lab) = Undef lab
generaliseAenv (Let lhs rhs ex) = Let lhs (generaliseAenv rhs) (generaliseAenv ex)
generaliseAenv (Var lab v referLab) = Var lab v referLab
generaliseAenv (FreeVar lab v) = FreeVar lab v
generaliseAenv (Arg lab argsty tidx) = Arg lab argsty tidx

-- Checks the expression does not contain array variables
generaliseAenvFun :: OpenFun env aenv lab alab tenv t -> OpenFun env aenv' lab alab tenv t
generaliseAenvFun (Lam lhs fun) = Lam lhs (generaliseAenvFun fun)
generaliseAenvFun (Body ex) = Body (generaliseAenv ex)

elabelsOf :: OpenExp env aenv lab alab args tenv t -> [Some (EDLabelN lab)]
elabelsOf (Const lab _) = [Some (tupleLabel lab)]
elabelsOf (PrimApp lab _ ex) = Some lab : elabelsOf ex
elabelsOf (PrimConst lab _) = [Some (tupleLabel lab)]
elabelsOf (Pair _ e1 e2) = elabelsOf e1 ++ elabelsOf e2
elabelsOf (Nil lab) = [Some lab]
elabelsOf (Cond lab e1 e2 e3) = Some lab : elabelsOf e1 ++ elabelsOf e2 ++ elabelsOf e3
elabelsOf (Shape lab _) = [Some lab]
elabelsOf (Index lab _ execLab e) = Some lab : Some (tupleLabel execLab) : elabelsOf e
elabelsOf (ShapeSize lab _ e) = Some (tupleLabel lab) : elabelsOf e
elabelsOf (Get lab _ ex) = Some lab : elabelsOf ex
elabelsOf (Undef lab) = [Some (tupleLabel lab)]
elabelsOf (Let _ rhs ex) = elabelsOf rhs ++ elabelsOf ex
elabelsOf (Var lab _ _) = [Some (tupleLabel lab)]
elabelsOf (FreeVar lab _) = [Some (tupleLabel lab)]
elabelsOf (Arg lab _ _) = [Some (tupleLabel lab)]

-- TODO: These IndexInstantiators need some documentation
newtype IndexInstantiator idxadj sh t =
    IndexInstantiator
        (forall     env aenv alab args tenv.
            OpenExp env aenv () alab args tenv idxadj
         -> OpenExp env aenv () alab args tenv ((t, sh), A.PrimBool))

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
                      (TupR (AAnyPartLabelN alab) fv)
                      (TypeR tmp)
                      (TypeR idxadj)
                      (DMap (AAnyPartLabelN alab) (IndexInstantiators idxadj))

data SomeSplitLambdaAD t t' lab alab tenv =
    forall tmp idxadj. SomeSplitLambdaAD (SplitLambdaAD t t' lab alab tenv tmp idxadj)

sinkExp :: env A.:> env' -> OpenExp env aenv lab alab args tenv t -> OpenExp env' aenv lab alab args tenv t
sinkExp _ (Const lab x) = Const lab x
sinkExp k (PrimApp lab op e) = PrimApp lab op (sinkExp k e)
sinkExp _ (PrimConst lab c) = PrimConst lab c
sinkExp k (Pair lab e1 e2) = Pair lab (sinkExp k e1) (sinkExp k e2)
sinkExp _ (Nil lab) = Nil lab
sinkExp k (Cond lab c t e) = Cond lab (sinkExp k c) (sinkExp k t) (sinkExp k e)
sinkExp _ (Shape lab var) = Shape lab var
sinkExp k (Index lab var execLab idx) = Index lab var execLab (sinkExp k idx)
sinkExp k (ShapeSize lab sht e) = ShapeSize lab sht (sinkExp k e)
sinkExp k (Get lab ti e) = Get lab ti (sinkExp k e)
sinkExp _ (Undef lab) = Undef lab
sinkExp k (Let lhs rhs e)
  | Exists lhs' <- A.rebuildLHS lhs =
      Let lhs' (sinkExp k rhs) (sinkExp (A.sinkWithLHS lhs lhs' k) e)
sinkExp k (Var lab (A.Var sty idx) referLab) = Var lab (A.Var sty (k A.>:> idx)) referLab
sinkExp _ (FreeVar lab var) = FreeVar lab var
sinkExp _ (Arg lab argsty tidx) = Arg lab argsty tidx

sinkFun :: env A.:> env' -> OpenFun env aenv lab alab tenv t -> OpenFun env' aenv lab alab tenv t
sinkFun w (Body ex) = Body (sinkExp w ex)
sinkFun w (Lam lhs fun)
  | Exists lhs' <- A.rebuildLHS lhs
  = Lam lhs' (sinkFun (A.sinkWithLHS lhs lhs' w) fun)

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

expALabels :: OpenExp env aenv lab alab args tenv t -> [Some (AAnyPartLabelN alab)]
expALabels (Const _ _) = []
expALabels (PrimApp _ _ e) = expALabels e
expALabels (PrimConst _ _) = []
expALabels (Pair _ e1 e2) = expALabels e1 ++ expALabels e2
expALabels (Nil _) = []
expALabels (Cond _ c t e) = expALabels c ++ expALabels t ++ expALabels e
expALabels (Shape _ var) = either (const []) (pure . Some) var
expALabels (Index _ var _ e) = either (const []) (pure . Some) var ++ expALabels e
expALabels (ShapeSize _ _ e) = expALabels e
expALabels (Get _ _ e) = expALabels e
expALabels (Undef _) = []
expALabels (Let _ rhs e) = expALabels rhs ++ expALabels e
expALabels (Var _ _ _) = []
expALabels (FreeVar _ _) = []
expALabels (Arg _ _ _) = []

expFunALabels :: OpenFun env aenv lab alab tenv t -> [Some (AAnyPartLabelN alab)]
expFunALabels (Lam _ fun) = expFunALabels fun
expFunALabels (Body ex) = expALabels ex

expHasIndex :: OpenExp env aenv lab alab args tenv t -> Bool
expHasIndex (Const _ _) = False
expHasIndex (PrimApp _ _ e) = expHasIndex e
expHasIndex (PrimConst _ _) = False
expHasIndex (Pair _ e1 e2) = expHasIndex e1 || expHasIndex e2
expHasIndex (Nil _) = False
expHasIndex (Cond _ c t e) = expHasIndex c || expHasIndex t || expHasIndex e
expHasIndex (Shape _ _) = False
expHasIndex (Index _ _ _ _) = True
expHasIndex (ShapeSize _ _ e) = expHasIndex e
expHasIndex (Get _ _ e) = expHasIndex e
expHasIndex (Undef _) = False
expHasIndex (Let _ rhs e) = expHasIndex rhs || expHasIndex e
expHasIndex (Var _ _ _) = False
expHasIndex (FreeVar _ _) = False
expHasIndex (Arg _ _ _) = False


mkNothing :: forall env aenv alab args tenv t. TypeR t -> OpenExp env aenv () alab args tenv (A.PrimMaybe t)
mkNothing ty
  | [tag] <- [tag | ("Nothing", tag) <- A.tags @(Maybe t)] =
      smartPair (Const scalarLabel tag) (smartPair (Nil magicLabel) (untupleExps (fmapTupR (Undef . nilLabel) ty)))
  | otherwise = error "Maybe does not have a Just constructor?"

mkJust :: forall env aenv alab args tenv t. OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv (A.PrimMaybe t)
mkJust ex
  | [tag] <- [tag | ("Just", tag) <- A.tags @(Maybe t)] =
      smartPair (Const scalarLabel tag) (smartPair (Nil magicLabel) ex)
  | otherwise = error "Maybe does not have a Just constructor?"

mkBool :: Bool -> OpenExp env aenv () alab args tenv A.PrimBool
mkBool b
  | [tag] <- [tag | (name, tag) <- A.tags @Bool, name == constrName] =
      Const scalarLabel tag
  | otherwise = error $ "Bool does not have a " ++ constrName ++ " constructor?"
  where constrName = if b then "True" else "False"


smartPair :: OpenExp env aenv () alab args tenv a -> OpenExp env aenv () alab args tenv b -> OpenExp env aenv () alab args tenv (a, b)
smartPair a b = Pair (nilLabel (TupRpair (etypeOf a) (etypeOf b))) a b

smartNeg :: NumType t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t
smartNeg ty a = PrimApp (nilLabel (TupRsingle (SingleScalarType (NumSingleType ty)))) (A.PrimNeg ty) a

smartRecip :: FloatingType t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t
smartRecip ty a = PrimApp (nilLabel (TupRsingle (SingleScalarType (NumSingleType (FloatingNumType ty))))) (A.PrimRecip ty) a

smartAdd :: NumType t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t
smartAdd ty a b = PrimApp (nilLabel (TupRsingle (SingleScalarType (NumSingleType ty)))) (A.PrimAdd ty) (smartPair a b)

smartSub :: NumType t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t
smartSub ty a b = PrimApp (nilLabel (TupRsingle (SingleScalarType (NumSingleType ty)))) (A.PrimSub ty) (smartPair a b)

smartMul :: NumType t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t
smartMul ty a b = PrimApp (nilLabel (TupRsingle (SingleScalarType (NumSingleType ty)))) (A.PrimMul ty) (smartPair a b)

smartFDiv :: FloatingType t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t
smartFDiv ty a b = PrimApp (nilLabel (TupRsingle (SingleScalarType (NumSingleType (FloatingNumType ty))))) (A.PrimFDiv ty) (smartPair a b)

smartLAnd :: OpenExp env aenv () alab args tenv A.PrimBool -> OpenExp env aenv () alab args tenv A.PrimBool -> OpenExp env aenv () alab args tenv A.PrimBool
smartLAnd a b = PrimApp magicLabel A.PrimLAnd (smartPair a b)

smartEq :: SingleType t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv A.PrimBool
smartEq ty a b = PrimApp magicLabel (A.PrimEq ty) (smartPair a b)

smartLt :: SingleType t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv A.PrimBool
smartLt ty a b = PrimApp magicLabel (A.PrimLt ty) (smartPair a b)

smartGt :: SingleType t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv A.PrimBool
smartGt ty a b = PrimApp magicLabel (A.PrimGt ty) (smartPair a b)

smartMin :: SingleType t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t
smartMin ty a b = PrimApp (nilLabel (TupRsingle (SingleScalarType ty))) (A.PrimMin ty) (smartPair a b)

smartMax :: SingleType t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t
smartMax ty a b = PrimApp (nilLabel (TupRsingle (SingleScalarType ty))) (A.PrimMax ty) (smartPair a b)

smartVar :: A.ExpVar env t -> OpenExp env aenv () alab args tenv t
smartVar var@(A.Var ty _) = Var (nilLabel ty) var (PartLabel (tupleLabel (nilLabel ty)) TIHere)

smartCond :: OpenExp env aenv () alab args tenv A.PrimBool -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t
smartCond e1 e2 e3 = Cond (nilLabel (etypeOf e2)) e1 e2 e3

smartShape :: Either (A.ArrayVar aenv (Array sh e)) (AAnyPartLabelN alab (Array sh e)) -> OpenExp env aenv () alab args tenv sh
smartShape (Left var@(A.Var (ArrayR sht _) _)) = Shape (nilLabel (shapeType sht)) (Left var)
smartShape (Right lab@(AnyPartLabel partl)) = Shape (nilLabel (shapeType (arrayRshape (untupleA (partLabelSmallType partl))))) (Right lab)

smartIndex :: A.ArrayVar aenv (Array sh e) -> OpenExp env aenv () alab args tenv sh -> OpenExp env aenv () alab args tenv e
smartIndex var@(A.Var (ArrayR _ ty) _) idxexp = Index (nilLabel ty) (Left var) scalarLabel idxexp

-- TODO: make smartGet not quadratic when used repeatedly
smartGet :: TupleIdx t t' -> OpenExp env aenv () alab args tenv t -> OpenExp env aenv () alab args tenv t'
smartGet TIHere ex = ex
smartGet (TILeft tidx) (Pair _ ex _) = smartGet tidx ex
smartGet (TIRight tidx) (Pair _ _ ex) = smartGet tidx ex
smartGet tidx (Get (labelType -> ty) tidx' ex) =
    Get (nilLabel (pickTupR tidx ty)) (composeTIdx tidx' tidx) ex
smartGet tidx ex = Get (nilLabel (pickTupR tidx (etypeOf ex))) tidx ex

smartFst :: OpenExp env aenv () alab args tenv (t1, t2) -> OpenExp env aenv () alab args tenv t1
smartFst = smartGet (TILeft TIHere)

smartSnd :: OpenExp env aenv () alab args tenv (t1, t2) -> OpenExp env aenv () alab args tenv t2
smartSnd = smartGet (TIRight TIHere)
