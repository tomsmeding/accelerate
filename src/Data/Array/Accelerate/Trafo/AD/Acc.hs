{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
module Data.Array.Accelerate.Trafo.AD.Acc (
    module Data.Array.Accelerate.Trafo.AD.Acc,
    Idx(..), idxToInt
) where

import Data.List (intercalate)
import Data.GADT.Show

import Data.Array.Accelerate.Representation.Array hiding ((!!))
import Data.Array.Accelerate.Representation.Type
import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.Orphans ()


type ALabVal = LabVal ArrayR

type ADLabel = DLabel ArrayR
type ADLabelT = DLabel ArraysR


-- Array programs
-- --------------

type ExpLambda1 aenv lab alab sh t1 t2 =
    Either (SplitLambdaAD t1 t2 lab alab sh)
           (Fun aenv lab alab (t1 -> t2))

-- TODO: Check how many reified types can be removed in this AST
data OpenAcc aenv lab alab args t where
    Aconst  :: ArrayR (Array sh t)
            -> Array sh t
            -> OpenAcc aenv lab alab args (Array sh t)

    Apair   :: ArraysR (a, b)
            -> OpenAcc aenv lab alab args a
            -> OpenAcc aenv lab alab args b
            -> OpenAcc aenv lab alab args (a, b)

    Anil    :: OpenAcc aenv lab alab args ()

    Acond   :: ArraysR a
            -> Exp aenv lab alab () A.PrimBool
            -> OpenAcc aenv lab alab args a
            -> OpenAcc aenv lab alab args a
            -> OpenAcc aenv lab alab args a

    Map     :: ArrayR (Array sh t2)
            -> ExpLambda1 aenv lab alab sh t1 t2
            -> OpenAcc aenv lab alab args (Array sh t1)
            -> OpenAcc aenv lab alab args (Array sh t2)

    ZipWith :: ArrayR (Array sh t3)
            -> ExpLambda1 aenv lab alab sh (t1, t2) t3
            -> OpenAcc aenv lab alab args (Array sh t1)
            -> OpenAcc aenv lab alab args (Array sh t2)
            -> OpenAcc aenv lab alab args (Array sh t3)

    Fold    :: ArrayR (Array sh e)
            -> ExpLambda1 aenv lab alab sh (e, e) e
            -> Maybe (Exp aenv lab alab () e)
            -> OpenAcc aenv lab alab args (Array (sh, Int) e)
            -> OpenAcc aenv lab alab args (Array sh e)

    Generate :: ArrayR (Array sh e)
             -> Exp aenv lab alab () sh
             -> ExpLambda1 aenv lab alab sh sh e
             -> OpenAcc aenv lab alab args (Array sh e)

    -- Use this VERY sparingly. It has no equivalent in the real AST, so must
    -- be laboriously back-converted using Let-bindings.
    Aget    :: ArraysR s
            -> TupleIdx t s
            -> OpenAcc env lab alab args t
            -> OpenAcc env lab alab args s

    Alet    :: A.ALeftHandSide bnd_t env env'
            -> OpenAcc env lab alab args bnd_t
            -> OpenAcc env' lab alab args a
            -> OpenAcc env lab alab args a

    Avar    :: A.ArrayVar env (Array sh e)
            -> OpenAcc env lab alab args (Array sh e)

    Aarg    :: ArrayR t
            -> Idx args t
            -> OpenAcc env lab alab args t

    Alabel  :: ADLabelT alab t
            -> OpenAcc env lab alab args t

    Asnowman :: OpenAcc env lab alab args t

type Acc = OpenAcc ()

-- Closed array program with an unknown type
data AnyAcc lab alab args = forall t. AnyAcc (Acc lab alab args t)
deriving instance (Show lab, Show alab) => Show (AnyAcc lab alab args)

data AnyArraysR = forall t. AnyArraysR (ArraysR t)
deriving instance Show AnyArraysR

data AnyArrayR = forall t. AnyArrayR (ArrayR t)
deriving instance Show AnyArrayR

-- Instances
-- ---------

showsAcc :: (lab -> String) -> (alab -> String) -> Int -> [String] -> Int -> OpenAcc env lab alab args t -> ShowS
showsAcc _ _ _ _ _ (Aconst ty x) =
    showString (showArray (showString . showTupR' showScalar (arrayRtype ty)) ty x)
showsAcc labf alabf seed env _ (Apair _ e1 e2) =
    showString "(" . showsAcc labf alabf seed env 0 e1 . showString ", " .
        showsAcc labf alabf seed env 0 e2 . showString ")"
showsAcc _ _ _ _ _ Anil =
    showString "()"
showsAcc labf alabf seed env d (Acond _ c t e) =
    showParen (d > 10) $
        showString "acond " .
            showsExp labf alabf seed [] env 11 c . showString " " .
            showsAcc labf alabf seed env 11 t . showString " " .
            showsAcc labf alabf seed env 11 e
showsAcc labf alabf seed env d (Map _ f e) =
    showParen (d > 10) $
        showString "map " .
            showsLambda labf alabf seed [] env 11 f . showString " " .
            showsAcc labf alabf seed env 11 e
showsAcc labf alabf seed env d (ZipWith _ f e1 e2) =
    showParen (d > 10) $
        showString "zipWith " .
            showsLambda labf alabf seed [] env 11 f . showString " " .
            showsAcc labf alabf seed env 11 e1 . showString " " .
            showsAcc labf alabf seed env 11 e2
showsAcc labf alabf seed env d (Fold _ f me0 e) =
    showParen (d > 10) $
        showString (maybe "fold1 " (const "fold ") me0) .
            showsLambda labf alabf seed [] env 11 f . showString " " .
            maybe id (\e0 -> showsExp labf alabf seed [] env 11 e0 . showString " ") me0 .
            showsAcc labf alabf seed env 11 e
showsAcc labf alabf seed env d (Generate _ sh f) =
    showParen (d > 10) $
        showString "generate " .
            showsExp labf alabf seed [] env 11 sh . showString " " .
            showsLambda labf alabf seed [] env 11 f
showsAcc labf alabf seed env d (Aget _ ti e) = showParen (d > 10) $
    showString (tiPrefix ti) . showsAcc labf alabf seed env 10 e
  where
    tiPrefix :: TupleIdx t t' -> String
    tiPrefix = (++ " ") . intercalate "." . reverse . tiPrefix'

    tiPrefix' :: TupleIdx t t' -> [String]
    tiPrefix' TIHere = []
    tiPrefix' (TILeft ti') = "afst" : tiPrefix' ti'
    tiPrefix' (TIRight ti') = "asnd" : tiPrefix' ti'
showsAcc labf alabf seed env d (Alet lhs rhs body) = showParen (d > 0) $
    let (descr, descrs, seed') = namifyLHS seed lhs
        env' = descrs ++ env
    in showString ("let " ++ descr ++ " = ") . showsAcc labf alabf seed' env 0 rhs .
            showString " in " . showsAcc labf alabf seed' env' 0 body
showsAcc _ _ _ _ d (Aarg ty idx) = showParen (d > 0) $
    showString ('A' : show (idxToInt idx) ++ " :: " ++ show ty)
showsAcc _ _ _ env _ (Avar (A.Var _ idx)) =
    case drop (idxToInt idx) env of
        descr : _ -> showString descr
        [] -> error $ "Var out of env range in showsAcc: " ++
                      show (idxToInt idx) ++ " in " ++ show env
showsAcc _ alabf _ _ d (Alabel lab) = showParen (d > 0) $
    showString ('L' : alabf (labelLabel lab) ++ " :: " ++ show (labelType lab))
showsAcc _ _ _ _ _ Asnowman = showString "⛄"

showsFun :: (lab -> String) -> (alab -> String) -> Int -> [String] -> [String] -> Int -> OpenFun env aenv lab alab t -> ShowS
showsFun labf alabf seed env aenv d (Body expr) = showsExp labf alabf seed env aenv d expr
showsFun labf alabf seed env aenv d (Lam lhs fun) =
    let (descr, descrs, seed') = namifyLHS seed lhs
        env' = descrs ++ env
    in showParen (d > 0) $
        showString "\\" . showString descr .
        showString " -> " . showsFun labf alabf seed' env' aenv 0 fun

showsLambda :: (lab -> String) -> (alab -> String) -> Int -> [String] -> [String] -> Int -> ExpLambda1 aenv lab alab sh t1 t2 -> ShowS
showsLambda labf alabf seed env aenv d (Right fun) = showsFun labf alabf seed env aenv d fun
showsLambda _ _ _ _ _ _ (Left _) = showString "{splitlambda}"

instance (Show lab, Show alab) => Show (OpenAcc aenv lab alab args t) where
    showsPrec = showsAcc show show 0 []

instance (Show lab, Show alab) => GShow (OpenAcc aenv lab alab args) where
    gshowsPrec = showsPrec

-- Auxiliary functions
-- -------------------

atypeOf :: OpenAcc aenv lab alab args t -> ArraysR t
atypeOf (Aconst ty _) = TupRsingle ty
atypeOf (Apair ty _ _) = ty
atypeOf Anil = TupRunit
atypeOf (Acond ty _ _ _) = ty
atypeOf (Map ty _ _) = TupRsingle ty
atypeOf (ZipWith ty _ _ _) = TupRsingle ty
atypeOf (Generate ty _ _) = TupRsingle ty
atypeOf (Fold ty _ _ _) = TupRsingle ty
atypeOf (Aget ty _ _) = ty
atypeOf (Alet _ _ body) = atypeOf body
atypeOf (Avar (A.Var ty _)) = TupRsingle ty
atypeOf (Aarg ty _) = TupRsingle ty
atypeOf (Alabel lab) = labelType lab

alabValFind :: Eq lab => ALabVal lab env -> ADLabel lab t -> Maybe (Idx env t)
alabValFind LEmpty _ = Nothing
alabValFind (LPush env (DLabel ty lab)) target@(DLabel ty2 lab2)
    | Just Refl <- matchArrayR ty ty2
    , lab == lab2 = Just ZeroIdx
    | otherwise = SuccIdx <$> alabValFind env target

alabValFinds :: Eq lab => ALabVal lab env -> TupR (DLabel ArrayR lab) t -> Maybe (A.ArrayVars env t)
alabValFinds _ TupRunit = Just TupRunit
alabValFinds labelenv (TupRsingle lab) =
    TupRsingle . A.Var (labelType lab) <$> alabValFind labelenv lab
alabValFinds labelenv (TupRpair labs1 labs2) =
    TupRpair <$> alabValFinds labelenv labs1 <*> alabValFinds labelenv labs2

alabValToList :: ALabVal lab env -> [(AnyArrayR, lab)]
alabValToList LEmpty = []
alabValToList (LPush env (DLabel ty lab)) =
    (AnyArrayR ty, lab) : alabValToList env

avars :: A.ArrayVars aenv t -> OpenAcc aenv lab alab args t
avars = snd . avars'
  where
    avars' :: A.ArrayVars aenv t -> (ArraysR t, OpenAcc aenv lab alab args t)
    avars' TupRunit = (TupRunit, Anil)
    avars' (TupRsingle var@(A.Var ty@(ArrayR _ _) _)) = (TupRsingle ty, Avar var)
    avars' (TupRpair vars1 vars2) =
        let (t1, e1) = avars' vars1
            (t2, e2) = avars' vars2
        in (TupRpair t1 t2, Apair (TupRpair t1 t2) e1 e2)
