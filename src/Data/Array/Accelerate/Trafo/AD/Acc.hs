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

-- Expression-level function
data OpenFun env lab t where
    Body :: OpenExp env lab () t -> OpenFun env lab t
    Lam :: A.ELeftHandSide a env env' -> OpenFun env' lab t -> OpenFun env lab (a -> t)

-- TODO: Check how many reified types can be removed in this AST
data OpenAcc aenv lab args t where
    Aconst  :: ArrayR (Array sh t)
            -> Array sh t
            -> OpenAcc aenv lab args (Array sh t)

    Apair   :: ArraysR (a, b)
            -> OpenAcc aenv lab args a
            -> OpenAcc aenv lab args b
            -> OpenAcc aenv lab args (a, b)

    Anil    :: OpenAcc aenv lab args ()

    Acond   :: ArraysR a
            -> Exp lab () A.PrimBool
            -> OpenAcc aenv lab args a
            -> OpenAcc aenv lab args a
            -> OpenAcc aenv lab args a

    Map     :: ArrayR (Array sh t2)
            -> OpenFun () lab (t1 -> t2)
            -> OpenAcc aenv lab args (Array sh t1)
            -> OpenAcc aenv lab args (Array sh t2)

    ZipWith :: ArrayR (Array sh t3)
            -> OpenFun () lab (t1 -> t2 -> t3)
            -> OpenAcc aenv lab args (Array sh t1)
            -> OpenAcc aenv lab args (Array sh t2)
            -> OpenAcc aenv lab args (Array sh t3)

    Fold    :: ArrayR (Array sh e)
            -> OpenFun () lab (e -> e -> e)
            -> Maybe (Exp lab () e)
            -> OpenAcc aenv lab args (Array (sh, Int) e)
            -> OpenAcc aenv lab args (Array sh e)

    -- Use this VERY sparingly. It has no equivalent in the real AST, so must
    -- be laboriously back-converted using Let-bindings.
    Aget    :: ArraysR s
            -> TupleIdx t s
            -> OpenAcc env lab args t
            -> OpenAcc env lab args s

    Alet    :: A.ALeftHandSide bnd_t env env'
            -> OpenAcc env lab args bnd_t
            -> OpenAcc env' lab args a
            -> OpenAcc env lab args a

    Avar    :: A.ArrayVar env t
            -> OpenAcc env lab args t

    Aarg    :: ArrayR t
            -> Idx args t
            -> OpenAcc env lab args t

    Alabel  :: ADLabelT lab t
            -> OpenAcc env lab args t

type Acc = OpenAcc ()

-- Closed array program with an unknown type
data AnyAcc lab args = forall t. AnyAcc (Acc lab args t)
deriving instance Show lab => Show (AnyAcc lab args)

data AnyArraysR = forall t. AnyArraysR (ArraysR t)
deriving instance Show AnyArraysR

data AnyArrayR = forall t. AnyArrayR (ArrayR t)
deriving instance Show AnyArrayR

-- Instances
-- ---------

showsAcc :: (lab -> String) -> Int -> [String] -> Int -> OpenAcc env lab args t -> ShowS
showsAcc _ _ _ _ (Aconst ty x) =
    showString (showArray (showString . showTupR' showScalar (arrayRtype ty)) ty x)
showsAcc labf seed env _ (Apair _ e1 e2) =
    showString "(" . showsAcc labf seed env 0 e1 . showString ", " .
        showsAcc labf seed env 0 e2 . showString ")"
showsAcc _ _ _ _ Anil =
    showString "()"
showsAcc labf seed env d (Acond _ c t e) =
    showParen (d > 10) $
        showString "acond " .
            showsExp labf seed [] 11 c . showString " " .
            showsAcc labf seed env 11 t . showString " " .
            showsAcc labf seed env 11 e
showsAcc labf seed env d (Map _ f e) =
    showParen (d > 10) $
        showString "map " .
            showsFun labf seed [] 11 f . showString " " .
            showsAcc labf seed env 11 e
showsAcc labf seed env d (ZipWith _ f e1 e2) =
    showParen (d > 10) $
        showString "zipWith " .
            showsFun labf seed [] 11 f . showString " " .
            showsAcc labf seed env 11 e1 . showString " " .
            showsAcc labf seed env 11 e2
showsAcc labf seed env d (Fold _ f me0 e) =
    showParen (d > 10) $
        showString (maybe "fold " (const "fold1 ") me0) .
            showsFun labf seed [] 11 f . showString " " .
            maybe id (\e0 -> showsExp labf seed [] 11 e0 . showString " ") me0 .
            showsAcc labf seed env 11 e
showsAcc labf seed env d (Aget _ ti e) = showParen (d > 10) $
    showString (tiPrefix ti) . showsAcc labf seed env 10 e
  where
    tiPrefix :: TupleIdx t t' -> String
    tiPrefix = (++ " ") . intercalate "." . reverse . tiPrefix'

    tiPrefix' :: TupleIdx t t' -> [String]
    tiPrefix' TIHere = []
    tiPrefix' (TILeft ti') = "afst" : tiPrefix' ti'
    tiPrefix' (TIRight ti') = "asnd" : tiPrefix' ti'
showsAcc labf seed env d (Alet lhs rhs body) = showParen (d > 0) $
    let (descr, descrs, seed') = namifyLHS seed lhs
        env' = descrs ++ env
    in showString ("let " ++ descr ++ " = ") . showsAcc labf seed' env 0 rhs .
            showString " in " . showsAcc labf seed' env' 0 body
showsAcc _ _ _ d (Aarg ty idx) = showParen (d > 0) $
    showString ('A' : show (idxToInt idx) ++ " :: " ++ show ty)
showsAcc _ _ env _ (Avar (A.Var _ idx)) =
    case drop (idxToInt idx) env of
        descr : _ -> showString descr
        [] -> error $ "Var out of env range in showsAcc: " ++
                      show (idxToInt idx) ++ " in " ++ show env
showsAcc labf _ _ d (Alabel lab) = showParen (d > 0) $
    showString ('L' : labf (labelLabel lab) ++ " :: " ++ show (labelType lab))

showsFun :: (lab -> String) -> Int -> [String] -> Int -> OpenFun env lab t -> ShowS
showsFun labf seed env d (Body expr) = showsExp labf seed env d expr
showsFun labf seed env d (Lam lhs fun) =
    let (descr, descrs, seed') = namifyLHS seed lhs
        env' = descrs ++ env
    in showParen (d > 0) $
        showString "\\" . showString descr .
        showString " -> " . showsFun labf seed' env' 0 fun

instance Show lab => Show (OpenAcc aenv lab args t) where
    showsPrec = showsAcc show 0 []

instance Show lab => GShow (OpenAcc aenv lab args) where
    gshowsPrec = showsPrec

-- Auxiliary functions
-- -------------------

atypeOf :: OpenAcc aenv lab args t -> ArraysR t
atypeOf (Aconst ty _) = TupRsingle ty
atypeOf (Apair ty _ _) = ty
atypeOf Anil = TupRunit
atypeOf (Acond ty _ _ _) = ty
atypeOf (Map ty _ _) = TupRsingle ty
atypeOf (ZipWith ty _ _ _) = TupRsingle ty
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

avars :: A.ArrayVars aenv t -> OpenAcc aenv lab args t
avars = snd . avars'
  where
    avars' :: A.ArrayVars aenv t -> (ArraysR t, OpenAcc aenv lab args t)
    avars' TupRunit = (TupRunit, Anil)
    avars' (TupRsingle var@(A.Var ty _)) = (TupRsingle ty, Avar var)
    avars' (TupRpair vars1 vars2) =
        let (t1, e1) = avars' vars1
            (t2, e2) = avars' vars2
        in (TupRpair t1 t2, Apair (TupRpair t1 t2) e1 e2)
