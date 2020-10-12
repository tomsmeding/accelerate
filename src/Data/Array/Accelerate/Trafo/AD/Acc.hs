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
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Slice
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

    Sum     :: ArrayR (Array sh e)
            -> OpenAcc aenv lab alab args (Array (sh, Int) e)
            -> OpenAcc aenv lab alab args (Array sh e)

    Generate :: ArrayR (Array sh e)
             -> Exp aenv lab alab () sh
             -> ExpLambda1 aenv lab alab sh sh e
             -> OpenAcc aenv lab alab args (Array sh e)

    Replicate :: ArrayR (Array sh e)
              -> SliceIndex slix sl co sh
              -> Exp aenv lab alab () slix
              -> OpenAcc aenv lab alab args (Array sl e)
              -> OpenAcc aenv lab alab args (Array sh e)

    Slice   :: ArrayR (Array sl e)
            -> SliceIndex slix sl co sh
            -> OpenAcc aenv lab alab args (Array sh e)
            -> Exp aenv lab alab () slix
            -> OpenAcc aenv lab alab args (Array sl e)

    -- Has no equivalent in the real AST. Is converted using backpermute, reshape, fold.
    -- Folds the RSpecReduce-dimensions away using the binary operation.
    -- Like 'add' is the dual of 'dup', Reduce is the dual of Replicate.
    Reduce  :: ArrayR (Array redsh e)
            -> ReduceSpec slix redsh fullsh
            -> Fun aenv lab alab (e -> e -> e)
            -> OpenAcc aenv lab alab args (Array fullsh e)
            -> OpenAcc aenv lab alab args (Array redsh e)

    Reshape :: ArrayR (Array sh e)
            -> Exp aenv lab alab () sh
            -> OpenAcc aenv lab alab args (Array sh' e)
            -> OpenAcc aenv lab alab args (Array sh e)

    Backpermute :: ArrayR (Array sh' e)
                -> Exp aenv lab alab () sh'                 -- dimensions of the result
                -> Fun aenv lab alab (sh' -> sh)            -- permutation function
                -> OpenAcc aenv lab alab args (Array sh e)  -- source array
                -> OpenAcc aenv lab alab args (Array sh' e)

    -- The combination function is not stored as an ExpLambda1, because we
    -- don't currently support taking the derivative of a Permute: we only
    -- generate it as the derivative of a Backpermute.
    Permute :: ArrayR (Array sh' e)
            -> Fun aenv lab alab (e -> e -> e)            -- combination function
            -> OpenAcc aenv lab alab args (Array sh' e)   -- default values
            -> Fun aenv lab alab (sh -> A.PrimMaybe sh')  -- permutation function
            -> OpenAcc aenv lab alab args (Array sh e)    -- source array
            -> OpenAcc aenv lab alab args (Array sh' e)

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

type Acc = OpenAcc ()

-- Closed array program with an unknown type
data AnyAcc lab alab args = forall t. AnyAcc (Acc lab alab args t)
deriving instance (Show lab, Show alab) => Show (AnyAcc lab alab args)

data AnyArraysR = forall t. AnyArraysR (ArraysR t)
deriving instance Show AnyArraysR

data AnyArrayR = forall t. AnyArrayR (ArrayR t)
deriving instance Show AnyArrayR

-- Specification for which dimensions to reduce in a Reduce aggregate operation.
-- spec: Equal to the dual SliceIndex, suitable for Replicate. Dual as in:
--       Replicate on a SliceIndex with its first 'slix' type argument set to
--       'spec' will create (expand) precisely those dimensions that a Reduce
--       with this spec will fold away.
-- red: The reduced shape type.
-- full: The pre-reduce, full shape type.
data ReduceSpec spec red full where
    RSpecNil    :: ReduceSpec () () ()
    RSpecReduce :: ReduceSpec spec red full -> ReduceSpec (spec, Int) red (full, Int)
    RSpecKeep   :: ReduceSpec spec red full -> ReduceSpec (spec, ()) (red, Int) (full, Int)

deriving instance Show (ReduceSpec spec red full)

rsReducedShapeR :: ReduceSpec spec red full -> ShapeR red
rsReducedShapeR RSpecNil = ShapeRz
rsReducedShapeR (RSpecReduce spec) = rsReducedShapeR spec
rsReducedShapeR (RSpecKeep spec) = ShapeRsnoc (rsReducedShapeR spec)

rsFullShapeR :: ReduceSpec spec red full -> ShapeR full
rsFullShapeR RSpecNil = ShapeRz
rsFullShapeR (RSpecReduce spec) = ShapeRsnoc (rsFullShapeR spec)
rsFullShapeR (RSpecKeep spec) = ShapeRsnoc (rsFullShapeR spec)

-- Instances
-- ---------

showsAcc :: AShowEnv lab alab -> Int -> OpenAcc env lab alab args t -> ShowS
showsAcc _ _ (Aconst ty x) =
    showString (showArray (showString . showTupR' showScalar (arrayRtype ty)) ty x)
showsAcc se _ (Apair _ e1 e2) =
    showString "(" . showsAcc se 0 e1 . showString ", " .
        showsAcc se 0 e2 . showString ")"
showsAcc _ _ Anil =
    showString "()"
showsAcc se d (Acond _ c t e) =
    showParen (d > 10) $
        showString "acond " .
            showsExp (se { seEnv = [] }) 11 c . showString " " .
            showsAcc se 11 t . showString " " .
            showsAcc se 11 e
showsAcc se d (Map _ f e) =
    showParen (d > 10) $
        showString "map " .
            showsLambda (se { seEnv = [] }) 11 f . showString " " .
            showsAcc se 11 e
showsAcc se d (ZipWith _ f e1 e2) =
    showParen (d > 10) $
        showString "zipWith " .
            showsLambda (se { seEnv = [] }) 11 f . showString " " .
            showsAcc se 11 e1 . showString " " .
            showsAcc se 11 e2
showsAcc se d (Fold _ f me0 e) =
    showParen (d > 10) $
        showString (maybe "fold1 " (const "fold ") me0) .
            showsLambda (se { seEnv = [] }) 11 f . showString " " .
            maybe id (\e0 -> showsExp (se { seEnv = [] }) 11 e0 . showString " ") me0 .
            showsAcc se 11 e
showsAcc se d (Backpermute _ dim f e) =
    showParen (d > 10) $
        showString "backpermute " .
            showsExp (se { seEnv = [] }) 11 dim . showString " " .
            showsFun (se { seEnv = [] }) 11 f . showString " " .
            showsAcc se 11 e
showsAcc se d (Permute _ f1 e1 f2 e2) =
    showParen (d > 10) $
        showString "permute " .
            showsFun (se { seEnv = [] }) 11 f1 . showString " " .
            showsAcc se 11 e1 . showString " " .
            showsFun (se { seEnv = [] }) 11 f2 . showString " " .
            showsAcc se 11 e2
showsAcc se d (Sum _ e) =
    showParen (d > 10) $
        showString "sum " .
            showsAcc se 11 e
showsAcc se d (Generate _ sh f) =
    showParen (d > 10) $
        showString "generate " .
            showsExp (se { seEnv = [] }) 11 sh . showString " " .
            showsLambda (se { seEnv = [] }) 11 f
showsAcc se d (Replicate _ _ e a) =
    showParen (d > 10) $
        showString "replicate " .
            showsExp (se { seEnv = [] }) 11 e . showString " " .
            showsAcc se 11 a
showsAcc se d (Slice _ _ a e) =
    showParen (d > 10) $
        showString "slice " .
            showsAcc se 11 a . showString " " .
            showsExp (se { seEnv = [] }) 11 e
showsAcc se d (Reduce _ _ f a) =
    showParen (d > 10) $
        showString "reduce " .
            showsFun (se { seEnv = [] }) 11 f . showString " " .
            showsAcc se 11 a
showsAcc se d (Reshape _ e a) =
    showParen (d > 10) $
        showString "reshape " .
            showsExp (se { seEnv = [] }) 11 e . showString " " .
            showsAcc se 11 a
showsAcc se d (Aget _ ti e) = showParen (d > 10) $
    showString (tiPrefix ti) . showsAcc se 10 e
  where
    tiPrefix :: TupleIdx t t' -> String
    tiPrefix = (++ " ") . intercalate "." . reverse . tiPrefix'

    tiPrefix' :: TupleIdx t t' -> [String]
    tiPrefix' TIHere = []
    tiPrefix' (TILeft ti') = "afst" : tiPrefix' ti'
    tiPrefix' (TIRight ti') = "asnd" : tiPrefix' ti'
showsAcc se d (Alet lhs rhs body) = showParen (d > 0) $
    let (descr, descrs, seed') = namifyLHS (seSeed se) lhs
        env' = descrs ++ seAenv se
    in showString ("let " ++ descr ++ " = ") . showsAcc (se { seSeed = seed' }) 0 rhs .
            showString " in " . showsAcc (se { seSeed = seed', seAenv = env' }) 0 body
showsAcc _ d (Aarg ty idx) = showParen (d > 0) $
    showString ('A' : show (idxToInt idx) ++ " :: " ++ show ty)
showsAcc se _ (Avar (A.Var _ idx)) =
    case drop (idxToInt idx) (seAenv se) of
        descr : _ -> showString descr
        [] -> showString ("tA_UP" ++ show (1 + idxToInt idx - length (seAenv se)))
showsAcc se d (Alabel lab) = showParen (d > 0) $
    showString ('L' : seAlabf se (labelLabel lab) ++ " :: " ++ show (labelType lab))

showsLambda :: EShowEnv lab alab -> Int -> ExpLambda1 aenv lab alab sh t1 t2 -> ShowS
showsLambda se d (Right fun) = showsFun se d fun
showsLambda _ _ (Left _) = showString "{splitlambda}"

instance (Show lab, Show alab) => Show (OpenAcc aenv lab alab args t) where
    showsPrec = showsAcc (ShowEnv show show 0 () [])

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
atypeOf (Backpermute ty _ _ _) = TupRsingle ty
atypeOf (Permute ty _ _ _ _) = TupRsingle ty
atypeOf (Replicate ty _ _ _) = TupRsingle ty
atypeOf (Slice ty _ _ _) = TupRsingle ty
atypeOf (Reduce ty _ _ _) = TupRsingle ty
atypeOf (Reshape ty _ _) = TupRsingle ty
atypeOf (Sum ty _) = TupRsingle ty
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
