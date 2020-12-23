{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Accelerate.Trafo.AD.Acc (
    module Data.Array.Accelerate.Trafo.AD.Acc,
    Idx(..), idxToInt
) where

import Data.Functor.Identity
import Data.GADT.Show

import Data.Array.Accelerate.Representation.Array hiding ((!!))
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Slice
import Data.Array.Accelerate.Representation.Type
import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.Orphans ()


-- Array programs
-- --------------

-- An expression lambda is either a split AD'd function (ELSplit), which
-- contains the split-lambda information as well as the label at which the
-- expression temporaries are stored; or a plain expression function (ELPlain).
data ExpLambda1 aenv lab alab tenv sh t1 t2
  = forall tmp idxadj. ELSplit (SplitLambdaAD t1 t2 lab alab tenv tmp idxadj) (ADLabelNS alab (Array sh tmp))
  |                    ELPlain (Fun aenv lab alab tenv (t1 -> t2))

fmapPlain :: (Fun aenv lab alab tenv (t1 -> t2) -> Fun aenv' lab alab tenv (t1 -> t2))
          -> ExpLambda1 aenv lab alab tenv sh t1 t2
          -> ExpLambda1 aenv' lab alab tenv sh t1 t2
fmapPlain f e = runIdentity (traversePlain (Identity . f) e)

traversePlain :: Applicative f
              => (Fun aenv lab alab tenv (t1 -> t2) -> f (Fun aenv' lab alab tenv (t1 -> t2)))
              -> ExpLambda1 aenv lab alab tenv sh t1 t2
              -> f (ExpLambda1 aenv' lab alab tenv sh t1 t2)
traversePlain _ (ELSplit lam lab) = pure (ELSplit lam lab)
traversePlain f (ELPlain fun) = ELPlain <$> f fun

data OpenAcc aenv lab alab args t where
    Aconst  :: ADLabelNS alab (Array sh t)
            -> Array sh t
            -> OpenAcc aenv lab alab args (Array sh t)

    Apair   :: ADLabelN alab (a, b)
            -> OpenAcc aenv lab alab args a
            -> OpenAcc aenv lab alab args b
            -> OpenAcc aenv lab alab args (a, b)

    Anil    :: ADLabelN alab ()
            -> OpenAcc aenv lab alab args ()

    Acond   :: ADLabelN alab a
            -> Exp aenv lab alab () () A.PrimBool
            -> OpenAcc aenv lab alab args a
            -> OpenAcc aenv lab alab args a
            -> OpenAcc aenv lab alab args a

    Map     :: ADLabelNS alab (Array sh t2)
            -> ExpLambda1 aenv lab alab () sh t1 t2
            -> OpenAcc aenv lab alab args (Array sh t1)
            -> OpenAcc aenv lab alab args (Array sh t2)

    ZipWith :: ADLabelNS alab (Array sh t3)
            -> ExpLambda1 aenv lab alab () sh (t1, t2) t3
            -> OpenAcc aenv lab alab args (Array sh t1)
            -> OpenAcc aenv lab alab args (Array sh t2)
            -> OpenAcc aenv lab alab args (Array sh t3)

    Fold    :: ADLabelNS alab (Array sh e)
            -> Fun aenv lab alab () ((e, e) -> e)
            -> Maybe (Exp aenv lab alab () () e)
            -> OpenAcc aenv lab alab args (Array (sh, Int) e)
            -> OpenAcc aenv lab alab args (Array sh e)

    Sum     :: ADLabelNS alab (Array sh e)
            -> OpenAcc aenv lab alab args (Array (sh, Int) e)
            -> OpenAcc aenv lab alab args (Array sh e)

    Scan    :: ADLabelNS alab (Array (sh, Int) e)
            -> A.Direction
            -> Fun aenv lab alab () ((e, e) -> e)
            -> Maybe (Exp aenv lab alab () () e)
            -> OpenAcc aenv lab alab args (Array (sh, Int) e)
            -> OpenAcc aenv lab alab args (Array (sh, Int) e)

    Scan'   :: ADLabelN alab (Array (sh, Int) e, Array sh e)
            -> A.Direction
            -> Fun aenv lab alab () ((e, e) -> e)
            -> Exp aenv lab alab () () e
            -> OpenAcc aenv lab alab args (Array (sh, Int) e)
            -> OpenAcc aenv lab alab args (Array (sh, Int) e, Array sh e)

    Generate :: ADLabelNS alab (Array sh e)
             -> Exp aenv lab alab () () sh
             -> ExpLambda1 aenv lab alab () sh sh e
             -> OpenAcc aenv lab alab args (Array sh e)

    Replicate :: ADLabelNS alab (Array sh e)
              -> SliceIndex slix sl co sh
              -> Exp aenv lab alab () () slix
              -> OpenAcc aenv lab alab args (Array sl e)
              -> OpenAcc aenv lab alab args (Array sh e)

    Slice   :: ADLabelNS alab (Array sl e)
            -> SliceIndex slix sl co sh
            -> OpenAcc aenv lab alab args (Array sh e)
            -> Exp aenv lab alab () () slix
            -> OpenAcc aenv lab alab args (Array sl e)

    -- Has no equivalent in the real AST. Is converted using backpermute, reshape, fold.
    -- Folds the RSpecReduce-dimensions away using the binary operation.
    -- Like 'add' is the dual of 'dup', Reduce is the dual of Replicate.
    Reduce  :: ADLabelNS alab (Array redsh e)
            -> ReduceSpec slix redsh fullsh
            -> Fun aenv lab alab () (e -> e -> e)
            -> OpenAcc aenv lab alab args (Array fullsh e)
            -> OpenAcc aenv lab alab args (Array redsh e)

    Reshape :: ADLabelNS alab (Array sh e)
            -> Exp aenv lab alab () () sh
            -> OpenAcc aenv lab alab args (Array sh' e)
            -> OpenAcc aenv lab alab args (Array sh e)

    Backpermute :: ADLabelNS alab (Array sh' e)
                -> Exp aenv lab alab () () sh'              -- dimensions of the result
                -> Fun aenv lab alab () (sh' -> sh)         -- permutation function
                -> OpenAcc aenv lab alab args (Array sh e)  -- source array
                -> OpenAcc aenv lab alab args (Array sh' e)

    -- The combination function is not stored as an ExpLambda1, because we
    -- don't currently support taking the derivative of a Permute: we only
    -- generate it as the derivative of a Backpermute and of array indexing.
    Permute :: ADLabelNS alab (Array sh' e)
            -> Fun aenv lab alab () (e -> e -> e)            -- combination function
            -> OpenAcc aenv lab alab args (Array sh' e)      -- default values
            -> Fun aenv lab alab () (sh -> A.PrimMaybe sh')  -- permutation function
            -> OpenAcc aenv lab alab args (Array sh e)       -- source array
            -> OpenAcc aenv lab alab args (Array sh' e)

    -- Use this VERY sparingly. It has no equivalent in the real AST, so must
    -- be laboriously back-converted using Let-bindings.
    Aget    :: ADLabelN alab s
            -> TupleIdx t s
            -> OpenAcc env lab alab args t
            -> OpenAcc env lab alab args s

    Alet    :: A.ALeftHandSide bnd_t env env'
            -> OpenAcc env lab alab args bnd_t
            -> OpenAcc env' lab alab args a
            -> OpenAcc env lab alab args a

    Avar    :: ADLabelNS alab (Array sh e)  -- own label
            -> A.ArrayVar env (Array sh e)  -- pointer to binding
            -> APartLabelN alab rhs_t (Array sh e)  -- label of, and index into, referred-to right-hand side
            -> OpenAcc env lab alab args (Array sh e)

    Aarg    :: ADLabelNS alab (Array sh e)
            -> ArraysR args
            -> TupleIdx args (Array sh e)
            -> OpenAcc env lab alab args (Array sh e)

type Acc = OpenAcc ()

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
showsAcc se _ (Aconst lab@DLabel { labelType = ty } x) =
    showString (showArray (showString . showTupR' showScalar (arrayRtype ty)) ty x)
        . ashowLabelSuffix se lab
showsAcc se _ (Apair lab e1 e2) =
    showString "(" . showsAcc se 0 e1 . showString ", " .
        showsAcc se 0 e2 . showString ")" .
        ashowLabelSuffix se lab
showsAcc se _ (Anil lab) =
    showString "()" . ashowLabelSuffix se lab
showsAcc se d (Acond lab c t e) =
    showParen (d > 10) $
        showString "acond" . ashowLabelSuffix se lab . showString " " .
            showsExp (se { seEnv = [] }) 11 c . showString " " .
            showsAcc se 11 t . showString " " .
            showsAcc se 11 e
showsAcc se d (Map lab f e) =
    showParen (d > 10) $
        showString "map" . ashowLabelSuffix se lab . showString " " .
            showsLambda (se { seEnv = [] }) 11 f . showString " " .
            showsAcc se 11 e
showsAcc se d (ZipWith lab f e1 e2) =
    showParen (d > 10) $
        showString "zipWith" . ashowLabelSuffix se lab . showString " " .
            showsLambda (se { seEnv = [] }) 11 f . showString " " .
            showsAcc se 11 e1 . showString " " .
            showsAcc se 11 e2
showsAcc se d (Fold lab f me0 e) =
    showParen (d > 10) $
        showString (maybe "fold1" (const "fold") me0) .
            ashowLabelSuffix se lab . showString " " .
            showsFun (se { seEnv = [] }) 11 f . showString " " .
            maybe id (\e0 -> showsExp (se { seEnv = [] }) 11 e0 . showString " ") me0 .
            showsAcc se 11 e
showsAcc se d (Scan lab dir f me0 e) =
    showParen (d > 10) $
        showString ("scan" ++ (case dir of A.LeftToRight -> "l" ; A.RightToLeft -> "r") ++ maybe "1" (const "") me0) .
            ashowLabelSuffix se lab . showString " " .
            showsFun (se { seEnv = [] }) 11 f . showString " " .
            maybe id (\e0 -> showsExp (se { seEnv = [] }) 11 e0 . showString " ") me0 .
            showsAcc se 11 e
showsAcc se d (Scan' lab dir f e0 e) =
    showParen (d > 10) $
        showString ("scan" ++ (case dir of A.LeftToRight -> "l" ; A.RightToLeft -> "r") ++ "'") .
            ashowLabelSuffix se lab . showString " " .
            showsFun (se { seEnv = [] }) 11 f . showString " " .
            showsExp (se { seEnv = [] }) 11 e0 . showString " " .
            showsAcc se 11 e
showsAcc se d (Backpermute lab dim f e) =
    showParen (d > 10) $
        showString "backpermute" . ashowLabelSuffix se lab . showString " " .
            showsExp (se { seEnv = [] }) 11 dim . showString " " .
            showsFun (se { seEnv = [] }) 11 f . showString " " .
            showsAcc se 11 e
showsAcc se d (Permute lab f1 e1 f2 e2) =
    showParen (d > 10) $
        showString "permute" . ashowLabelSuffix se lab . showString " " .
            showsFun (se { seEnv = [] }) 11 f1 . showString " " .
            showsAcc se 11 e1 . showString " " .
            showsFun (se { seEnv = [] }) 11 f2 . showString " " .
            showsAcc se 11 e2
showsAcc se d (Sum lab e) =
    showParen (d > 10) $
        showString "sum" . ashowLabelSuffix se lab . showString " " .
            showsAcc se 11 e
showsAcc se d (Generate lab sh f) =
    showParen (d > 10) $
        showString "generate" . ashowLabelSuffix se lab . showString " " .
            showsExp (se { seEnv = [] }) 11 sh . showString " " .
            showsLambda (se { seEnv = [] }) 11 f
showsAcc se d (Replicate lab _ e a) =
    showParen (d > 10) $
        showString "replicate" . ashowLabelSuffix se lab . showString " " .
            showsExp (se { seEnv = [] }) 11 e . showString " " .
            showsAcc se 11 a
showsAcc se d (Slice lab _ a e) =
    showParen (d > 10) $
        showString "slice" . ashowLabelSuffix se lab . showString " " .
            showsAcc se 11 a . showString " " .
            showsExp (se { seEnv = [] }) 11 e
showsAcc se d (Reduce lab _ f a) =
    showParen (d > 10) $
        showString "reduce" . ashowLabelSuffix se lab . showString " " .
            showsFun (se { seEnv = [] }) 11 f . showString " " .
            showsAcc se 11 a
showsAcc se d (Reshape lab e a) =
    showParen (d > 10) $
        showString "reshape" . ashowLabelSuffix se lab . showString " " .
            showsExp (se { seEnv = [] }) 11 e . showString " " .
            showsAcc se 11 a
showsAcc se d (Aget lab ti e) = showParen (d > 10) $
    showString (tiPrefixAcc ti) . ashowLabelSuffix se lab . showString " " .
    showsAcc se 10 e
showsAcc se d (Alet lhs rhs body) = showParen (d > 0) $
    let (descr, descrs, seed') = namifyLHS (seSeed se) lhs
        env' = descrs ++ seAenv se
    in showString ("let " ++ descr ++ " = ") . showsAcc (se { seSeed = seed' }) 0 rhs .
            showString " in " . showsAcc (se { seSeed = seed', seAenv = env' }) 0 body
showsAcc se _ (Avar lab (A.Var _ idx) (PartLabel referLab referPart)) =
    let varstr
          | descr : _ <- drop (idxToInt idx) (seAenv se) = descr
          | otherwise = "tA_UP" ++ show (1 + idxToInt idx - length (seAenv se))
    in case ashowLabelSuffix se referLab "" of
         "" -> showString varstr
         referLabStr ->
             showString ("(" ++ varstr ++ "->" ++ tiPrefixAcc referPart ++ " " ++ referLabStr ++ ")") .
             ashowLabelSuffix se lab
showsAcc se d (Aarg lab _ tidx) = showParen (d > 0) $
    showString (case tiPrefixAcc tidx of "" -> "A" ; pr -> "(" ++ pr ++ " A)")
    . ashowLabelSuffix se lab . showString (" :: " ++ show (labelType lab))

tiPrefixAcc :: TupleIdx t t' -> String
tiPrefixAcc = tiPrefix "afst" "asnd"

showsLambda :: EShowEnv lab alab -> Int -> ExpLambda1 aenv lab alab tenv sh t1 t2 -> ShowS
showsLambda se d (ELPlain fun) = showsFun se d fun
showsLambda _ _ ELSplit{} = showString "{splitlambda}"

ashowLabelSuffix :: AShowEnv lab alab -> DLabel lty s alab t -> ShowS
ashowLabelSuffix se lab =
    showString $ case seAlabf se (labelLabel lab) of
                   "" -> ""
                   "()" -> ""
                   res -> "[" ++ res ++ "]"

instance (Show lab, Show alab) => Show (OpenAcc aenv lab alab args t) where
    showsPrec = showsAcc (ShowEnv show show 0 () [])

instance (Show lab, Show alab) => GShow (OpenAcc aenv lab alab args) where
    gshowsPrec = showsPrec

-- Auxiliary functions
-- -------------------

alabelOf :: OpenAcc aenv lab alab args t -> ADLabelN alab t
alabelOf (Aconst lab _) = tupleLabel lab
alabelOf (Apair lab _ _) = lab
alabelOf (Anil lab) = lab
alabelOf (Acond lab _ _ _) = lab
alabelOf (Map lab _ _) = tupleLabel lab
alabelOf (ZipWith lab _ _ _) = tupleLabel lab
alabelOf (Generate lab _ _) = tupleLabel lab
alabelOf (Fold lab _ _ _) = tupleLabel lab
alabelOf (Scan lab _ _ _ _) = tupleLabel lab
alabelOf (Scan' lab _ _ _ _) = lab
alabelOf (Backpermute lab _ _ _) = tupleLabel lab
alabelOf (Permute lab _ _ _ _) = tupleLabel lab
alabelOf (Replicate lab _ _ _) = tupleLabel lab
alabelOf (Slice lab _ _ _) = tupleLabel lab
alabelOf (Reduce lab _ _ _) = tupleLabel lab
alabelOf (Reshape lab _ _) = tupleLabel lab
alabelOf (Sum lab _) = tupleLabel lab
alabelOf (Aget lab _ _) = lab
alabelOf (Alet _ _ body) = alabelOf body
alabelOf (Avar lab _ _) = tupleLabel lab
alabelOf (Aarg lab _ _) = tupleLabel lab

atypeOf :: OpenAcc aenv lab alab args t -> ArraysR t
atypeOf = labelType . alabelOf

alabelOf1 :: OpenAcc aenv lab alab args (Array sh t) -> ADLabelNS alab (Array sh t)
alabelOf1 a | DLabel (TupRsingle ty@ArrayR{}) lab <- alabelOf a = DLabel ty lab
            | otherwise = error "invalid GADTs"

atypeOf1 :: OpenAcc aenv lab alab args (Array sh t) -> ArrayR (Array sh t)
atypeOf1 a | TupRsingle ty <- atypeOf a = ty
           | otherwise = error "invalid GADTs"

avars :: A.ArrayVars aenv t -> OpenAcc aenv lab () args t
avars = snd . avars'
  where
    avars' :: A.ArrayVars aenv t -> (ArraysR t, OpenAcc aenv lab () args t)
    avars' TupRunit = (TupRunit, Anil (nilLabel TupRunit))
    avars' (TupRsingle var@(A.Var ty@ArrayR{} _)) =
        (TupRsingle ty, Avar (nilLabel ty) var (PartLabel (nilLabel (TupRsingle ty)) TIHere))
    avars' (TupRpair vars1 vars2) =
        let (t1, e1) = avars' vars1
            (t2, e2) = avars' vars2
        in (TupRpair t1 t2, Apair (nilLabel (TupRpair t1 t2)) e1 e2)

untupleAccs :: TupR (OpenAcc aenv () () args) t -> OpenAcc aenv () () args t
untupleAccs TupRunit = Anil (nilLabel TupRunit)
untupleAccs (TupRsingle e) = e
untupleAccs (TupRpair t1 t2) = smartApair (untupleAccs t1) (untupleAccs t2)

smartAvar :: A.ArrayVar aenv (Array sh t) -> OpenAcc aenv lab () args (Array sh t)
smartAvar var@(A.Var ty _) = Avar (nilLabel ty) var (PartLabel (nilLabel (TupRsingle ty)) TIHere)

smartApair :: OpenAcc aenv lab () args a -> OpenAcc aenv lab () args b -> OpenAcc aenv lab () args (a, b)
smartApair a b = Apair (nilLabel (TupRpair (atypeOf a) (atypeOf b))) a b

-- TODO: make smartFstA and smartSndA non-quadratic
smartFstA :: OpenAcc aenv lab () args (t1, t2) -> OpenAcc aenv lab () args t1
smartFstA (Apair _ ex _) = ex
smartFstA (Aget (labelType -> TupRpair t1 _) tidx ex) = Aget (nilLabel t1) (insertFst tidx) ex
smartFstA ex
  | TupRpair t1 _ <- atypeOf ex
  = Aget (nilLabel t1) (TILeft TIHere) ex
smartFstA _ = error "smartFstA: impossible GADTs"

smartSndA :: OpenAcc aenv lab () args (t1, t2) -> OpenAcc aenv lab () args t2
smartSndA (Apair _ _ ex) = ex
smartSndA (Aget (labelType -> TupRpair _ t2) tidx ex) = Aget (nilLabel t2) (insertSnd tidx) ex
smartSndA ex
  | TupRpair _ t2 <- atypeOf ex
  = Aget (nilLabel t2) (TIRight TIHere) ex
smartSndA _ = error "smartSndA: impossible GADTs"
