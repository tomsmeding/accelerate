{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module Data.Array.Accelerate.Trafo.UnDelayed (
  unDelayed, unDelayedAfun
) where

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Trafo.Delayed


-- | Convert from a delayed Acc representation back to the pre-fusion, internal
-- Acc representation. This forgets information about whether nodes are
-- manifest or not.
unDelayed :: DelayedOpenAcc aenv a -> OpenAcc aenv a
unDelayed (Manifest acc) = OpenAcc (unDelayed `through` acc)
unDelayed (Delayed repr shexp fun _) = unDelayed (Manifest (Generate repr shexp fun))

unDelayedAfun :: DelayedOpenAfun aenv a -> OpenAfun aenv a
unDelayedAfun (Alam lhs fun) = Alam lhs (unDelayedAfun fun)
unDelayedAfun (Abody a) = Abody (unDelayed a)

through :: (forall aenv' t. f aenv' t -> g aenv' t)
        -> PreOpenAcc f aenv a
        -> PreOpenAcc g aenv a
through f = \case
  Alet lhs rhs body -> Alet lhs (f rhs) (f body)
  Avar var -> Avar var
  Apair a1 a2 -> Apair (f a1) (f a2)
  Anil -> Anil
  Apply ty fun a -> Apply ty (f `throughAF` fun) (f a)
  Aforeign ty asm fun a -> Aforeign ty asm (f `throughAF` fun) (f a)
  Acond e a1 a2 -> Acond e (f a1) (f a2)
  Awhile fun1 fun2 a -> Awhile (f `throughAF` fun1) (f `throughAF` fun2) (f a)
  Atrace msg a1 a2 -> Atrace msg (f a1) (f a2)
  Use ty arr -> Use ty arr
  Unit ety e -> Unit ety e
  Reshape sht e a -> Reshape sht e (f a)
  Generate ty e efun -> Generate ty e efun
  Transform ty e efun1 efun2 a -> Transform ty e efun1 efun2 (f a)
  Replicate slix e a -> Replicate slix e (f a)
  Slice slix a e -> Slice slix (f a) e
  Map ty fun a -> Map ty fun (f a)
  ZipWith ty fun a1 a2 -> ZipWith ty fun (f a1) (f a2)
  Fold efun me a -> Fold efun me (f a)
  FoldSeg ety efun me a1 a2 -> FoldSeg ety efun me (f a1) (f a2)
  Scan dir efun me a -> Scan dir efun me (f a)
  Scan' dir efun e a -> Scan' dir efun e (f a)
  Permute efun1 a1 efun2 a2 -> Permute efun1 (f a1) efun2 (f a2)
  Backpermute sht e efun a -> Backpermute sht e efun (f a)
  Stencil stty ety efun bnd a -> Stencil stty ety efun bnd (f a)
  Stencil2 stty1 stty2 ety efun bnd1 a1 bnd2 a2 ->
    Stencil2 stty1 stty2 ety efun bnd1 (f a1) bnd2 (f a2)
  Avjp t t' fun a b -> Avjp t t' (f `throughAF` fun) (f a) (f b)
  AcustomDeriv ty fun fun2 a -> AcustomDeriv ty (f `throughAF` fun) (f `throughAF` fun2) (f a)

throughAF :: (forall aenv' t. f aenv' t -> g aenv' t)
          -> PreOpenAfun f aenv a
          -> PreOpenAfun g aenv a
throughAF f = \case
  Abody a -> Abody (f a)
  Alam lhs fun -> Alam lhs (f `throughAF` fun)
