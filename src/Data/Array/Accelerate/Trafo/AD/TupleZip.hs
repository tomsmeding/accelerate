{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Accelerate.Trafo.AD.TupleZip (
  tupleZipExp, tupleZipExp',
  tupleZipAcc, tupleZipAcc',
) where

import Data.Functor.Identity

import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.AST.Environment ((:>)(..), (.>), weakenWithLHS, weakenId)
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.Acc
import Data.Array.Accelerate.Trafo.AD.Sink (sinkAcc)
import Data.Array.Accelerate.Trafo.Var


type CombinerExp m top topenv lab alab =
  forall s env aenv args tenv.
       ScalarType s
    -> TupleIdx top s
    -> topenv :> env
    -> OpenExp env aenv lab alab args tenv s
    -> OpenExp env aenv lab alab args tenv s
    -> m (OpenExp env aenv lab alab args tenv s)

type CombinerExp' top topenv lab alab =
  forall s env aenv args tenv.
       ScalarType s
    -> TupleIdx top s
    -> topenv :> env
    -> OpenExp env aenv lab alab args tenv s
    -> OpenExp env aenv lab alab args tenv s
    -> OpenExp env aenv lab alab args tenv s

type IgnorerExp lab alab =
  forall s env aenv args tenv.
    ScalarType s -> OpenExp env aenv lab alab args tenv s
                 -> Bool

type CombinerAcc m top topaenv lab alab =
  forall sh t aenv args.
       ArrayR (Array sh t)
    -> TupleIdx top (Array sh t)
    -> topaenv :> aenv
    -> OpenAcc aenv lab alab args (Array sh t)
    -> OpenAcc aenv lab alab args (Array sh t)
    -> m (OpenAcc aenv lab alab args (Array sh t))

type CombinerAcc' top topaenv lab alab =
  forall sh t aenv args.
       ArrayR (Array sh t)
    -> TupleIdx top (Array sh t)
    -> topaenv :> aenv
    -> OpenAcc aenv lab alab args (Array sh t)
    -> OpenAcc aenv lab alab args (Array sh t)
    -> OpenAcc aenv lab alab args (Array sh t)

type IgnorerAcc lab alab =
  forall sh t aenv args.
    ArrayR (Array sh t) -> OpenAcc aenv lab alab args (Array sh t)
                        -> Bool

class ExprLike s f | f -> s where
  nil :: f env ()
  pair :: f env a -> f env b -> f env (a, b)
  var :: A.Var s env t -> f env t
  let_ :: LeftHandSide s t env env' -> f env t -> f env' t' -> f env t'
  fromPair :: f env (a, b) -> Maybe (f env a, f env b)
  sink :: env :> env' -> f env t -> f env' t

-- This type only exists to move the 'env' type variable to the end.
newtype OpenExpEnv aenv lab alab args tenv env t =
  OpenExpEnv { unExpEnv :: OpenExp env aenv lab alab args tenv t }

instance ExprLike ScalarType (OpenExpEnv aenv () alab args tenv) where
  nil = OpenExpEnv (Nil magicLabel)
  pair (OpenExpEnv e1) (OpenExpEnv e2) = OpenExpEnv (smartPair e1 e2)
  var v = OpenExpEnv (smartVar v)
  let_ lhs (OpenExpEnv e1) (OpenExpEnv e2) = OpenExpEnv (Let lhs e1 e2)
  fromPair (OpenExpEnv (Pair _ e1 e2)) = Just (OpenExpEnv e1, OpenExpEnv e2)
  fromPair _ = Nothing
  sink w = OpenExpEnv . sinkExp w . unExpEnv

-- This type only exists to move the 'aenv' type variable to the end.
newtype OpenAccEnv lab alab args aenv t =
  OpenAccEnv { unAccEnv :: OpenAcc aenv lab alab args t }

instance ExprLike ArrayR (OpenAccEnv lab () args) where
  nil = OpenAccEnv (Anil (nilLabel TupRunit))
  pair (OpenAccEnv e1) (OpenAccEnv e2) = OpenAccEnv (Apair (nilLabel (TupRpair (atypeOf e1) (atypeOf e2))) e1 e2)
  var v@(A.Var ty@ArrayR{} _) = OpenAccEnv (Avar (nilLabel ty) v (PartLabel (nilLabel (TupRsingle ty)) TIHere))
  let_ lhs (OpenAccEnv e1) (OpenAccEnv e2) = OpenAccEnv (Alet lhs e1 e2)
  fromPair (OpenAccEnv (Apair _ e1 e2)) = Just (OpenAccEnv e1, OpenAccEnv e2)
  fromPair _ = Nothing
  sink w = OpenAccEnv . sinkAcc w . unAccEnv

type CombinerGen m top topenv s f = forall t env. s t -> TupleIdx top t -> topenv :> env -> f env t -> f env t -> m (f env t)

type IgnorerGen s f = forall t env. s t -> f env t -> Bool

varsZip :: (Applicative m, ExprLike s f)
        => CombinerGen m top topenv s f
        -> TupR s t
        -> TupleIdx top t
        -> topenv :> env
        -> A.Vars s env t
        -> A.Vars s env t
        -> m (f env t)
varsZip _ TupRunit _ _ TupRunit TupRunit =
  pure nil
varsZip combine (TupRsingle ty) tidx w (TupRsingle v1) (TupRsingle v2) =
  combine ty tidx w (var v1) (var v2)
varsZip combine (TupRpair t1 t2) tidx w (TupRpair v11 v12) (TupRpair v21 v22) =
  pair <$> varsZip combine t1 (insertFst tidx) w v11 v21
       <*> varsZip combine t2 (insertSnd tidx) w v12 v22
varsZip _ _ _ _ _ _ = error "inconsistency in varsZip"

tupleZipGen :: (Applicative m, ExprLike s f)
            => TupR s t
            -> TupleIdx top t
            -> topenv :> env
            -> CombinerGen m top topenv s f
            -> IgnorerGen s f
            -> f env t
            -> f env t
            -> m (f env t)
tupleZipGen TupRunit _ _ _ _ _ _ = pure nil
tupleZipGen (TupRsingle ty) tidx w combine ignore e1 e2
  | ignore ty e1 = pure e2
  | ignore ty e2 = pure e1
  | otherwise = combine ty tidx w e1 e2
tupleZipGen (TupRpair t1 t2) tidx w combine ignore (fromPair -> Just (e11, e12)) (fromPair -> Just (e21, e22)) =
  pair <$> tupleZipGen t1 (insertFst tidx) w combine ignore e11 e21
       <*> tupleZipGen t2 (insertSnd tidx) w combine ignore e12 e22
tupleZipGen ty tidx w combine _ignore e1 e2
  | DeclareVars lhs1 _ value1 <- declareVars ty
  , DeclareVars lhs2 _ value2 <- declareVars ty
  = let_ lhs1 e1 . let_ lhs2 (sink (weakenWithLHS lhs1) e2)
      <$> varsZip combine ty tidx (weakenWithLHS lhs2 .> weakenWithLHS lhs1 .> w) (value1 (weakenWithLHS lhs2)) (value2 weakenId)

-- TODO: check whether this is actually used somewhere (and not only tupleZipExp')
tupleZipExp :: Applicative m
            => TypeR t
            -> CombinerExp m t env () alab
            -> IgnorerExp () alab
            -> OpenExp env aenv () alab args tenv t
            -> OpenExp env aenv () alab args tenv t
            -> m (OpenExp env aenv () alab args tenv t)
tupleZipExp ty combine ignore e1 e2 =
  unExpEnv <$> tupleZipGen ty TIHere weakenId
                   (\t tidx w (OpenExpEnv x1) (OpenExpEnv x2) -> OpenExpEnv <$> combine t tidx w x1 x2)
                   (\t (OpenExpEnv x) -> ignore t x)
                   (OpenExpEnv e1)
                   (OpenExpEnv e2)

tupleZipExp' :: TypeR t
             -> CombinerExp' t env () alab
             -> IgnorerExp () alab
             -> OpenExp env aenv () alab args tenv t
             -> OpenExp env aenv () alab args tenv t
             -> OpenExp env aenv () alab args tenv t
tupleZipExp' ty combine' ignore e1 e2 =
  runIdentity $ tupleZipExp ty (\sty tidx w sub1 sub2 -> pure (combine' sty tidx w sub1 sub2)) ignore e1 e2

-- TODO: check whether this is actually used somewhere (and not only tupleZipAcc')
tupleZipAcc :: Applicative m
            => ArraysR t
            -> CombinerAcc m t aenv lab ()
            -> IgnorerAcc lab ()
            -> OpenAcc aenv lab () args t
            -> OpenAcc aenv lab () args t
            -> m (OpenAcc aenv lab () args t)
tupleZipAcc ty combine ignore e1 e2 =
  unAccEnv <$> tupleZipGen ty TIHere weakenId
                   (\t@ArrayR{} tidx w (OpenAccEnv x1) (OpenAccEnv x2) -> OpenAccEnv <$> combine t tidx w x1 x2)
                   (\t@ArrayR{} (OpenAccEnv x) -> ignore t x)
                   (OpenAccEnv e1)
                   (OpenAccEnv e2)

tupleZipAcc' :: ArraysR t
             -> CombinerAcc' t aenv lab ()
             -> IgnorerAcc lab ()
             -> OpenAcc aenv lab () args t
             -> OpenAcc aenv lab () args t
             -> OpenAcc aenv lab () args t
tupleZipAcc' ty combine' ignore e1 e2 =
  runIdentity $ tupleZipAcc ty (\sty tidx w x1 x2 -> pure (combine' sty tidx w x1 x2)) ignore e1 e2
