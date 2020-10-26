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
import Data.Array.Accelerate.AST.Environment ((:>)(..), weakenWithLHS, weakenId)
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.Acc
import Data.Array.Accelerate.Trafo.AD.Sink (sinkAcc)
import Data.Array.Accelerate.Trafo.Var


type CombinerExp m lab alab =
  forall s env aenv args tenv.
    ScalarType s -> OpenExp env aenv lab alab args tenv s
                 -> OpenExp env aenv lab alab args tenv s
                 -> m (OpenExp env aenv lab alab args tenv s)

type CombinerExp' lab alab =
  forall s env aenv args tenv.
    ScalarType s -> OpenExp env aenv lab alab args tenv s
                 -> OpenExp env aenv lab alab args tenv s
                 -> OpenExp env aenv lab alab args tenv s

type CombinerAcc m lab alab =
  forall sh t aenv args.
    ArrayR (Array sh t) -> OpenAcc aenv lab alab args (Array sh t)
                        -> OpenAcc aenv lab alab args (Array sh t)
                        -> m (OpenAcc aenv lab alab args (Array sh t))

type CombinerAcc' lab alab =
  forall sh t aenv args.
    ArrayR (Array sh t) -> OpenAcc aenv lab alab args (Array sh t)
                        -> OpenAcc aenv lab alab args (Array sh t)
                        -> OpenAcc aenv lab alab args (Array sh t)

class ExprLike s f | f -> s where
  nil :: f env ()
  pair :: f env a -> f env b -> f env (a, b)
  var :: A.Var s env t -> f env t
  let_ :: LeftHandSide s t env env' -> f env t -> f env' t' -> f env t'
  fromPair :: f env (a, b) -> Maybe (f env a, f env b)
  sink :: env :> env' -> f env t -> f env' t

newtype OpenExpEnv aenv lab alab args tenv env t =
  OpenExpEnv { unExpEnv :: OpenExp env aenv lab alab args tenv t }

instance ExprLike ScalarType (OpenExpEnv aenv lab alab args tenv) where
  nil = OpenExpEnv Nil
  pair (OpenExpEnv e1) (OpenExpEnv e2) = OpenExpEnv (Pair (TupRpair (etypeOf e1) (etypeOf e2)) e1 e2)
  var = OpenExpEnv . Var
  let_ lhs (OpenExpEnv e1) (OpenExpEnv e2) = OpenExpEnv (Let lhs e1 e2)
  fromPair (OpenExpEnv (Pair _ e1 e2)) = Just (OpenExpEnv e1, OpenExpEnv e2)
  fromPair _ = Nothing
  sink w = OpenExpEnv . sinkExp w . unExpEnv

newtype OpenAccEnv lab alab args aenv t =
  OpenAccEnv { unAccEnv :: OpenAcc aenv lab alab args t }

instance ExprLike ArrayR (OpenAccEnv lab alab args) where
  nil = OpenAccEnv Anil
  pair (OpenAccEnv e1) (OpenAccEnv e2) = OpenAccEnv (Apair (TupRpair (atypeOf e1) (atypeOf e2)) e1 e2)
  var v@(A.Var (ArrayR _ _) _) = OpenAccEnv (Avar v)
  let_ lhs (OpenAccEnv e1) (OpenAccEnv e2) = OpenAccEnv (Alet lhs e1 e2)
  fromPair (OpenAccEnv (Apair _ e1 e2)) = Just (OpenAccEnv e1, OpenAccEnv e2)
  fromPair _ = Nothing
  sink w = OpenAccEnv . sinkAcc w . unAccEnv

type CombinerGen m s f = forall t env. s t -> f env t -> f env t -> m (f env t)

varsZip :: (Applicative m, ExprLike s f)
        => CombinerGen m s f
        -> TupR s t
        -> A.Vars s env t
        -> A.Vars s env t
        -> m (f env t)
varsZip _ TupRunit TupRunit TupRunit =
  pure nil
varsZip combine (TupRsingle ty) (TupRsingle v1) (TupRsingle v2) =
  combine ty (var v1) (var v2)
varsZip combine (TupRpair t1 t2) (TupRpair v11 v12) (TupRpair v21 v22) =
  pair <$> varsZip combine t1 v11 v21 <*> varsZip combine t2 v12 v22
varsZip _ _ _ _ = error "inconsistency in varsZip"

tupleZipGen :: (Applicative m, ExprLike s f) => TupR s t -> CombinerGen m s f -> f env t -> f env t -> m (f env t)
tupleZipGen TupRunit _ _ _ = pure nil
tupleZipGen (TupRsingle ty) combine e1 e2 = combine ty e1 e2
tupleZipGen (TupRpair t1 t2) combine (fromPair -> Just (e11, e12)) (fromPair -> Just (e21, e22)) =
  pair <$> tupleZipGen t1 combine e11 e21 <*> tupleZipGen t2 combine e12 e22
tupleZipGen ty combine e1 e2
  | DeclareVars lhs1 _ value1 <- declareVars ty
  , DeclareVars lhs2 _ value2 <- declareVars ty
  = let_ lhs1 e1 . let_ lhs2 (sink (weakenWithLHS lhs1) e2)
      <$> varsZip combine ty (value1 (weakenWithLHS lhs2)) (value2 weakenId)

-- TODO: check whether this is actually used somewhere (and not only tupleZipExp')
tupleZipExp :: Applicative m
            => TypeR t
            -> CombinerExp m lab alab
            -> OpenExp env aenv lab alab args tenv t
            -> OpenExp env aenv lab alab args tenv t
            -> m (OpenExp env aenv lab alab args tenv t)
tupleZipExp ty combine e1 e2 =
  unExpEnv <$> tupleZipGen ty (\t (OpenExpEnv x1) (OpenExpEnv x2) -> OpenExpEnv <$> combine t x1 x2) (OpenExpEnv e1) (OpenExpEnv e2)

tupleZipExp' :: TypeR t
             -> CombinerExp' lab alab
             -> OpenExp env aenv lab alab args tenv t
             -> OpenExp env aenv lab alab args tenv t
             -> OpenExp env aenv lab alab args tenv t
tupleZipExp' ty combine' e1 e2 =
  runIdentity $ tupleZipExp ty (\sty sub1 sub2 -> pure (combine' sty sub1 sub2)) e1 e2

-- TODO: check whether this is actually used somewhere (and not only tupleZipAcc')
tupleZipAcc :: Applicative m
            => ArraysR t
            -> CombinerAcc m lab alab
            -> OpenAcc aenv lab alab args t
            -> OpenAcc aenv lab alab args t
            -> m (OpenAcc aenv lab alab args t)
tupleZipAcc ty combine e1 e2 =
  unAccEnv <$> tupleZipGen ty (\t@(ArrayR _ _) (OpenAccEnv x1) (OpenAccEnv x2) -> OpenAccEnv <$> combine t x1 x2) (OpenAccEnv e1) (OpenAccEnv e2)

tupleZipAcc' :: ArraysR t
             -> CombinerAcc' lab alab
             -> OpenAcc aenv lab alab args t
             -> OpenAcc aenv lab alab args t
             -> OpenAcc aenv lab alab args t
tupleZipAcc' ty combine' e1 e2 =
  runIdentity $ tupleZipAcc ty (\sty x1 x2 -> pure (combine' sty x1 x2)) e1 e2
