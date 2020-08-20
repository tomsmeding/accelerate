{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.TupleZip (
  tupleZip, tupleZip'
) where

import Data.Functor.Identity

import qualified Data.Array.Accelerate.AST as A
import Data.Array.Accelerate.AST.Environment (weakenWithLHS, weakenId)
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.Sink
import Data.Array.Accelerate.Trafo.Var


type Combiner m lab =
  forall s env args.
    ScalarType s -> OpenExp env lab args s
                 -> OpenExp env lab args s
                 -> m (OpenExp env lab args s)

type Combiner' lab =
  forall s env args.
    ScalarType s -> OpenExp env lab args s
                 -> OpenExp env lab args s
                 -> OpenExp env lab args s

varsZip :: Applicative m
        => Combiner m lab
        -> TypeR t
        -> A.ExpVars env t
        -> A.ExpVars env t
        -> m (OpenExp env lab args t)
varsZip _ TupRunit TupRunit TupRunit =
  pure Nil
varsZip combine (TupRsingle ty) (TupRsingle v1) (TupRsingle v2) =
  combine ty (Var v1) (Var v2)
varsZip combine ty@(TupRpair t1 t2) (TupRpair v11 v12) (TupRpair v21 v22) =
  Pair ty <$> varsZip combine t1 v11 v21 <*> varsZip combine t2 v12 v22
varsZip _ _ _ _ = error "inconsistency in varsZip"

-- TODO: check whether this is actually used somewhere (and not only tupleZip')
tupleZip :: Applicative m
         => TypeR t
         -> Combiner m lab
         -> OpenExp env lab args t
         -> OpenExp env lab args t
         -> m (OpenExp env lab args t)
tupleZip ty combine e1 e2
  | DeclareVars lhs1 _ value1 <- declareVars ty
  , DeclareVars lhs2 _ value2 <- declareVars ty
  = Let lhs1 e1 . Let lhs2 (sinkExp (weakenWithLHS lhs1) e2)
      <$> varsZip combine ty (value1 (weakenWithLHS lhs2)) (value2 weakenId)

tupleZip' :: TypeR t
          -> Combiner' lab
          -> OpenExp env lab args t
          -> OpenExp env lab args t
          -> OpenExp env lab args t
tupleZip' ty combine' e1 e2 =
  runIdentity $ tupleZip ty (\sty sub1 sub2 -> pure (combine' sty sub1 sub2)) e1 e2
