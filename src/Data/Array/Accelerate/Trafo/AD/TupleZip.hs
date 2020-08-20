{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.TupleZip (
  tupleZip
) where

import qualified Data.Array.Accelerate.AST as A
import Data.Array.Accelerate.AST.Environment (weakenWithLHS, weakenId)
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.Sink
import Data.Array.Accelerate.Trafo.Var


type Combiner lab =
  forall s env args.
    ScalarType s -> OpenExp env lab args s
                 -> OpenExp env lab args s
                 -> Maybe (OpenExp env lab args s)

varsZip :: Combiner lab
        -> TypeR t
        -> A.ExpVars env t
        -> A.ExpVars env t
        -> Maybe (OpenExp env lab args t)
varsZip _ TupRunit TupRunit TupRunit =
  Just Nil
varsZip combine (TupRsingle ty) (TupRsingle v1) (TupRsingle v2) =
  combine ty (Var v1) (Var v2)
varsZip combine ty@(TupRpair t1 t2) (TupRpair v11 v12) (TupRpair v21 v22) =
  Pair ty <$> varsZip combine t1 v11 v21 <*> varsZip combine t2 v12 v22
varsZip _ _ _ _ = error "inconsistency in varsZip"

tupleZip :: forall env lab t args.
            TypeR t
         -> Combiner lab
         -> OpenExp env lab args t
         -> OpenExp env lab args t
         -> Maybe (OpenExp env lab args t)
tupleZip ty combine e1 e2
  | DeclareVars lhs1 _ value1 <- declareVars ty
  , DeclareVars lhs2 _ value2 <- declareVars ty
  = Let lhs1 e1 . Let lhs2 (sinkExp (weakenWithLHS lhs1) e2)
      <$> varsZip combine ty (value1 (weakenWithLHS lhs2)) (value2 weakenId)
