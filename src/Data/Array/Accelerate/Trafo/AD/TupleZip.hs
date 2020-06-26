{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.TupleZip (
  tupleZip
) where

import qualified Data.Array.Accelerate.AST as A
import Data.Array.Accelerate.AST (weakenWithLHS, weakenId)
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.Base
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.Sink


type Combiner lab =
  forall s env.
    ScalarType s -> OpenExp env lab s
                 -> OpenExp env lab s
                 -> Maybe (OpenExp env lab s)

varsZip :: Combiner lab
        -> TupleType t
        -> A.ExpVars env t
        -> A.ExpVars env t
        -> Maybe (OpenExp env lab t)
varsZip _ TupRunit A.VarsNil A.VarsNil =
  Just Nil
varsZip combine (TupRsingle ty) (A.VarsSingle v1) (A.VarsSingle v2) =
  combine ty (Var v1) (Var v2)
varsZip combine ty@(TupRpair t1 t2) (A.VarsPair v11 v12) (A.VarsPair v21 v22) =
  Pair ty <$> varsZip combine t1 v11 v21 <*> varsZip combine t2 v12 v22
varsZip _ _ _ _ = error "inconsistency in varsZip"

tupleZip :: forall env lab t. TupleType t
         -> Combiner lab
         -> OpenExp env lab t
         -> OpenExp env lab t
         -> Maybe (OpenExp env lab t)
tupleZip ty combine e1 e2
  | DeclareVars lhs1 _ value1 <- declareVars ty
  , DeclareVars lhs2 _ value2 <- declareVars ty
  = Let lhs1 e1 . Let lhs2 (sinkExp (weakenWithLHS lhs1) e2)
      <$> varsZip combine ty (value1 (weakenWithLHS lhs2)) (value2 weakenId)
