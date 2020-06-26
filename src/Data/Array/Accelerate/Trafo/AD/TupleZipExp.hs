{-| This is the same as TupleZip, except it's on the main Accelerate AST
    instead of the AD subproject's copy AST with Label. It's also currently
    unused, but it's left here for novelty's sake.
    - Tom Smeding, 2020
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.TupleZipExp (
  tupleZip
) where

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Trafo.Base
import Data.Array.Accelerate.Type


type Combiner lab =
  forall s env.
    ScalarType s -> OpenExp env lab s
                 -> OpenExp env lab s
                 -> Maybe (OpenExp env lab s)

varsZip :: Combiner lab
        -> TupleType t
        -> ExpVars env t
        -> ExpVars env t
        -> Maybe (OpenExp env lab t)
varsZip _ TupRunit VarsNil VarsNil =
  Just Nil
varsZip combine (TupRsingle ty) (VarsSingle v1) (VarsSingle v2) =
  combine ty (Evar v1) (Evar v2)
varsZip combine (TupRpair t1 t2) (VarsPair v11 v12) (VarsPair v21 v22) =
  Pair <$> varsZip combine t1 v11 v21 <*> varsZip combine t2 v12 v22
varsZip _ _ _ _ = error "inconsistency in varsZip"

tupleZip :: forall env lab t. TupleType t
         -> Combiner lab
         -> OpenExp env lab t
         -> OpenExp env lab t
         -> Maybe (OpenExp env lab t)
tupleZip ty combine e1 e2
  | DeclareVars lhs1 _ value1 <- declareVars ty
  , DeclareVars lhs2 _ value2 <- declareVars ty
  = Let lhs1 e1 . Let lhs2 (weakenE (weakenWithLHS lhs1) e2)
      <$> varsZip combine ty (value1 (weakenWithLHS lhs2)) (value2 weakenId)
