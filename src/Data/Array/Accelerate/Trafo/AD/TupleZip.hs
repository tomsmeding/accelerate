{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.TupleZip (
  tupleZip
) where

import qualified Data.Array.Accelerate.AST as A
import Data.Array.Accelerate.AST ((>:>), weakenWithLHS, weakenId, ELeftHandSide, LeftHandSide(..))
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.Base
import Data.Array.Accelerate.Trafo.AD.Exp


data GenLHS env t = forall env'. GenLHS (ELeftHandSide t env env')

type Combiner lab =
  forall s env.
    ScalarType s -> OpenExp env lab s
                 -> OpenExp env lab s
                 -> Maybe (OpenExp env lab s)

sinkExp :: env A.:> env' -> OpenExp env lab t -> OpenExp env' lab t
sinkExp _ (Const ty x) = Const ty x
sinkExp k (PrimApp ty op e) = PrimApp ty op (sinkExp k e)
sinkExp k (Pair ty e1 e2) = Pair ty (sinkExp k e1) (sinkExp k e2)
sinkExp _ Nil = Nil
sinkExp k (Let lhs rhs e) =
    case generaliseLHS lhs of
        GenLHS lhs' -> Let lhs' (sinkExp k rhs) (sinkExp (A.sinkWithLHS lhs lhs' k) e)
sinkExp k (Var (A.Var sty idx)) = Var (A.Var sty (k >:> idx))
sinkExp _ (Label lab) = Label lab

generaliseLHS :: ELeftHandSide t env1 env1' -> GenLHS env2 t
generaliseLHS (LeftHandSideWildcard ty) = GenLHS (LeftHandSideWildcard ty)
generaliseLHS (LeftHandSideSingle ty) = GenLHS (LeftHandSideSingle ty)
generaliseLHS (LeftHandSidePair lhs1 lhs2) =
    case generaliseLHS lhs1 of
        GenLHS lhs1' ->
            case generaliseLHS lhs2 of
                GenLHS lhs2' ->
                    GenLHS (LeftHandSidePair lhs1' lhs2')

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
