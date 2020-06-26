{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.Sink (
  sinkExp
) where

import qualified Data.Array.Accelerate.AST as A
import Data.Array.Accelerate.Trafo.AD.Exp


data GenLHS env t = forall env'. GenLHS (A.ELeftHandSide t env env')

sinkExp :: env A.:> env' -> OpenExp env lab t -> OpenExp env' lab t
sinkExp _ (Const ty x) = Const ty x
sinkExp k (PrimApp ty op e) = PrimApp ty op (sinkExp k e)
sinkExp k (Pair ty e1 e2) = Pair ty (sinkExp k e1) (sinkExp k e2)
sinkExp _ Nil = Nil
sinkExp k (Get ti e) = Get ti (sinkExp k e)
sinkExp k (Let lhs rhs e)
  | GenLHS lhs' <- generaliseLHS lhs =
      Let lhs' (sinkExp k rhs) (sinkExp (A.sinkWithLHS lhs lhs' k) e)
  where
    generaliseLHS :: A.ELeftHandSide t env1 env1' -> GenLHS env2 t
    generaliseLHS (A.LeftHandSideWildcard ty) = GenLHS (A.LeftHandSideWildcard ty)
    generaliseLHS (A.LeftHandSideSingle ty) = GenLHS (A.LeftHandSideSingle ty)
    generaliseLHS (A.LeftHandSidePair lhs1 lhs2)
      | GenLHS lhs1' <- generaliseLHS lhs1
      , GenLHS lhs2' <- generaliseLHS lhs2 =
          GenLHS (A.LeftHandSidePair lhs1' lhs2')
sinkExp k (Var (A.Var sty idx)) = Var (A.Var sty (k A.>:> idx))
sinkExp _ (Label lab) = Label lab
