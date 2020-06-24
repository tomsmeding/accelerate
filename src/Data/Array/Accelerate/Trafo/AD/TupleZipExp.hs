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
import Data.Array.Accelerate.Type


data GenLHS env t = forall env'. GenLHS (ELeftHandSide t env env')
data TZDown lab t =
    TZDown (forall env. GenLHS env t)
           (forall env1 env1' env2 env2' env3.
               ELeftHandSide t env1 env1'
               -> env1' :> env2
               -> ELeftHandSide t env2 env2'
               -> env2' :> env3
               -> Maybe (OpenExp env3 lab t))

tzDown :: forall t lab.
          (forall s env. ScalarType s -> OpenExp env lab s
                                      -> OpenExp env lab s
                                      -> Maybe (OpenExp env lab s))
       -> TupleType t
       -> TZDown lab t
tzDown combine (TupRpair t1 t2) =
  case tzDown combine t1 of
    TZDown genlhs1 resgen1 ->
      case tzDown combine t2 of
        TZDown genlhs2 resgen2 ->
          TZDown
            (case genlhs1 of
               GenLHS genlhs1' ->
                 case genlhs2 of
                   GenLHS genlhs2' ->
                     GenLHS (LeftHandSidePair genlhs1' genlhs2'))
            (\lhs1 weak1 lhs2 weak2 ->
                case lhs1 of
                  LeftHandSidePair lhs11 lhs12 ->
                    case lhs2 of
                      LeftHandSidePair lhs21 lhs22 ->
                        Pair
                          <$> resgen1 lhs11 (weak1 .> weakenWithLHS lhs12) lhs21 (weak2 .> weakenWithLHS lhs22)
                          <*> resgen2 lhs12 (weakenWithLHS lhs21 .> weak1) lhs22 weak2
                      LeftHandSideSingle _ -> error "inconsistency in tzDown"
                      LeftHandSideWildcard _ -> error "inconsistency in tzDown"
                  LeftHandSideSingle _ -> error "inconsistency in tzDown"
                  LeftHandSideWildcard _ -> error "inconsistency in tzDown")
tzDown combine (TupRsingle sty) =
  TZDown (GenLHS (LeftHandSideSingle sty))
         (\lhs1 weak1 lhs2 weak2 ->
             case lhs1 of
               LeftHandSideSingle _ ->
                 case lhs2 of
                   LeftHandSideSingle _ ->
                     combine sty
                       (Evar (Var sty (weak2 >:> SuccIdx (weak1 >:> ZeroIdx))))
                       (Evar (Var sty (weak2 >:> ZeroIdx)))
                   LeftHandSidePair _ _ -> error "inconsistency in tzDown"
                   LeftHandSideWildcard _ -> error "inconsistency in tzDown"
               LeftHandSidePair _ _ -> error "inconsistency in tzDown"
               LeftHandSideWildcard _ -> error "inconsistency in tzDown")
tzDown _ TupRunit =
  TZDown (GenLHS (LeftHandSideWildcard TupRunit)) (\_ _ _ _ -> Just Nil)

sinkExp :: env :> env' -> OpenExp env lab t -> OpenExp env' lab t
sinkExp _ (Const ty x) = Const ty x
sinkExp k (PrimApp op e) = PrimApp op (sinkExp k e)
sinkExp k (Pair e1 e2) = Pair (sinkExp k e1) (sinkExp k e2)
sinkExp _ Nil = Nil
sinkExp k (Let lhs rhs e) =
    case generaliseLHS lhs of
        GenLHS lhs' -> Let lhs' (sinkExp k rhs) (sinkExp (sinkWithLHS lhs lhs' k) e)
sinkExp k (Evar (Var sty idx)) = Evar (Var sty (k >:> idx))

generaliseLHS :: ELeftHandSide t env1 env1' -> GenLHS env2 t
generaliseLHS (LeftHandSideWildcard ty) = GenLHS (LeftHandSideWildcard ty)
generaliseLHS (LeftHandSideSingle ty) = GenLHS (LeftHandSideSingle ty)
generaliseLHS (LeftHandSidePair lhs1 lhs2) =
    case generaliseLHS lhs1 of
        GenLHS lhs1' ->
            case generaliseLHS lhs2 of
                GenLHS lhs2' ->
                    GenLHS (LeftHandSidePair lhs1' lhs2')

tupleZip :: forall env lab t. TupleType t
         -> (forall s env'. ScalarType s -> OpenExp env' lab s
                                         -> OpenExp env' lab s
                                         -> Maybe (OpenExp env' lab s))
         -> OpenExp env lab t
         -> OpenExp env lab t
         -> Maybe (OpenExp env lab t)
tupleZip ty combine e1 e2 =
  case tzDown combine ty of
    TZDown genlhs resgen ->
      case genlhs of
        GenLHS lhs1 ->
          case genlhs of
            GenLHS lhs2 ->
              (Let lhs1 e1 . Let lhs2 (sinkExp (weakenWithLHS lhs1) e2)) <$> resgen lhs1 weakenId lhs2 weakenId
