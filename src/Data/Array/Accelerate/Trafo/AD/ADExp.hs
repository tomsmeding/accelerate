{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Accelerate.Trafo.AD.ADExp (
  reverseAD, ReverseADResE(..),
  splitLambdaAD, labeliseFunA,
  labeliseExpA, inlineAvarLabels'
) where

import qualified Control.Monad.Writer as W
import Data.List (sort)
import Data.GADT.Compare (GCompare(..))
import Data.Function ((&))
import qualified Data.Functor.Product as Product
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Map (DMap)
import Data.Dependent.Sum
import Data.Maybe (fromMaybe)
import Data.Some
import Data.Type.Equality
import GHC.Stack (HasCallStack)

import qualified Data.Array.Accelerate.AST as A
import Data.Array.Accelerate.AST (ELeftHandSide)
import qualified Data.Array.Accelerate.AST.Environment as A
import Data.Array.Accelerate.AST.LeftHandSide
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.Analysis.Match (matchScalarType, matchTypeR)
import Data.Array.Accelerate.Error (internalError)
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (shapeType)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Shows (showPrimFun)
import Data.Array.Accelerate.Trafo.AD.Additive
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Debug
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.Pretty
import Data.Array.Accelerate.Trafo.Substitution (rebuildLHS)


genId :: TypeR t -> IdGen (EDLabelN Int t)
genId = genId'

genIdNodeSingle :: ScalarType t -> IdGen (EDLabelNS Int t)
genIdNodeSingle = genId'

genSingleId :: ScalarType t -> IdGen (EDLabel Int t)
genSingleId = genId'

genSingleIds :: TypeR t -> IdGen (Exists (ELeftHandSide t env), TupR (EDLabel Int) t)
genSingleIds TupRunit = return (Exists (LeftHandSideWildcard TupRunit), TupRunit)
genSingleIds (TupRsingle ty) = (Exists (LeftHandSideSingle ty),) . TupRsingle <$> genSingleId ty
genSingleIds (TupRpair t1 t2) = do
    (Exists lhs1, ids1) <- genSingleIds t1
    (Exists lhs2, ids2) <- genSingleIds t2
    return (Exists (LeftHandSidePair lhs1 lhs2), TupRpair ids1 ids2)


-- Assumes the expression does not contain Arg
generaliseArgs :: OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args' tenv t
generaliseArgs (Const lab x) = Const lab x
generaliseArgs (PrimApp lab op ex) = PrimApp lab op (generaliseArgs ex)
generaliseArgs (PrimConst lab c) = PrimConst lab c
generaliseArgs (Pair lab e1 e2) = Pair lab (generaliseArgs e1) (generaliseArgs e2)
generaliseArgs (Nil lab) = Nil lab
generaliseArgs (Cond lab e1 e2 e3) = Cond lab (generaliseArgs e1) (generaliseArgs e2) (generaliseArgs e3)
generaliseArgs (Shape lab ref) = Shape lab ref
generaliseArgs (Index lab ref execLab idx) = Index lab ref execLab (generaliseArgs idx)
generaliseArgs (ShapeSize lab sht e) = ShapeSize lab sht (generaliseArgs e)
generaliseArgs (Get lab path ex) = Get lab path (generaliseArgs ex)
generaliseArgs (Undef lab) = Undef lab
generaliseArgs (Let lhs rhs ex) = Let lhs (generaliseArgs rhs) (generaliseArgs ex)
generaliseArgs (Var lab var referLab) = Var lab var referLab
generaliseArgs (FreeVar lab var) = FreeVar lab var
generaliseArgs (Arg _ _ _) = error "generaliseArgs: Arg found"

-- Replaces all array variables by their labels in the array environment, and additionally returns the list of labels thus inserted.
-- The list of labels is deduplicated.
-- Asserts that there are no array labels yet in the expression, and resets the array environment.
labeliseFunA :: Ord alab
             => TagVal (AAnyPartLabelN alab) aenv
             -> OpenFun env aenv lab alab' tenv t
             -> ([Some (AAnyPartLabelN alab)], OpenFun env aenv' lab alab tenv t)
labeliseFunA labelenv (Lam lhs fun) = Lam lhs <$> labeliseFunA labelenv fun
labeliseFunA labelenv (Body ex) = Body <$> labeliseExpA labelenv ex

-- Replaces all array variables by their labels in the array environment, and additionally returns the list of labels thus inserted.
-- The list of labels is deduplicated.
-- Asserts that there are no array labels yet in the expression, and resets the array environment.
labeliseExpA :: Ord alab
             => TagVal (AAnyPartLabelN alab) aenv
             -> OpenExp env aenv lab alab' args tenv t
             -> ([Some (AAnyPartLabelN alab)], OpenExp env aenv' lab alab args tenv t)
labeliseExpA labelenv = \ex -> let (labs, ex') = go ex
                               in (sortUniq labs, ex')
  where
    go ex = case ex of
      Const lab x -> return (Const lab x)
      PrimApp lab op e -> PrimApp lab op <$> labeliseExpA labelenv e
      PrimConst lab c -> return (PrimConst lab c)
      Pair lab e1 e2 -> Pair lab <$> labeliseExpA labelenv e1 <*> labeliseExpA labelenv e2
      Nil lab -> return (Nil lab)
      Cond lab e1 e2 e3 -> Cond lab <$> labeliseExpA labelenv e1 <*> labeliseExpA labelenv e2 <*> labeliseExpA labelenv e3
      Shape lab (Left (A.Var _ idx)) -> do
          let alab = prjT idx labelenv
          W.tell [Some alab]
          return (Shape lab (Right alab))
      Shape _ (Right _) -> error "Unexpected Shape(Label) in labeliseExpA"
      Index lab (Left (A.Var _ idx)) execLab idxe -> do
          let alab = prjT idx labelenv
          W.tell [Some alab]
          Index lab (Right alab) execLab <$> labeliseExpA labelenv idxe
      Index _ (Right _) _ _ -> error "Unexpected Index(Label) in labeliseExpA"
      ShapeSize lab sht e -> ShapeSize lab sht <$> labeliseExpA labelenv e
      Get lab ti e -> Get lab ti <$> labeliseExpA labelenv e
      Undef lab -> return (Undef lab)
      Let lhs rhs e -> Let lhs <$> labeliseExpA labelenv rhs <*> labeliseExpA labelenv e
      Arg lab argsty tidx -> return (Arg lab argsty tidx)
      Var lab var referLab -> return (Var lab var referLab)
      FreeVar lab var -> return (FreeVar lab var)

inlineAvarLabels :: (HasCallStack, Ord alab)
                 => TupR (AAnyPartLabelN alab) fv
                 -> A.ArrayVars aenv' fv
                 -> OpenExp env aenv lab alab args tenv t
                 -> OpenExp env aenv' lab alab' args tenv t
inlineAvarLabels labs vars =
    let mp = zipTupRmap labs vars
    in inlineAvarLabels' (\lab -> case DMap.lookup lab mp of
                                    Just var -> var
                                    Nothing -> error "inlineAvarLabels: Not all labels instantiated")

inlineAvarLabels' :: (forall sh t'. AAnyPartLabelN alab (Array sh t') -> A.ArrayVar aenv' (Array sh t'))
                  -> OpenExp env aenv lab alab args tenv t
                  -> OpenExp env aenv' lab alab' args tenv t
inlineAvarLabels' f = \case
    Const lab x -> Const lab x
    PrimApp lab op ex -> PrimApp lab op (inlineAvarLabels' f ex)
    PrimConst lab c -> PrimConst lab c
    Pair lab e1 e2 -> Pair lab (inlineAvarLabels' f e1) (inlineAvarLabels' f e2)
    Nil lab -> Nil lab
    Cond lab e1 e2 e3 -> Cond lab (inlineAvarLabels' f e1) (inlineAvarLabels' f e2) (inlineAvarLabels' f e3)
    Shape lab (Right alab) -> Shape lab (Left (f alab))
    Shape _ (Left _) -> error "inlineAvarLabels': Array variable found in labelised expression (Shape)"
    ShapeSize lab sht e -> ShapeSize lab sht (inlineAvarLabels' f e)
    Index lab (Right alab) execLab idxe -> Index lab (Left (f alab)) execLab (inlineAvarLabels' f idxe)
    Index _ (Left _) _ _ -> error "inlineAvarLabels': Array variable found in labelised expression (Index)"
    Get lab tidx ex -> Get lab tidx (inlineAvarLabels' f ex)
    Undef lab -> Undef lab
    Let lhs rhs ex -> Let lhs (inlineAvarLabels' f rhs) (inlineAvarLabels' f ex)
    Var lab v referLab -> Var lab v referLab
    FreeVar lab v -> FreeVar lab v
    Arg lab argsty tidx -> Arg lab argsty tidx

data ReverseADResE aenv alab tenv t =
    forall env.
        ReverseADResE (A.ELeftHandSide t () env)
                      (OpenExp env aenv () alab () tenv t)

reverseAD :: Show alab
          => ELeftHandSide t () env
          -> OpenExp env aenv () alab () tenv Float
          -> ReverseADResE aenv alab tenv t
reverseAD paramlhs expr = evalIdGen $ do
    let paramty = lhsToTupR paramlhs
        argsRHS = untupleExps
                      (zipWithTupR (\ty tidx -> Arg (nilLabel ty) paramty tidx)
                                   paramty
                                   (tupleIndices paramty))
        closedExpr = Let paramlhs argsRHS (generaliseArgs expr)
    expr' <- enlabelExp TEmpty closedExpr

    traceM ("exp labeled:\n" ++ prettyPrint expr')

    PrimalResult (EBuilder primalCtx primalBuilder) _ _ <-
        primal (Context LEmpty mempty) expr'

    let cmap0 = DMap.singleton (Local (elabelOf expr')) (AdjList (\_ -> [Const scalarLabel 1.0]))
    DualResult (EBuilder dualCtx dualBuilder) _ dualCMap <- dual primalCtx cmap0 expr'
    let (gradient, _) = collectAdjointCMap dualCMap (Argument paramty) dualCtx

    return $ ReverseADResE
        paramlhs
        (realiseArgs paramlhs
            (primalBuilder
             . dualBuilder
             $ gradient))

splitLambdaAD :: forall t t' tenv.
                 Fun () () Int tenv (t -> t')
              -> SomeSplitLambdaAD t t' () Int tenv
splitLambdaAD (Lam paramlhs (Body expr))
  | let paramty = lhsToTupR paramlhs
        resty = etypeOf expr
        argsRHS = untupleExps
                      (zipWithTupR (\ty tidx -> Arg (nilLabel ty) paramty tidx)
                                   paramty
                                   (tupleIndices paramty))
        closedExpr = Let paramlhs argsRHS (generaliseArgs expr)
  , fvlablist <- sortUniq (expALabels closedExpr)
  , Some fvlabs <- tuplify fvlablist
  = evalIdGen $ do
      expr' <- enlabelExp TEmpty closedExpr

      traceM ("exp labeled:\n" ++ prettyPrint expr')

      PrimalResult (EBuilder primalCtx primalBuilder) primalStores primalOutput <-
          primal (Context LEmpty mempty) expr'
      Some' primalTmplabs <- returnSome (tuplify primalStores)
      let primalCore = evars (resolveEnvLabs primalCtx (TupRpair primalOutput primalTmplabs))

      (Exists adjlhs, adjlabs) <- genSingleIds resty
      LetBoundVars tmplhs _ <- return (lhsCopy (fmapTupR labelType primalTmplabs))
      let dualLabelenv = LEmpty & lpushLabTup adjlhs adjlabs
                                & lpushLabTup tmplhs primalTmplabs
          dualBindmap = DMap.insert (Local (fmapLabel D (elabelOf expr'))) adjlabs
                                    (let Context _ bm = primalCtx in bm)
          dualCMapIn = DMap.singleton (Local (elabelOf expr'))
                                      (AdjList (\ctx2 -> [evars (resolveEnvLabs ctx2 adjlabs)]))
      DualResult (EBuilder dualCtx dualBuilder) _ dualCMap <-
          dual (Context dualLabelenv dualBindmap) dualCMapIn expr'
      let (gradient, _) = collectAdjointCMap dualCMap (Argument paramty) dualCtx
          indexNodes = listIndexNodes expr'
      traceM ("exp dualCtx: " ++ showContext dualCtx)
      CollectIndexAdjoints idxadjExpr idxadjInsts <- return (collectIndexAdjoints indexNodes dualCtx)
      let dualCore = smartPair gradient idxadjExpr

      return $ SomeSplitLambdaAD $ SplitLambdaAD
          (\fvavars ->
              Lam paramlhs (Body
                  (realiseArgs paramlhs
                      (inlineAvarLabels fvlabs fvavars
                          (primalBuilder primalCore)))))
          (\fvavars ->
              Lam (LeftHandSidePair adjlhs tmplhs) (Body
                  (inlineAvarLabels fvlabs fvavars
                      (generaliseArgs (dualBuilder dualCore)))))
          fvlabs
          (fmapTupR labelType primalTmplabs)
          (etypeOf idxadjExpr)
          idxadjInsts
splitLambdaAD _ =
    internalError "splitLambdaAD passed function with more than 1 argument"

-- Produces an expression that can be put under a LHS that binds exactly the
-- 'args' of the original expression.
realiseArgs :: forall args argsenv aenv alab tenv res.
               ELeftHandSide args () argsenv
            -> Exp aenv () alab args tenv res
            -> OpenExp argsenv aenv () alab () tenv res
realiseArgs paramlhs = \expr -> go A.weakenId (A.weakenWithLHS paramlhs) expr
  where
    go :: argsenv A.:> env' -> env A.:> env' -> OpenExp env aenv () alab args tenv t -> OpenExp env' aenv () alab () tenv t
    go argWeaken varWeaken expr = case expr of
        Const lab x -> Const lab x
        PrimApp lab op ex -> PrimApp lab op (go argWeaken varWeaken ex)
        PrimConst lab c -> PrimConst lab c
        Pair lab e1 e2 -> Pair lab (go argWeaken varWeaken e1) (go argWeaken varWeaken e2)
        Nil lab -> Nil lab
        Cond lab e1 e2 e3 -> Cond lab (go argWeaken varWeaken e1) (go argWeaken varWeaken e2) (go argWeaken varWeaken e3)
        Shape lab ref -> Shape lab ref
        Index lab ref execLab idxe -> Index lab ref execLab (go argWeaken varWeaken idxe)
        ShapeSize lab sht e -> ShapeSize lab sht (go argWeaken varWeaken e)
        Get lab tidx ex -> Get lab tidx (go argWeaken varWeaken ex)
        Undef lab -> Undef lab
        Let lhs rhs ex
          | Exists lhs' <- rebuildLHS lhs ->
              Let lhs' (go argWeaken varWeaken rhs)
                  (go (A.weakenWithLHS lhs' A..> argWeaken) (A.sinkWithLHS lhs lhs' varWeaken) ex)
        Var lab (A.Var ty idx) referLab -> Var lab (A.Var ty (varWeaken A.>:> idx)) referLab
        FreeVar lab var -> FreeVar lab var
        Arg lab _ tidx ->
            case indexIntoLHS paramlhs tidx of
              Just idx -> let nillab = nilLabel (labelType lab)
                          in Var nillab (A.Var (labelType lab) (argWeaken A.>:> idx))
                                 (PartLabel (tupleLabel nillab) TIHere)
              Nothing -> Undef (nilLabel (labelType lab))

data IndexNodeInfo lab alab =
    forall sh t.
        IndexNodeInfo (EDLabelN lab t)               -- The label of the Index
                      (EDLabelN lab sh)              -- The label of the target index node
                      (EDLabelNS lab A.PrimBool)     -- The label of the virtual was-executed node
                      (AAnyPartLabelN alab (Array sh t))  -- The array label of the indexed array

listIndexNodes :: OpenExp env aenv lab alab args tenv t -> [IndexNodeInfo lab alab]
listIndexNodes (Const _ _) = []
listIndexNodes (PrimApp _ _ ex) = listIndexNodes ex
listIndexNodes (PrimConst _ _) = []
listIndexNodes (Pair _ e1 e2) = listIndexNodes e1 ++ listIndexNodes e2
listIndexNodes (Nil _) = []
listIndexNodes (Cond _ e1 e2 e3) = listIndexNodes e1 ++ listIndexNodes e2 ++ listIndexNodes e3
listIndexNodes (Shape _ _) = []
listIndexNodes (Index lab (Right alab) execLab e) =
    IndexNodeInfo lab (elabelOf e) execLab alab : listIndexNodes e
listIndexNodes (Index _ (Left _) _ _) = error "listIndexNodes: Array variables not labelised"
listIndexNodes (ShapeSize _ _ e) = listIndexNodes e
listIndexNodes (Get _ _ ex) = listIndexNodes ex
listIndexNodes (Undef _) = []
listIndexNodes (Let _ rhs ex) = listIndexNodes rhs ++ listIndexNodes ex
listIndexNodes (Var _ _ _) = []
listIndexNodes (FreeVar _ _) = []
listIndexNodes (Arg _ _ _) = []

data CollectIndexAdjoints env aenv alab args tenv =
    forall idxadj.
        CollectIndexAdjoints (OpenExp env aenv () alab args tenv idxadj)
                             (DMap (AAnyPartLabelN alab) (IndexInstantiators idxadj))

collectIndexAdjoints :: (Ord lab, Show lab, Ord alab)
                     => [IndexNodeInfo lab alab]
                     -> EContext lab env
                     -> CollectIndexAdjoints env aenv alab args tenv
collectIndexAdjoints indexNodes dualCtx =
    let constructExp :: (Ord lab, Show lab)
                     => EContext lab env -> IndexNodeInfo lab alab -> Some (OpenExp env aenv () alab args tenv)
        constructExp dualCtx' (IndexNodeInfo adjlab idxlab execlab _) =
            let adjexpr = evars . resolveEnvLabs dualCtx' <$> findAdjointBMap' dualCtx' adjlab
                idxexpr = evars (resolveEnvLabs dualCtx' (findPrimalBMap dualCtx' idxlab))
                execexpr = evars (resolveEnvLabs dualCtx' (findPrimalBMap dualCtx' execlab))
            in Some (smartPair (smartPair (fromMaybe (zeroForType (labelType adjlab)) adjexpr) idxexpr) execexpr)
        constructAlab (IndexNodeInfo _ _ _ alab) = Some alab
    in case tuplify' indexNodes (constructExp dualCtx) constructAlab of
         TuplifyWithTrace tup tupTraces ->
             CollectIndexAdjoints
                 (untupleExps tup)
                 (DMap.fromListWithKey (const (<>))
                     [case (etypeOf expr, partLabelSmallType partl) of
                        (triplety@(TupRpair (TupRpair eltty shty) (TupRsingle boolty)),
                             TupRsingle (ArrayR (shapeType -> shty') eltty'))
                          | Just Refl <- matchTypeR eltty eltty'
                          , Just Refl <- matchTypeR shty shty'
                          , Just Refl <- matchScalarType boolty (scalarType :: ScalarType A.PrimBool) ->
                              AnyPartLabel partl :=> IndexInstantiators [IndexInstantiator (Get (nilLabel triplety) tidx)]
                        _ -> error "invalid GADTs"
                     | (Some (AnyPartLabel partl), Some (Product.Pair expr tidx)) <- tupTraces])

enlabelExp :: TagVal (EAnyPartLabelN Int) env -> OpenExp env aenv () alab args tenv t -> IdGen (OpenExp env aenv Int alab args tenv t)
enlabelExp env expr = case expr of
    Const lab x -> Const <$> genLabNS lab <*> return x
    PrimApp lab op ex -> PrimApp <$> genLabN lab <*> return op <*> enlabelExp env ex
    PrimConst lab c -> PrimConst <$> genLabNS lab <*> return c
    Pair lab e1 e2 -> Pair <$> genLabN lab <*> enlabelExp env e1 <*> enlabelExp env e2
    Nil lab -> Nil <$> genLabN lab
    Cond lab e1 e2 e3 -> Cond <$> genLabN lab <*> enlabelExp env e1 <*> enlabelExp env e2 <*> enlabelExp env e3
    Shape lab ref -> Shape <$> genLabN lab <*> return ref
    Index lab ref execLab idxe -> Index <$> genLabN lab <*> return ref <*> genLabNS execLab <*> enlabelExp env idxe
    ShapeSize lab sht e -> ShapeSize <$> genLabNS lab <*> return sht <*> enlabelExp env e
    Get lab tidx e -> Get <$> genLabN lab <*> return tidx <*> enlabelExp env e
    Undef lab -> Undef <$> genLabNS lab
    Let lhs rhs ex -> do
        rhs' <- enlabelExp env rhs
        Let lhs <$> return rhs' <*> enlabelExp (lpushLHS_parts env (elabelOf rhs') TIHere lhs) ex
    Var lab var@(A.Var _ idx) _
      | AnyPartLabel pl <- prjT idx env ->
          Var <$> genLabNS lab <*> return var <*> return pl
    FreeVar lab var -> FreeVar <$> genLabNS lab <*> return var
    Arg lab argsty tidx -> Arg <$> genLabNS lab <*> return argsty <*> return tidx
  where
    genLabN :: EDLabelN () t -> IdGen (EDLabelN Int t)
    genLabN = genId . labelType

    genLabNS :: EDLabelNS () t -> IdGen (EDLabelNS Int t)
    genLabNS = genIdNodeSingle . labelType

data EBuilder env aenv alab args tenv =
    forall env'.
        EBuilder (EContext Int env')
                 (forall res. OpenExp env' aenv () alab args tenv res
                           -> OpenExp env aenv () alab args tenv res)

data PrimalResult env aenv alab args tenv t =
    PrimalResult (EBuilder env aenv alab args tenv)  -- Primal builder
                 [Some (EDLabel Int)]                -- To-store "set" (really list)
                 (TupR (EDLabel Int) t)              -- Env labels of the subtree root

primal :: Show alab
       => EContext Int env
       -> OpenExp progenv aenv Int alab args tenv t
       -> IdGen (PrimalResult env aenv alab args tenv t)
primal ctx = \case
    -- e | trace ("exp primal: " ++ head (words (show e))) False -> undefined

    Const lab value ->
        simplePrimal TLNil ctx lab (\_ lab' _ -> Const lab' value)

    PrimApp lab oper arg ->
        simplePrimal (arg :@ TLNil) ctx lab (\_ lab' (arg' :@ _) -> PrimApp lab' oper arg')

    PrimConst lab value ->
        simplePrimal TLNil ctx lab (\_ lab' _ -> PrimConst lab' value)

    Pair lab arg1 arg2 ->
        simplePrimal (arg1 :@ arg2 :@ TLNil) ctx lab (\_ lab' (arg1' :@ arg2' :@ _) -> Pair lab' arg1' arg2')

    Nil lab ->
        simplePrimal TLNil ctx lab (\_ lab' _ -> Nil lab')

    Cond lab argC argT argE -> do
        PrimalResult (EBuilder ctxC fC) storesC labsC <- primal ctx argC
        PrimalResult (EBuilder ctxT fT) storesT labsT <- primal ctxC argT
        PrimalResult (EBuilder ctxE fE) storesE labsE <- primal ctxC argE
        Some' tmplabsT <- returnSome (tuplify storesT)
        Some' tmplabsE <- returnSome (tuplify storesE)
        let tmptyT = fmapTupR labelType tmplabsT
            tmptyE = fmapTupR labelType tmplabsE
            branchty = TupRpair (labelType lab) (TupRpair tmptyT tmptyE)
        (Exists lhs, envlabs) <- genSingleIds (labelType lab)
        LetBoundVars lhsT _ <- return (lhsCopy tmptyT)
        LetBoundVars lhsE _ <- return (lhsCopy tmptyE)
        let Context labelenv bindmap = ctxPush lhs (fmapLabel P lab) envlabs ctxC
            labelenv' = labelenv & lpushLabTup lhsT tmplabsT
                                 & lpushLabTup lhsE tmplabsE
            bindmap' = dmapDisjointUnions
                          [bindmap
                          ,let Context _ bm = ctxT in bm DMap.\\ bindmap
                          ,let Context _ bm = ctxE in bm DMap.\\ bindmap]
        return $ PrimalResult
            (EBuilder (Context labelenv' bindmap')
                      (fC . Let (LeftHandSidePair lhs (LeftHandSidePair lhsT lhsE))
                                (Cond (nilLabel branchty)
                                      (evars (resolveEnvLabs ctxC labsC))
                                      (fT (smartPair
                                              (evars (resolveEnvLabs ctxT labsT))
                                              (smartPair
                                                  (evars (resolveEnvLabs ctxT tmplabsT))
                                                  (zeroForType tmptyE))))
                                      (fE (smartPair
                                              (evars (resolveEnvLabs ctxE labsE))
                                              (smartPair
                                                  (zeroForType tmptyT)
                                                  (evars (resolveEnvLabs ctxE tmplabsE))))))))
            (concat [enumerateTupR envlabs
                    ,storesC
                    ,enumerateTupR tmplabsT
                    ,enumerateTupR tmplabsE])
            envlabs

    Shape lab ref ->
        simplePrimal TLNil ctx lab (\_ lab' _ -> Shape lab' ref)

    Index lab ref execLab arg -> do
        -- This is not simplePrimal because we want to additionally store the "executed" flag.
        PrimalResult (EBuilder ctx' f1) stores1 arglabs1 <- primal ctx arg
        (Exists lhs, envlabs) <- genSingleIds (toTupleType (labelType lab))
        execEnvLab <- genSingleId scalarType
        let exp' = Index (nilLabel (labelType lab)) ref scalarLabel (evars (resolveEnvLabs ctx' arglabs1)) 
        return $ PrimalResult
            (EBuilder (ctx'
                       & ctxPush lhs (fmapLabel P lab) envlabs
                       & ctxPush (LeftHandSideSingle scalarType) (fmapLabel P (tupleLabel execLab))
                                 (TupRsingle execEnvLab))
                      (f1 . Let lhs exp' . Let (LeftHandSideSingle scalarType) (Const scalarLabel 1)))
            (enumerateTupR envlabs ++ [Some execEnvLab] ++ stores1)
            envlabs

    ShapeSize lab sht arg ->
        simplePrimal (arg :@ TLNil) ctx lab (\_ lab' (arg' :@ _) -> ShapeSize lab' sht arg')

    Get lab tidx arg ->
        simplePrimal (arg :@ TLNil) ctx lab (\_ lab' (arg' :@ _) -> Get lab' tidx arg')

    Undef lab ->
        simplePrimal TLNil ctx lab (\_ lab' _ -> Undef lab')

    Let _ rhs body -> do
        -- It's not a simplePrimal because it doesn't generate labels; in fact
        -- it's even simpler than simplePrimal.
        PrimalResult (EBuilder ctx1 f1) stores1 _ <- primal ctx rhs
        PrimalResult (EBuilder ctx2 f2) stores2 arglabs2 <- primal ctx1 body
        return $ PrimalResult
            (EBuilder ctx2 (f1 . f2))
            (stores1 ++ stores2)
            arglabs2

    Var lab _ (PartLabel referLab referPart) -> do
        simplePrimal TLNil ctx lab (\ctx' _ _ ->
            case pickTupR referPart (resolveEnvLabs ctx' (findPrimalBMap ctx' referLab)) of
              TupRsingle var -> smartVar var
              _ -> error "impossible GADTs")

    FreeVar lab var ->
        simplePrimal TLNil ctx lab (\_ lab' _ -> FreeVar lab' var)

    Arg lab argsty tidx ->
        simplePrimal TLNil ctx lab (\_ lab' _ -> Arg lab' argsty tidx)

simplePrimal :: (IsTupleType ScalarType s, GCompare s, Show alab)
             => TypedList (OpenExp progenv aenv Int alab args tenv) argts
             -> EContext Int env
             -> DLabel NodeLabel s Int t
             -> (forall env'.
                    EContext Int env'
                 -> DLabel nodeLabel s () t
                 -> TypedList (OpenExp env' aenv () alab args tenv) argts
                 -> OpenExp env' aenv () alab args tenv t)
             -> IdGen (PrimalResult env aenv alab args tenv t)
simplePrimal args ctx lab buildf =
    runArgs args ctx $ \(EBuilder ctx' f1) stores arglabss -> do
        (Exists lhs, envlabs) <- genSingleIds (toTupleType (labelType lab))
        let exp' = buildf ctx' (nilLabel (labelType lab))
                               (tlmap (evars . resolveEnvLabs ctx') arglabss)
        return $ PrimalResult
            (EBuilder (ctxPush lhs (fmapLabel P (tupleLabel lab)) envlabs ctx')
                      (f1 . Let lhs exp'))
            (enumerateTupR envlabs ++ stores)
            envlabs
  where
    runArgs :: Show alab
            => TypedList (OpenExp progenv aenv Int alab args tenv) argts
            -> EContext Int env
            -> (   EBuilder env aenv alab args tenv
                -> [Some (EDLabel Int)]
                -> TypedList (TupR (EDLabel Int)) argts
                -> IdGen r)
            -> IdGen r
    runArgs TLNil ctx' cont = cont (EBuilder ctx' id) [] TLNil
    runArgs (arg :@ args') ctx' cont = do
        PrimalResult (EBuilder ctx1 f1) stores1 arglabs1 <- primal ctx' arg
        runArgs args' ctx1 $ \(EBuilder ctx2 f2) stores2 arglabss2 ->
            cont (EBuilder ctx2 (f1 . f2))
                 (stores1 ++ stores2)
                 (arglabs1 :@ arglabss2)

-- List of adjoints, collected for a particular label.
-- The exact variable references in the adjoints are dependent on the Let stack, thus the
-- environment (and the bindmap) is needed.
newtype AdjList aenv lab alab args tenv t =
    AdjList (forall env. EContext lab env -> [OpenExp env aenv () alab args tenv t])

instance Semigroup (AdjList aenv lab alab args tenv t) where
    AdjList f1 <> AdjList f2 = AdjList (\ctx -> f1 ctx ++ f2 ctx)

data DualResult env aenv alab args tenv =
    DualResult (EBuilder env aenv alab args tenv)  -- Dual builder
               [Some (EDLabelN Int)]               -- To-store "set" (really list)
               (DMap (CMapKey ScalarType Int)      -- Contribution map
                     (AdjList aenv Int alab args tenv))

dual :: Show alab
     => EContext Int env
     -> DMap (CMapKey ScalarType Int) (AdjList aenv Int alab args tenv)  -- Contribution map
     -> OpenExp progenv aenv Int alab args tenv t
     -> IdGen (DualResult env aenv alab args tenv)
dual ctx cmap = \case
    e | trace ("exp dual: " ++ head (words (show e))) False -> undefined

    PrimApp lab oper arg
      -- If 'oper' has integral arguments or an integral result, we have no
      -- need to compute the adjoint of the argument (it would be zero anyway).
      | isIntegralType (etypeOf arg) || isIntegralType (labelType lab) -> do
          traceM ("!dual PrimApp[" ++ showDLabel lab ++ "]: empty")
          return (emptyDual ctx cmap)

      | otherwise -> do
          let (adjoint, cmap') = collectAdjointCMap cmap (Local lab) ctx
          (Exists lhs, envlabs) <- genSingleIds (labelType lab)
          let ctx' = ctxPush lhs (fmapLabel D lab) envlabs ctx
              cmap'' = addContrib (Local (elabelOf arg))
                                  (\ctx2 ->
                                      let adjoint' = evars (resolveEnvLabs ctx2 (findAdjointBMap ctx2 lab))
                                          argPrimal = evars (resolveEnvLabs ctx2 (findPrimalBMap ctx2 (elabelOf arg)))
                                          resultPrimal = evars (resolveEnvLabs ctx2 (findPrimalBMap ctx2 lab))
                                          -- Note that 'argPrimal', 'argResult' and 'adjoint' are just
                                          -- tuples of variable references, so they are cheap to duplicate.
                                          argDeriv = primAppDerivative (etypeOf arg) oper argPrimal resultPrimal adjoint'
                                      in argDeriv)
                                  cmap'
          traceM ("!dual PrimApp[" ++ showDLabel lab ++ "]: envlabs = " ++ showTupR showDLabel envlabs)
          DualResult (EBuilder ctx1 f1) stores1 cmap1 <- dual ctx' cmap'' arg
          return $ DualResult
              (EBuilder ctx1 (Let lhs adjoint . f1))
              stores1  -- don't need to store this node
              cmap1

    Pair lab arg1 arg2 -> do
        let (adjoint, cmap') = collectAdjointCMap cmap (Local lab) ctx
        (Exists lhs, envlabs) <- genSingleIds (labelType lab)
        let ctx' = ctxPush lhs (fmapLabel D lab) envlabs ctx
            cmap'' = addContrib (Local (elabelOf arg1))
                                (\ctx2 ->
                                    let TupRpair labs _ = resolveEnvLabs ctx2 (findAdjointBMap ctx2 lab)
                                    in evars labs)
                   . addContrib (Local (elabelOf arg2))
                                (\ctx2 ->
                                    let TupRpair _ labs = resolveEnvLabs ctx2 (findAdjointBMap ctx2 lab)
                                    in evars labs)
                   $ cmap'
        traceM ("!dual Pair[" ++ showDLabel lab ++ "]: envlabs = " ++ showTupR showDLabel envlabs)
        DualResult (EBuilder ctx1 f1) stores1 cmap1 <- dual ctx' cmap'' arg1
        DualResult (EBuilder ctx2 f2) stores2 cmap2 <- dual ctx1 cmap1 arg2
        return $ DualResult
            (EBuilder ctx2 (Let lhs adjoint . f1 . f2))
            (stores1 ++ stores2)  -- don't need to store this node
            cmap2

    Get lab tidx arg -> do
        let (adjoint, cmap') = collectAdjointCMap cmap (Local lab) ctx
        (Exists lhs, envlabs) <- genSingleIds (labelType lab)
        let ctx' = ctxPush lhs (fmapLabel D lab) envlabs ctx
            cmap'' = addContrib (Local (elabelOf arg))
                                (\ctx2 ->
                                    oneHotTup (etypeOf arg) tidx (evars (resolveEnvLabs ctx2 (findAdjointBMap ctx2 lab))))
                                cmap'
        traceM ("!dual Get[" ++ showDLabel lab ++ "]: envlabs = " ++ showTupR showDLabel envlabs)
        DualResult (EBuilder ctx1 f1) stores1 cmap1 <- dual ctx' cmap'' arg
        return $ DualResult
            (EBuilder ctx1 (Let lhs adjoint . f1))
            stores1  -- don't need to store this node
            cmap1

    Var lab _ (PartLabel referLab referPart) -> do
        let (adjoint, cmap') = collectAdjointCMap cmap (Local (tupleLabel lab)) ctx
        (Exists lhs, envlabs) <- genSingleIds (TupRsingle (labelType lab))
        let ctx' = ctxPush lhs (fmapLabel D (tupleLabel lab)) envlabs ctx
            cmap'' = addContrib (Local referLab)
                                (\ctx2 ->
                                    let adjoint' = evars (resolveEnvLabs ctx2 (findAdjointBMap ctx2 lab))
                                    in oneHotTup (labelType referLab) referPart adjoint')
                                cmap'
        traceM ("!dual Var[" ++ showDLabel lab ++ " -> " ++ tiPrefixExp referPart ++ " " ++ showDLabel referLab ++ "]: envlabs = " ++ showTupR showDLabel envlabs)
        return $ DualResult
            (EBuilder ctx' (Let lhs adjoint))
            [Some (tupleLabel lab)]  -- Store this node! We need to keep the contribution around.
            cmap''

    Arg lab argsty tidx -> do
        let (adjoint, cmap') = collectAdjointCMap cmap (Local (tupleLabel lab)) ctx
        (Exists lhs, envlabs) <- genSingleIds (TupRsingle (labelType lab))
        let ctx' = ctxPush lhs (fmapLabel D (tupleLabel lab)) envlabs ctx
            cmap'' = addContrib (Argument argsty)
                                (\ctx2 ->
                                    let adjoint' = evars (resolveEnvLabs ctx2 (findAdjointBMap ctx2 lab))
                                    in oneHotTup argsty tidx adjoint')
                                cmap'
        traceM ("!dual Arg[" ++ showDLabel lab ++ " -> " ++ tiPrefixExp tidx ++ " A]: envlabs = " ++ showTupR showDLabel envlabs)
        return $ DualResult
            (EBuilder ctx' (Let lhs adjoint))
            [Some (tupleLabel lab)]  -- Store this node! We need to keep the contribution around.
            cmap''

    Cond lab arg1 argT argE -> do
        let (adjoint, cmap') = collectAdjointCMap cmap (Local lab) ctx
        (Exists envlhs, envlabs) <- genSingleIds (labelType lab)
        let ctx' = ctxPush envlhs (fmapLabel D lab) envlabs ctx
            cmap'' = addContrib (Local (elabelOf argT))
                                (\ctx2 -> evars (resolveEnvLabs ctx2 envlabs))
                   . addContrib (Local (elabelOf argE))
                                (\ctx2 -> evars (resolveEnvLabs ctx2 envlabs))
                   $ cmap'
        traceM ("!dual Cond[" ++ showDLabel lab ++ "]: envlabs = " ++ showTupR showDLabel envlabs)
        DualResult (EBuilder ctxT fT) storesT cmapT <- dual ctx' cmap'' argT
        DualResult (EBuilder ctxE fE) storesE cmapE <- dual ctx' cmapT argE
        Some' tmplabsT <- returnSome (tuplify (sortUniq (concat [enumerateTupR (findAdjointBMap ctxT l) | Some l <- storesT])))
        Some' tmplabsE <- returnSome (tuplify (sortUniq (concat [enumerateTupR (findAdjointBMap ctxE l) | Some l <- storesE])))
        let tmptyT = fmapTupR labelType tmplabsT
            tmptyE = fmapTupR labelType tmplabsE
            branchty = TupRpair tmptyT tmptyE
        LetBoundVars lhsT _ <- return (lhsCopy tmptyT)
        LetBoundVars lhsE _ <- return (lhsCopy tmptyE)
        let branchlhs = LeftHandSidePair lhsT lhsE
            Context labelenv bindmap = ctx'
            labelenv' = labelenv & lpushLabTup lhsT tmplabsT
                                 & lpushLabTup lhsE tmplabsE
            isInStores st k _ = case k of Argument _ -> True
                                          Local l -> Some l `elem` map (mapSome (fmapLabel D)) st
            bindmap' = dmapDisjointUnions
                          [bindmap
                          ,DMap.filterWithKey (isInStores storesT) (let Context _ bm = ctxT in bm)
                          ,DMap.filterWithKey (isInStores storesE) (let Context _ bm = ctxE in bm)]
        traceM (unlines ["!dual RE Cond[" ++ showDLabel lab ++ "]:"
                        ,"  tmplabsT = " ++ showTupR showDLabel tmplabsT
                        ,"  tmplabsE = " ++ showTupR showDLabel tmplabsE
                        ,"  bmT = " ++ showBindmap (let Context _ bm = ctxT in bm DMap.\\ bindmap)
                        ,"  bmE = " ++ showBindmap (let Context _ bm = ctxE in bm DMap.\\ bindmap)
                        ,"  storesT = " ++ show storesT
                        ,"  storesE = " ++ show storesE
                        ,"  labelenv' = " ++ showLabelenv labelenv'
                        ,"  bindmap' = " ++ showBindmap bindmap'
                        ])
        return $ DualResult
            (EBuilder (Context labelenv' bindmap')
                      (Let envlhs adjoint .
                       Let branchlhs
                           (Cond (nilLabel branchty)
                                 (evars (resolveEnvLabs ctx' (findPrimalBMap ctx' (elabelOf arg1))))
                                 (fT (smartPair
                                         (evars (resolveEnvLabs ctxT tmplabsT))
                                         (zeroForType tmptyE)))
                                 (fE (smartPair
                                         (zeroForType tmptyT)
                                         (evars (resolveEnvLabs ctxE tmplabsE)))))))
            (storesT ++ storesE)  -- don't need to store this node
            cmapE

    Let _ arg1 arg2 -> do
        -- The contribution is stored in the cmap under the label of the body,
        -- so it will be communicated without work here in Let.
        DualResult (EBuilder ctx2 f2) stores2 cmap2 <- dual ctx cmap arg2
        -- The contribution for the RHS is already stored in the cmap, nothing
        -- more to do.
        DualResult (EBuilder ctx1 f1) stores1 cmap1 <- dual ctx2 cmap2 arg1
        return $ DualResult
            (EBuilder ctx1 (f2 . f1))
            (stores1 ++ stores2)  -- nothing to store
            cmap1

    -- These primitives all have none or only integral arguments. Since
    -- integral nodes always have adjoint zero, we don't even need to traverse
    -- those subtrees. This just means some contribution list may be empty,
    -- which is okay.
    -- For these nodes we also don't have to keep the adjoint around outside
    -- condition branches.
    Const _ _       -> return (emptyDual ctx cmap)
    PrimConst _ _   -> return (emptyDual ctx cmap)
    Nil _           -> return (emptyDual ctx cmap)
    Shape _ _       -> return (emptyDual ctx cmap)
    ShapeSize _ _ _ -> return (emptyDual ctx cmap)
    Undef _         -> return (emptyDual ctx cmap)
    FreeVar _ _     -> return (emptyDual ctx cmap)
    -- However, for Index we must store the adjoint for the index adjoint information tuple.
    Index lab _ _ _ -> simpleDual ctx cmap lab
  where
    emptyDual :: EContext Int env
              -> DMap (CMapKey ScalarType Int) (AdjList aenv Int alab args tenv)  -- Contribution map
              -> DualResult env aenv alab args tenv
    emptyDual ctx' cmap' = DualResult (EBuilder ctx' id) [] cmap'

    simpleDual :: (Show alab, IsTupleType ScalarType s)
               => EContext Int env
               -> DMap (CMapKey ScalarType Int) (AdjList aenv Int alab args tenv)
               -> DLabel NodeLabel s Int t
               -> IdGen (DualResult env aenv alab args tenv)
    simpleDual ctx' cmap' lab = do
        let (adjoint, cmap'') = collectAdjointCMap cmap' (Local (tupleLabel lab)) ctx'
        (Exists lhs, envlabs) <- genSingleIds (etypeOf adjoint)
        return $
            DualResult (EBuilder (ctxPush lhs (fmapLabel D (tupleLabel lab)) envlabs ctx')
                                 (Let lhs adjoint))
                       [Some (tupleLabel lab)]
                       cmap''

-- Make sure the expressions given are cheap to duplicate, i.e. just variable
-- references.
primAppDerivative :: TypeR t
                  -> A.PrimFun (t -> t')
                  -> OpenExp env aenv () alab args tenv t   -- primal value of argument
                  -> OpenExp env aenv () alab args tenv t'  -- primal value of result
                  -> OpenExp env aenv () alab args tenv t'  -- adjoint of result
                  -> OpenExp env aenv () alab args tenv t   -- adjoint of argument
primAppDerivative argty oper parg pres adjoint = case oper of
    A.PrimAdd _ ->
        Pair (nilLabel argty) adjoint adjoint
    A.PrimSub nty ->
        Pair (nilLabel argty) adjoint (smartNeg nty adjoint)
    A.PrimMul nty ->
        Pair (nilLabel argty) (smartMul nty (smartSnd parg) adjoint)
                           (smartMul nty (smartFst parg) adjoint)
    A.PrimFDiv fty ->
        -- x / y  ->  (adjoint / x, adjoint * (-x / (y*y)))
        let nty = FloatingNumType fty
        in Pair (nilLabel argty) (smartFDiv fty adjoint (smartSnd parg))
                              (smartMul nty adjoint
                                  (smartFDiv fty (smartNeg nty (smartFst parg))
                                                 (smartMul nty (smartSnd parg) (smartSnd parg))))
    A.PrimMax sgty ->
        Cond (nilLabel argty)
             (smartGt sgty (smartFst parg) (smartSnd parg))
             (smartPair adjoint (zeroForType sgty))
             (smartPair (zeroForType sgty) adjoint)
    A.PrimNeg nty ->
        smartNeg nty adjoint
    A.PrimLog fty ->
        smartFDiv fty adjoint parg
    A.PrimSqrt fty ->
        -- sqrt x  ->  adjoint / (2 * sqrt x) = adjoint / (2 * primalresult)
        let nty = FloatingNumType fty
        in smartFDiv fty adjoint (smartMul nty (zeroForType' 2 fty) pres)
    A.PrimExpFloating fty ->
        -- exp x  ->  adjoint * exp x = adjoint * primalresult
        smartMul (FloatingNumType fty) adjoint pres
    A.PrimTanh fty ->
        -- tanh x  ->  adjoint * (1 - tanh x * tanh x) = adjoint * (1 - primalresult * primalresult)
        let nty = FloatingNumType fty
        in smartMul nty adjoint (smartSub nty (zeroForType' 1 fty) (smartMul nty pres pres))
    A.PrimSin fty ->
        smartMul (FloatingNumType fty) adjoint (PrimApp (nilLabel argty) (A.PrimCos fty) parg)
    A.PrimCos fty ->
        let nty = FloatingNumType fty
        in smartMul nty adjoint (smartNeg nty (PrimApp (nilLabel argty) (A.PrimSin fty) parg))
    _ -> error $ "Derivative for expression primitive " ++ showPrimFun oper ++ " not implemented"

isIntegralType :: TypeR t -> Bool
isIntegralType TupRunit = True
isIntegralType (TupRpair t1 t2) = isIntegralType t1 && isIntegralType t2
isIntegralType (TupRsingle (SingleScalarType (NumSingleType (IntegralNumType _)))) = True
isIntegralType _ = False


-- Utility functions
-- -----------------

-- Collect adjoint from the contribution map, and returns the map with this label's entries removed.
collectAdjointCMap :: Show alab
                   => DMap (CMapKey ScalarType Int) (AdjList aenv Int alab args tenv)
                   -> CMapKey ScalarType Int t
                   -> EContext Int env
                   -> (OpenExp env aenv () alab args tenv t
                      ,DMap (CMapKey ScalarType Int) (AdjList aenv Int alab args tenv))
collectAdjointCMap contribmap key ctx =
    case DMap.lookup key contribmap of
        Just (AdjList listgen) ->
            let adj = expSum (cmapKeyType key) (listgen ctx)
            in trace ("\x1B[1mcmap collect: " ++ showCMapKey showDLabel key ++ " ==> " ++ show adj ++ "\x1B[0m")
               (adj, DMap.delete key contribmap)
        Nothing -> -- if there are no contributions, well, the adjoint is an empty sum (i.e. zero)
                   let res = expSum (cmapKeyType key) []
                   in trace ("\x1B[1mcmap collect: " ++ showCMapKey showDLabel key ++ " ==> {} ==> " ++ show res ++ "\x1B[0m")
                      (res, contribmap)

addContrib :: CMapKey ScalarType Int t
           -> (forall env. EContext Int env -> OpenExp env aenv () alab args tenv t)
           -> DMap (CMapKey ScalarType Int) (AdjList aenv Int alab args tenv)
           -> DMap (CMapKey ScalarType Int) (AdjList aenv Int alab args tenv)
addContrib key gen = DMap.insertWith (<>) key (AdjList (pure . gen))

oneHotTup :: TypeR t -> TupleIdx t t' -> OpenExp env aenv () alab args tenv t' -> OpenExp env aenv () alab args tenv t
oneHotTup _ TIHere ex = ex
oneHotTup ty@(TupRpair ty1 ty2) (TILeft ti) ex = Pair (nilLabel ty) (oneHotTup ty1 ti ex) (zeroForType ty2)
oneHotTup ty@(TupRpair ty1 ty2) (TIRight ti) ex = Pair (nilLabel ty) (zeroForType ty1) (oneHotTup ty2 ti ex)
oneHotTup _ _ _ = error "oneHotTup: impossible GADTs"

sortUniq :: Ord a => [a] -> [a]
sortUniq = uniq . sort
  where
    uniq :: Eq a => [a] -> [a]
    uniq (x:y:xs) | x == y = uniq (x:xs)
                  | otherwise = x : uniq (y:xs)
    uniq l = l

-- Data.Some (Some) is not like this because it's a newtype for performance.
data Some' f = forall a. Some' (f a)
gadtSome :: Some f -> Some' f
gadtSome (Some x) = Some' x
returnSome :: Applicative m => Some f -> m (Some' f)
returnSome = pure . gadtSome
