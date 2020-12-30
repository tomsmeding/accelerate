{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Accelerate.Trafo.AD.ADAcc (
  reverseADA, ReverseADResA(..)
) where

import Data.Function ((&))
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Map (DMap)
import Data.Dependent.Sum
import Data.List (sort)
import Data.Some (Some, pattern Some)
import Data.GADT.Compare (GCompare)

import qualified Data.Array.Accelerate.AST as A
import Data.Array.Accelerate.AST (ALeftHandSide)
import qualified Data.Array.Accelerate.AST.Environment as A
import Data.Array.Accelerate.AST.LeftHandSide
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.Error (HasCallStack)
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (ShapeR(..), shapeType)
import Data.Array.Accelerate.Representation.Slice
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.AD.Acc
import Data.Array.Accelerate.Trafo.AD.Additive
import Data.Array.Accelerate.Trafo.AD.ADExp (splitLambdaAD, labeliseExpA, labeliseFunA, inlineAvarLabels')
import qualified Data.Array.Accelerate.Trafo.AD.ADExp as ADExp
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Config
import Data.Array.Accelerate.Trafo.AD.Debug
import Data.Array.Accelerate.Trafo.AD.Exp
import qualified Data.Array.Accelerate.Trafo.AD.Heuristic as Heuristic
import Data.Array.Accelerate.Trafo.AD.Pretty
import Data.Array.Accelerate.Trafo.AD.Sink
import Data.Array.Accelerate.Trafo.AD.TupleZip
import Data.Array.Accelerate.Trafo.Substitution (rebuildLHS, weakenVars, weaken)
import Data.Array.Accelerate.Trafo.Var (declareVars, DeclareVars(..))


genId :: ArraysR t -> IdGen (ADLabelN Int t)
genId = genId'

genIdNodeSingle :: ArrayR t -> IdGen (ADLabelNS Int t)
genIdNodeSingle = genId'

genSingleId :: ArrayR t -> IdGen (ADLabel Int t)
genSingleId = genId'

genSingleIds :: ArraysR t -> IdGen (Exists (ALeftHandSide t aenv), TupR (ADLabel Int) t)
genSingleIds TupRunit = return (Exists (LeftHandSideWildcard TupRunit), TupRunit)
genSingleIds (TupRsingle ty) = (Exists (LeftHandSideSingle ty),) . TupRsingle <$> genSingleId ty
genSingleIds (TupRpair t1 t2) = do
    (Exists lhs1, ids1) <- genSingleIds t1
    (Exists lhs2, ids2) <- genSingleIds t2
    return (Exists (LeftHandSidePair lhs1 lhs2), TupRpair ids1 ids2)


-- Assumes the expression does not contain Arg
generaliseArgs :: HasCallStack => OpenAcc aenv lab alab args t -> OpenAcc aenv lab alab args' t
generaliseArgs (Aconst lab x) = Aconst lab x
generaliseArgs (Apair lab e1 e2) = Apair lab (generaliseArgs e1) (generaliseArgs e2)
generaliseArgs (Anil lab) = Anil lab
generaliseArgs (Acond lab e1 e2 e3) = Acond lab e1 (generaliseArgs e2) (generaliseArgs e3)
generaliseArgs (Map lab f e) = Map lab f (generaliseArgs e)
generaliseArgs (ZipWith lab f e1 e2) = ZipWith lab f (generaliseArgs e1) (generaliseArgs e2)
generaliseArgs (Fold lab f me0 a) = Fold lab f me0 (generaliseArgs a)
generaliseArgs (Scan lab dir f me0 a) = Scan lab dir f me0 (generaliseArgs a)
generaliseArgs (Scan' lab dir f e0 a) = Scan' lab dir f e0 (generaliseArgs a)
generaliseArgs (Backpermute lab dim f e) = Backpermute lab dim f (generaliseArgs e)
generaliseArgs (Replicate lab sht she e) = Replicate lab sht she (generaliseArgs e)
generaliseArgs (Slice lab sht e she) = Slice lab sht (generaliseArgs e) she
generaliseArgs (Reduce sht she f e) = Reduce sht she f (generaliseArgs e)
generaliseArgs (Reshape lab she e) = Reshape lab she (generaliseArgs e)
generaliseArgs (Sum lab a) = Sum lab (generaliseArgs a)
generaliseArgs (Generate lab she f) = Generate lab she f
generaliseArgs (Permute lab cf e1 pf e2) = Permute lab cf (generaliseArgs e1) pf (generaliseArgs e2)
generaliseArgs (Aget lab path ex) = Aget lab path (generaliseArgs ex)
generaliseArgs (Alet lhs rhs ex) = Alet lhs (generaliseArgs rhs) (generaliseArgs ex)
generaliseArgs (Avar lab v referLab) = Avar lab v referLab
generaliseArgs (Aarg _ _ _) = error "generaliseArgs: Arg found"

data ReverseADResA alab tenv t =
    forall aenv.
        ReverseADResA (A.ALeftHandSide t () aenv)
                      (OpenAcc aenv () () () t)

reverseADA :: ALeftHandSide t () aenv
           -> OpenAcc aenv () () () (Array () Float)
           -> ReverseADResA alab tenv t
reverseADA paramlhs expr = evalIdGen $ do
    let paramty = lhsToTupR paramlhs
    (argsRHSlabel, expr') <-
        enlabelAccToplevel paramlhs (argumentTuple paramty) (generaliseArgs expr)

    traceM ("acc labeled:\n" ++ prettyPrint expr' ++ "\n")

    PrimalResult (ABuilder primalCtx primalBuilder) _ _ <-
        primal (Context LEmpty mempty) expr'

    let cmap0 = DMap.singleton (Local (alabelOf expr')) (AdjList (\_ ->
                  [Generate (nilLabel (ArrayR ShapeRz tupleType))
                            (Nil magicLabel)
                            (ELPlain (Lam (LeftHandSideWildcard tupleType)
                                          (Body (Const scalarLabel 1.0))))]))
    DualResult (ABuilder dualCtx dualBuilder) _ dualCMap <- dual primalCtx cmap0 expr'
    let argpvars = resolveEnvLabs dualCtx (findPrimalBMap dualCtx argsRHSlabel)
        (gradient, _) = collectAdjointCMap dualCMap (Argument paramty) argpvars dualCtx

    return $ ReverseADResA
        paramlhs
        (realiseArgs paramlhs
            (primalBuilder
             . dualBuilder
             $ gradient))

argumentTuple :: ArraysR args -> OpenAcc aenv () () args args
argumentTuple argsty = untupleAccs
                           (zipWithTupR (\ty@ArrayR{} tidx -> Aarg (nilLabel ty) argsty tidx)
                                        argsty (tupleIndices argsty))

-- Produces an expression that can be put under a LHS that binds exactly the
-- 'args' of the original expression.
realiseArgs :: forall args argsenv res.
               ALeftHandSide args () argsenv
            -> OpenAcc () () () args res
            -> OpenAcc argsenv () () () res
realiseArgs paramlhs = \expr -> go A.weakenId (A.weakenWithLHS paramlhs) expr
  where
    go :: argsenv A.:> aenv' -> aenv A.:> aenv' -> OpenAcc aenv () () args t -> OpenAcc aenv' () () () t
    go argWeaken varWeaken expr = case expr of
        Aconst lab x -> Aconst lab x
        Apair lab e1 e2 -> Apair lab (go argWeaken varWeaken e1) (go argWeaken varWeaken e2)
        Anil lab -> Anil lab
        Acond lab e1 e2 e3 -> Acond lab (sinkExpAenv varWeaken e1) (go argWeaken varWeaken e2) (go argWeaken varWeaken e3)
        Map lab f e -> Map lab (fmapPlain (sinkFunAenv varWeaken) f) (go argWeaken varWeaken e)
        ZipWith lab f e1 e2 -> ZipWith lab (fmapPlain (sinkFunAenv varWeaken) f) (go argWeaken varWeaken e1) (go argWeaken varWeaken e2)
        Fold lab f me0 e -> Fold lab (sinkFunAenv varWeaken f) (sinkExpAenv varWeaken <$> me0) (go argWeaken varWeaken e)
        Scan lab dir f me0 e -> Scan lab dir (sinkFunAenv varWeaken f) (sinkExpAenv varWeaken <$> me0) (go argWeaken varWeaken e)
        Scan' lab dir f e0 e -> Scan' lab dir (sinkFunAenv varWeaken f) (sinkExpAenv varWeaken e0) (go argWeaken varWeaken e)
        Backpermute lab dim f e -> Backpermute lab (sinkExpAenv varWeaken dim) (sinkFunAenv varWeaken f) (go argWeaken varWeaken e)
        Permute lab cf def pf e -> Permute lab (sinkFunAenv varWeaken cf) (go argWeaken varWeaken def) (sinkFunAenv varWeaken pf) (go argWeaken varWeaken e)
        Sum lab e -> Sum lab (go argWeaken varWeaken e)
        Generate lab she f -> Generate lab (sinkExpAenv varWeaken she) (fmapPlain (sinkFunAenv varWeaken) f)
        Replicate lab slt sle e -> Replicate lab slt (sinkExpAenv varWeaken sle) (go argWeaken varWeaken e)
        Slice lab slt e sle -> Slice lab slt (go argWeaken varWeaken e) (sinkExpAenv varWeaken sle)
        Reduce lab slt f e -> Reduce lab slt (sinkFunAenv varWeaken f) (go argWeaken varWeaken e)
        Reshape lab she e -> Reshape lab (sinkExpAenv varWeaken she) (go argWeaken varWeaken e)
        Aget lab tidx ex -> Aget lab tidx (go argWeaken varWeaken ex)
        Alet lhs rhs ex
          | Exists lhs' <- rebuildLHS lhs ->
              Alet lhs' (go argWeaken varWeaken rhs)
                  (go (A.weakenWithLHS lhs' A..> argWeaken) (A.sinkWithLHS lhs lhs' varWeaken) ex)
        Avar lab (A.Var ty idx) referLab -> Avar lab (A.Var ty (varWeaken A.>:> idx)) referLab
        Aarg lab _ tidx ->
            case indexIntoLHS paramlhs tidx of
              Just idx -> let nillab = nilLabel (labelType lab)
                          in Avar nillab (A.Var (labelType lab) (argWeaken A.>:> idx))
                                  (PartLabel (tupleLabel nillab) TIHere)
              -- If an argument component is ignored in the top-level LHS, it
              -- is by construction never used. Thus, we only need to generate
              -- an arbitrary valid value of the type.
              Nothing -> emptiesForType (TupRsingle (labelType lab))

-- Enlabels a program of the form 'Alet lhs rhs body', where 'rhs' has type
-- 'args' and the Alet has been broken out into its three components. In
-- addition to the full program, returns the label of the enlabeled rhs.
enlabelAccToplevel :: ALeftHandSide args () aenv
                   -> OpenAcc () () () args args
                   -> OpenAcc aenv () () args t
                   -> IdGen (ADLabelN Int args, OpenAcc () () Int args t)
enlabelAccToplevel lhs argsRHS body = do
    argsRHS' <- enlabelAcc TEmpty argsRHS
    let lab = alabelOf argsRHS'
    body' <- enlabelAcc (lpushLHS_parts TEmpty lab TIHere lhs) body
    return (lab, Alet lhs argsRHS' body')

enlabelAcc :: TagVal (AAnyPartLabelN Int) aenv -> OpenAcc aenv () () args t -> IdGen (OpenAcc aenv () Int args t)
enlabelAcc aenv prog = case prog of
    Aconst lab x -> Aconst <$> genLabNS lab <*> return x
    Apair lab a1 a2 -> Apair <$> genLabN lab <*> enlabelAcc aenv a1 <*> enlabelAcc aenv a2
    Anil lab -> Anil <$> genLabN lab
    Acond lab ex a1 a2 -> Acond <$> genLabN lab <*> return (snd (labeliseExpA aenv ex)) <*> enlabelAcc aenv a1 <*> enlabelAcc aenv a2
    Map lab (ELPlain fun) a1 -> Map <$> genLabNS lab <*> splitLambda (atypeOf1 prog) aenv fun <*> enlabelAcc aenv a1
    ZipWith lab (ELPlain fun) a1 a2 -> ZipWith <$> genLabNS lab <*> splitLambda (atypeOf1 prog) aenv fun <*> enlabelAcc aenv a1 <*> enlabelAcc aenv a2
    Fold lab fun mex a1 -> Fold <$> genLabNS lab <*> return (snd (labeliseFunA aenv fun)) <*> return (snd . labeliseExpA aenv <$> mex) <*> enlabelAcc aenv a1
    Sum lab a1 -> Sum <$> genLabNS lab <*> enlabelAcc aenv a1
    Scan lab dir fun mex a1 -> Scan <$> genLabNS lab <*> return dir <*> return (snd (labeliseFunA aenv fun)) <*> return (snd . labeliseExpA aenv <$> mex) <*> enlabelAcc aenv a1
    Scan' lab dir fun mex a1 -> Scan' <$> genLabN lab <*> return dir <*> return (snd (labeliseFunA aenv fun)) <*> return (snd (labeliseExpA aenv mex)) <*> enlabelAcc aenv a1
    Generate lab ex (ELPlain fun) -> Generate <$> genLabNS lab <*> return (snd (labeliseExpA aenv ex)) <*> splitLambda (atypeOf1 prog) aenv fun
    Replicate lab slix ex a1 -> Replicate <$> genLabNS lab <*> return slix <*> return (snd (labeliseExpA aenv ex)) <*> enlabelAcc aenv a1
    Slice lab slix a1 ex -> Slice <$> genLabNS lab <*> return slix <*> enlabelAcc aenv a1 <*> return (snd (labeliseExpA aenv ex))
    Reduce lab slix fun a1 -> Reduce <$> genLabNS lab <*> return slix <*> return (snd (labeliseFunA aenv fun)) <*> enlabelAcc aenv a1
    Reshape lab ex a1 -> Reshape <$> genLabNS lab <*> return (snd (labeliseExpA aenv ex)) <*> enlabelAcc aenv a1
    Backpermute lab ex fun a1 -> Backpermute <$> genLabNS lab <*> return (snd (labeliseExpA aenv ex)) <*> return (snd (labeliseFunA aenv fun)) <*> enlabelAcc aenv a1
    Permute lab fun1 a1 fun2 a2 -> Permute <$> genLabNS lab <*> return (snd (labeliseFunA aenv fun1)) <*> enlabelAcc aenv a1 <*> return (snd (labeliseFunA aenv fun2)) <*> enlabelAcc aenv a2
    Aget lab tidx a1 -> Aget <$> genLabN lab <*> return tidx <*> enlabelAcc aenv a1
    Alet lhs rhs a1 -> do
        rhs' <- enlabelAcc aenv rhs
        Alet lhs <$> return rhs' <*> enlabelAcc (lpushLHS_parts aenv (alabelOf rhs') TIHere lhs) a1
    Avar lab var@(A.Var _ idx) _
      | AnyPartLabel pl <- prjT idx aenv ->
          Avar <$> genLabNS lab <*> return var <*> return pl
    Aarg lab argsty tidx -> Aarg <$> genLabNS lab <*> return argsty <*> return tidx
    Map _ ELSplit{} _ -> error "Unexpected split Map in enlabelAcc"
    ZipWith _ ELSplit{} _ _ -> error "Unexpected split ZipWith in enlabelAcc"
    Generate _ _ ELSplit{} -> error "Unexpected split Generate in enlabelAcc"
  where
    genLabN :: ADLabelN () t -> IdGen (ADLabelN Int t)
    genLabN = genId . labelType

    genLabNS :: ADLabelNS () t -> IdGen (ADLabelNS Int t)
    genLabNS = genIdNodeSingle . labelType

    splitLambda :: ArrayR (Array sh e) -> TagVal (AAnyPartLabelN Int) aenv -> Fun aenv () () tenv (t1 -> t2) -> IdGen (ExpLambda1 aenv () Int tenv sh t1 t2)
    splitLambda (ArrayR sht _) aenv' fun
      | SomeSplitLambdaAD split@(SplitLambdaAD _ _ _ tmpty _ _) <- splitLambdaAD (snd (labeliseFunA aenv' fun))
      = ELSplit split <$> genIdNodeSingle (ArrayR sht tmpty)

data ABuilder aenv alab args =
    forall aenv'.
        ABuilder (AContext Int aenv')
                 (forall res. OpenAcc aenv' () () args res
                           -> OpenAcc aenv () () args res)

data PrimalResult aenv alab args t =
    PrimalResult (ABuilder aenv alab args)  -- Primal builder
                 [Some (ADLabel Int)]       -- To-store "set" (really list)
                 (TupR (ADLabel Int) t)     -- Env labels of the subtree root

primal :: AContext Int aenv
       -> OpenAcc progaenv () Int args t
       -> IdGen (PrimalResult aenv alab args t)
primal ctx = \case
    Aconst lab value ->
        simplePrimal TLNil ctx lab (\_ lab' _ ->
            Aconst lab' value)

    Apair lab arg1 arg2 ->
        simplePrimal (arg1 :@ arg2 :@ TLNil) ctx lab (\_ lab' (arg1' :@ arg2' :@ _) ->
            Apair lab' arg1' arg2')

    Anil lab ->
        simplePrimal TLNil ctx lab (\_ lab' _ ->
            Anil lab')

    Acond lab condexp argT argE -> do
        PrimalResult (ABuilder ctxT fT) storesT labsT <- primal ctx argT
        PrimalResult (ABuilder ctxE fE) storesE labsE <- primal ctx argE
        Some' tmplabsT <- returnSome (tuplify storesT)
        Some' tmplabsE <- returnSome (tuplify storesE)
        let tmptyT = fmapTupR labelType tmplabsT
            tmptyE = fmapTupR labelType tmplabsE
            branchty = TupRpair (labelType lab) (TupRpair tmptyT tmptyE)
        (Exists lhs, envlabs) <- genSingleIds (labelType lab)
        LetBoundVars lhsT _ <- return (lhsCopy tmptyT)
        LetBoundVars lhsE _ <- return (lhsCopy tmptyE)
        let Context labelenv bindmap = ctxPush lhs (fmapLabel P lab) envlabs ctx
            labelenv' = labelenv & lpushLabTup lhsT tmplabsT
                                 & lpushLabTup lhsE tmplabsE
            bindmap' = dmapDisjointUnions
                          [bindmap
                          ,let Context _ bm = ctxT in bm DMap.\\ bindmap
                          ,let Context _ bm = ctxE in bm DMap.\\ bindmap]
        return $ PrimalResult
            (ABuilder (Context labelenv' bindmap')
                      (Alet (LeftHandSidePair lhs (LeftHandSidePair lhsT lhsE))
                            (Acond (nilLabel branchty)
                                   (resolveAlabs ctx condexp)
                                   (fT (smartApair
                                           (avars (resolveEnvLabs ctxT labsT))
                                           (smartApair
                                               (avars (resolveEnvLabs ctxT tmplabsT))
                                               (emptiesForType tmptyE))))
                                   (fE (smartApair
                                           (avars (resolveEnvLabs ctxE labsE))
                                           (smartApair
                                               (emptiesForType tmptyT)
                                               (avars (resolveEnvLabs ctxE tmplabsE))))))))
            (concat [enumerateTupR envlabs
                    ,enumerateTupR tmplabsT
                    ,enumerateTupR tmplabsE])
            envlabs

    Generate lab shexp (ELSplit spl tmplab) -> do
        let resty@(ArrayR sht eltty) = labelType lab
            tmparrty@(ArrayR _ tmpty) = labelType tmplab
        envlab1 <- genSingleId resty
        envlab2 <- genSingleId tmparrty
        let lhsp = LeftHandSidePair (LeftHandSideSingle resty) (LeftHandSideSingle tmparrty)
            pairarrty = ArrayR sht (TupRpair eltty tmpty)
        return $ PrimalResult
            (ABuilder (ctx & ctxPushS (fmapLabel P lab) envlab1
                           & ctxPushS (fmapLabel P tmplab) envlab2)
                      (Alet lhsp (primalProducerFromLambda ctx spl
                                      (\lam -> Generate (nilLabel pairarrty)
                                                        (resolveAlabs ctx shexp)
                                                        (ELPlain lam)))))
            [Some envlab1, Some envlab2]
            (TupRsingle envlab1)

    Generate _ _ ELPlain{} -> error "Unexpected Generate ELPlain in primal"

    Map lab (ELSplit spl tmplab) arg -> do
        let resty@(ArrayR sht eltty) = labelType lab
            tmparrty@(ArrayR _ tmpty) = labelType tmplab
        PrimalResult (ABuilder ctx1 f1) stores1 arglabs1 <- primal ctx arg
        envlab1 <- genSingleId resty
        envlab2 <- genSingleId tmparrty
        let lhsp = LeftHandSidePair (LeftHandSideSingle resty) (LeftHandSideSingle tmparrty)
            pairarrty = ArrayR sht (TupRpair eltty tmpty)
        return $ PrimalResult
            (ABuilder (ctx1 & ctxPushS (fmapLabel P lab) envlab1
                            & ctxPushS (fmapLabel P tmplab) envlab2)
                      (f1 . Alet lhsp (primalProducerFromLambda ctx1 spl
                                           (\lam -> Map (nilLabel pairarrty)
                                                        (ELPlain lam)
                                                        (avars (resolveEnvLabs ctx1 arglabs1))))))
            (Some envlab1 : Some envlab2 : stores1)
            (TupRsingle envlab1)

    Map _ ELPlain{} _ -> error "Unexpected Map ELPlain in primal"

    ZipWith lab (ELSplit spl tmplab) arg1 arg2 -> do
        let resty@(ArrayR sht eltty) = labelType lab
            tmparrty@(ArrayR _ tmpty) = labelType tmplab
        PrimalResult (ABuilder ctx1 f1) stores1 arglabs1 <- primal ctx arg1
        PrimalResult (ABuilder ctx2 f2) stores2 arglabs2 <- primal ctx1 arg2
        envlab1 <- genSingleId resty
        envlab2 <- genSingleId tmparrty
        let lhsp = LeftHandSidePair (LeftHandSideSingle resty) (LeftHandSideSingle tmparrty)
            pairarrty = ArrayR sht (TupRpair eltty tmpty)
        return $ PrimalResult
            (ABuilder (ctx2 & ctxPushS (fmapLabel P lab) envlab1
                            & ctxPushS (fmapLabel P tmplab) envlab2)
                      (f1 . f2 . Alet lhsp (primalProducerFromLambda ctx2 spl
                                                (\lam -> ZipWith (nilLabel pairarrty)
                                                                 (ELPlain lam)
                                                                 (avars (resolveEnvLabs ctx2 arglabs1))
                                                                 (avars (resolveEnvLabs ctx2 arglabs2))))))
            (Some envlab1 : Some envlab2 : stores1 ++ stores2)
            (TupRsingle envlab1)

    ZipWith _ ELPlain{} _ _ -> error "Unexpected ZipWith ELPlain in primal"

    Fold lab combfun minitexp arg ->
        simplePrimal (arg :@ TLNil) ctx lab (\ctx' lab' (arg' :@ _) ->
            Fold lab' (resolveAlabsFun ctx' combfun) (resolveAlabs ctx' <$> minitexp) arg')

    Sum lab arg ->
        simplePrimal (arg :@ TLNil) ctx lab (\_ lab' (arg' :@ _) ->
            Sum lab' arg')

    Scan lab dir combfun minitexp arg ->
        simplePrimal (arg :@ TLNil) ctx lab (\ctx' lab' (arg' :@ _) ->
            Scan lab' dir (resolveAlabsFun ctx' combfun) (resolveAlabs ctx' <$> minitexp) arg')

    Scan' lab dir combfun initexp arg ->
        simplePrimal (arg :@ TLNil) ctx lab (\ctx' lab' (arg' :@ _) ->
            Scan' lab' dir (resolveAlabsFun ctx' combfun) (resolveAlabs ctx' initexp) arg')

    Replicate lab slix slexp arg ->
        simplePrimal (arg :@ TLNil) ctx lab (\ctx' lab' (arg' :@ _) ->
            Replicate lab' slix (resolveAlabs ctx' slexp) arg')

    Slice lab slix arg slexp ->
        simplePrimal (arg :@ TLNil) ctx lab (\ctx' lab' (arg' :@ _) ->
            Slice lab' slix arg' (resolveAlabs ctx' slexp))

    Reduce lab rspec combfun arg ->
        simplePrimal (arg :@ TLNil) ctx lab (\ctx' lab' (arg' :@ _) ->
            Reduce lab' rspec (resolveAlabsFun ctx' combfun) arg')

    Reshape lab shexp arg ->
        simplePrimal (arg :@ TLNil) ctx lab (\ctx' lab' (arg' :@ _) ->
            Reshape lab' (resolveAlabs ctx' shexp) arg')

    Backpermute lab shexp permfun arg ->
        simplePrimal (arg :@ TLNil) ctx lab (\ctx' lab' (arg' :@ _) ->
            Backpermute lab' (resolveAlabs ctx' shexp) (resolveAlabsFun ctx' permfun) arg')

    Permute lab combfun arg1 permfun arg2 ->
        simplePrimal (arg1 :@ arg2 :@ TLNil) ctx lab (\ctx' lab' (arg1' :@ arg2' :@ _) ->
            Permute lab' (resolveAlabsFun ctx' combfun) arg1' (resolveAlabsFun ctx' permfun) arg2')

    Aget lab tidx arg ->
        simplePrimal (arg :@ TLNil) ctx lab (\_ lab' (arg' :@ _) ->
            Aget lab' tidx arg')

    Alet _ rhs body -> do
        -- It's not a simplePrimal because it doesn't generate labels; in fact
        -- it's even simpler than simplePrimal.
        PrimalResult (ABuilder ctx1 f1) stores1 _ <- primal ctx rhs
        PrimalResult (ABuilder ctx2 f2) stores2 arglabs2 <- primal ctx1 body
        return $ PrimalResult
            (ABuilder ctx2 (f1 . f2))
            (stores1 ++ stores2)
            arglabs2

    Avar lab _ (PartLabel referLab referPart) ->
        simplePrimal TLNil ctx lab (\ctx' _ _ ->
            smartAvar (untupleA (pickTupR referPart (resolveEnvLabs ctx' (findPrimalBMap ctx' referLab)))))

    Aarg lab argsty tidx ->
        simplePrimal TLNil ctx lab (\_ lab' _ ->
            Aarg lab' argsty tidx)

-- If the lambda is small, the result program computes the primal twice, once for
-- the primal value, and once for the temporaries tuple. This second computation
-- will be fused into its usage in the dual phase.
-- If the lambda is not small, the result computes the primal once and shares it.
primalProducerFromLambda
    :: AContext Int aenv
    -> SplitLambdaAD t1 t2 () Int () tmp idxadj
    -> (Fun aenv () () () (t1 -> (t2, tmp))
           -> OpenAcc aenv () () args (Array sh (t2, tmp)))
    -> OpenAcc aenv () () args (Array sh t2, Array sh tmp)
primalProducerFromLambda ctx (SplitLambdaAD primalLambda _ fvlabs _ _ _) buildf =
    let instantiatedLambda = primalLambda (lookupLambdaLabs ctx fvlabs)
        computePrimal = buildf instantiatedLambda
        pairarrty = atypeOf1 computePrimal
    in -- Note: the primal-transformed lambda is a lot larger than the input
       -- lambda, but it doesn't do more _work_ as far as functionSize is
       -- concerned. Thus this heuristic application is sensible.
       if Heuristic.functionSize instantiatedLambda < getConfigVar SmallFunSize
           then smartApair (mapFst computePrimal) (mapSnd computePrimal)
           else Alet (LeftHandSideSingle pairarrty) computePrimal
                     (let var = smartAvar (A.Var pairarrty ZeroIdx)
                      in smartApair (mapFst var) (mapSnd var))

simplePrimal :: (IsTupleType ArrayR s, GCompare s)
             => TypedList (OpenAcc progaenv () Int args) argts
             -> AContext Int aenv
             -> DLabel NodeLabel s Int t
             -> (forall aenv'.
                    AContext Int aenv'
                 -> DLabel nodeLabel s () t
                 -> TypedList (OpenAcc aenv' () () args) argts
                 -> OpenAcc aenv' () () args t)
             -> IdGen (PrimalResult aenv alab args t)
simplePrimal args ctx lab buildf =
    runArgs args ctx $ \(ABuilder ctx' f1) stores arglabss -> do
        (Exists lhs, envlabs) <- genSingleIds (toTupleType (labelType lab))
        let acc' = buildf ctx' (nilLabel (labelType lab))
                               (tlmap (avars . resolveEnvLabs ctx') arglabss)
        return $ PrimalResult
            (ABuilder (ctxPush lhs (fmapLabel P (tupleLabel lab)) envlabs ctx')
                      (f1 . Alet lhs acc'))
            (enumerateTupR envlabs ++ stores)
            envlabs
  where
    runArgs :: TypedList (OpenAcc progaenv () Int args) argts
            -> AContext Int aenv
            -> (   ABuilder aenv alab args
                -> [Some (ADLabel Int)]
                -> TypedList (TupR (ADLabel Int)) argts
                -> IdGen r)
            -> IdGen r
    runArgs TLNil ctx' cont = cont (ABuilder ctx' id) [] TLNil
    runArgs (arg :@ args') ctx' cont = do
        PrimalResult (ABuilder ctx1 f1) stores1 arglabs1 <- primal ctx' arg
        runArgs args' ctx1 $ \(ABuilder ctx2 f2) stores2 arglabss2 ->
            cont (ABuilder ctx2 (f1 . f2))
                 (stores1 ++ stores2)
                 (arglabs1 :@ arglabss2)

-- List of adjoints, collected for a particular label.
-- The exact variable references in the adjoints are dependent on the Let stack, thus the
-- environment (and the bindmap) is needed.
newtype AdjList lab alab args t =
    AdjList (forall aenv. AContext alab aenv -> [OpenAcc aenv lab () args t])

instance Semigroup (AdjList lab alab args t) where
    AdjList f1 <> AdjList f2 = AdjList (\ctx -> f1 ctx ++ f2 ctx)

showAdjList :: AContext alab aenv -> AdjList lab alab args t -> String
showAdjList ctx (AdjList f) =
    let len = length (f ctx)
    in "{\\_ -> [" ++ show len ++ " item" ++ (if len == 1 then "" else "s") ++ "]}"

showCMapA :: AContext alab aenv -> DMap (CMapKey ArrayR Int) (AdjList () alab args) -> String
showCMapA ctx = showCMap' (showAdjList ctx)

data DualResult aenv alab args =
    DualResult (ABuilder aenv alab args)      -- Dual builder
               [Some (ADLabel Int)]           -- To-store "set" (really list): Pair (labelToStore) (shapeReference)
               (DMap (CMapKey ArrayR Int)     -- Contribution map (only for let-bound things and array indexing)
                     (AdjList () alab args))

dual :: AContext Int aenv
     -> DMap (CMapKey ArrayR Int) (AdjList () Int args)  -- Contribution map
     -> OpenAcc progaenv () Int args t
     -> IdGen (DualResult aenv Int args)
dual ctx cmap = \case
    Aconst lab _ ->
        return (DualResult (ABuilder ctx id) [] (DMap.delete (Local (tupleLabel' lab)) cmap))

    Apair lab arg1 arg2 -> do
        let (adjoint, cmap') = collectAdjointCMap cmap (Local lab) (resolveEnvLabs ctx (findPrimalBMap ctx lab)) ctx
        (Exists lhs, envlabs) <- genSingleIds (labelType lab)
        let ctx' = ctxPush lhs (fmapLabel D lab) envlabs ctx
            cmap'' = addContrib (Local (alabelOf arg1))
                                (\ctx2 ->
                                    let TupRpair labs _ = resolveEnvLabs ctx2 (findAdjointBMap ctx2 lab)
                                    in avars labs)
                   . addContrib (Local (alabelOf arg2))
                                (\ctx2 ->
                                    let TupRpair _ labs = resolveEnvLabs ctx2 (findAdjointBMap ctx2 lab)
                                    in avars labs)
                   $ cmap'
        traceM ("!dual Apair[" ++ showDLabel lab ++ "]: envlabs = " ++ showTupR showDLabel envlabs)
        DualResult (ABuilder ctx1 f1) stores1 cmap1 <- dual ctx' cmap'' arg1
        DualResult (ABuilder ctx2 f2) stores2 cmap2 <- dual ctx1 cmap1 arg2
        return $ DualResult
            (ABuilder ctx2 (Alet lhs adjoint . f1 . f2))
            (stores1 ++ stores2)  -- don't need to store this node
            cmap2

    Anil lab ->
        return (DualResult (ABuilder ctx id) [] (DMap.delete (Local lab) cmap))

    Acond lab condexp argT argE -> do
        let (adjoint, cmap') = collectAdjointCMap cmap (Local lab) (resolveEnvLabs ctx (findPrimalBMap ctx lab)) ctx
        (Exists envlhs, envlabs) <- genSingleIds (labelType lab)
        let ctx' = ctxPush envlhs (fmapLabel D lab) envlabs ctx
            cmap'' = addContrib (Local (alabelOf argT))
                                (\ctx2 -> avars (resolveEnvLabs ctx2 envlabs))
                   . addContrib (Local (alabelOf argE))
                                (\ctx2 -> avars (resolveEnvLabs ctx2 envlabs))
                   $ cmap'
        traceM ("!dual Acond[" ++ showDLabel lab ++ "]: envlabs = " ++ showTupR showDLabel envlabs)
        DualResult (ABuilder ctxT fT) storesT cmapT <- dual ctx' cmap'' argT
        DualResult (ABuilder ctxE fE) storesE cmapE <- dual ctx' cmapT argE
        Some' tmplabsT <- returnSome (tuplify (sortUniq storesT))
        Some' tmplabsE <- returnSome (tuplify (sortUniq storesE))
        let tmptyT = fmapTupR labelType tmplabsT
            tmptyE = fmapTupR labelType tmplabsE
            branchty = TupRpair tmptyT tmptyE
        LetBoundVars lhsT _ <- return (lhsCopy tmptyT)
        LetBoundVars lhsE _ <- return (lhsCopy tmptyE)
        let branchlhs = LeftHandSidePair lhsT lhsE
            Context labelenv bindmap = ctx'
            labelenv' = labelenv & lpushLabTup lhsT tmplabsT
                                 & lpushLabTup lhsE tmplabsE
            bindmap' = dmapDisjointUnions
                          [bindmap
                          ,let Context _ bm = ctxT in bm DMap.\\ bindmap
                          ,let Context _ bm = ctxE in bm DMap.\\ bindmap]
        traceM (unlines ["!dual Acond[" ++ showDLabel lab ++ "]:"
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
            (ABuilder (Context labelenv' bindmap')
                      (Alet envlhs adjoint .
                       Alet branchlhs
                            (Acond (nilLabel branchty)
                                   (resolveAlabs ctx' condexp)
                                   (fT (smartApair
                                           (avars (resolveEnvLabs ctxT tmplabsT))
                                           (emptiesForType tmptyE)))
                                   (fE (smartApair
                                           (emptiesForType tmptyT)
                                           (avars (resolveEnvLabs ctxE tmplabsE)))))))
            (storesT ++ storesE)  -- don't need to store this node
            cmapE

    -- The expression determining the shape has an integral result, and can thus be
    -- ignored here. All that we do is collect the indexing contributions.
    Generate lab _ (ELSplit (SplitLambdaAD _ dualLambda fvlabs _ idxadjty idxInsts) tmplab) -> do
        let (adjoint, cmap') = collectAdjointCMap cmap (Local (tupleLabel' lab)) (resolveEnvLabs ctx (findPrimalBMap ctx lab)) ctx
            sht = arrayRshape (labelType lab)
            iaarrty = ArrayR sht idxadjty
            pairarrty = ArrayR sht (TupRpair (shapeType sht) idxadjty)
        envlab0 <- genSingleId (labelType lab)
        envlab1 <- genSingleId iaarrty
        let ctx'1 = ctxPushS (fmapLabel D lab) envlab0 ctx
            ctx' = ctxPushSEnvOnly envlab1 ctx'1
        traceM (unlines ["!dual Generate[" ++ showDLabel lab ++ "]:"
                        ,"  envlab0 = " ++ showDLabel envlab0
                        ,"  envlab1 = " ++ showDLabel envlab1
                        ,"  stores = " ++ show [Some envlab1]
                        ,"  out cmap = " ++ showCMapA ctx' (cmap' `unionCMap` indexingContributions envlab1 idxInsts)
                        ])
        return $ DualResult
            (ABuilder ctx' (Alet (LeftHandSideSingle (labelType lab)) adjoint .
                            Alet (LeftHandSideSingle iaarrty)
                                 (mapSnd
                                     (ZipWith (nilLabel pairarrty)
                                              (ELPlain (dualLambda (lookupLambdaLabs ctx'1 fvlabs)))
                                              (smartAvar (A.Var (labelType lab) ZeroIdx))
                                              (avars (resolveEnvLabs ctx'1 (findPrimalBMap ctx'1 tmplab)))))))
            [Some envlab1]  -- should store the IAI array for the indexing contributions
            (cmap' `unionCMap` indexingContributions envlab1 idxInsts)

    Generate _ _ ELPlain{} -> error "dual: unexpected Generate ELPlain"

    Map lab (ELSplit (SplitLambdaAD _ dualLambda fvlabs _ idxadjty idxInsts) tmplab) arg1 -> do
        let (adjoint, cmap') = collectAdjointCMap cmap (Local (tupleLabel' lab)) (resolveEnvLabs ctx (findPrimalBMap ctx lab)) ctx
            ArrayR sht argeltty = atypeOf1 arg1
            iaarrty = ArrayR sht idxadjty
            pairarrty = ArrayR sht (TupRpair argeltty idxadjty)
        envlab0 <- genSingleId (labelType lab)
        envlab1 <- genSingleId (atypeOf1 arg1)
        envlab2 <- genSingleId iaarrty
        let ctx'1 = ctxPushS (fmapLabel D lab) envlab0 ctx
            ctx' = ctx'1 & ctxPushSEnvOnly envlab1
                         & ctxPushSEnvOnly envlab2
            cmap'' = addContrib (Local (alabelOf arg1))
                                (\ctx2 -> smartAvar (resolveEnvLab ctx2 envlab1))
                                cmap'
        DualResult (ABuilder ctx1 f1) stores1 cmap1 <- dual ctx' cmap'' arg1
        traceM (unlines ["!dual Map[" ++ showDLabel lab ++ "]:"
                        ,"  envlab0 = " ++ showDLabel envlab0
                        ,"  envlab1 = " ++ showDLabel envlab1 ++ "  (adjoint of node " ++ showDLabel (alabelOf arg1) ++ ")"
                        ,"  envlab2 = " ++ showDLabel envlab2
                        ,"  stores = " ++ show stores1
                        ,"  out cmap = " ++ showCMapA ctx1 (cmap1 `unionCMap` indexingContributions envlab2 idxInsts)
                        ])
        return $ DualResult
            (ABuilder ctx1 (Alet (LeftHandSideSingle (labelType lab)) adjoint .
                            Alet (LeftHandSidePair (LeftHandSideSingle (atypeOf1 arg1))
                                                   (LeftHandSideSingle iaarrty))
                                 (Alet (LeftHandSideSingle pairarrty)
                                       (ZipWith (nilLabel pairarrty)
                                                (ELPlain (dualLambda (lookupLambdaLabs ctx'1 fvlabs)))
                                                (smartAvar (A.Var (labelType lab) ZeroIdx))
                                                (avars (resolveEnvLabs ctx'1 (findPrimalBMap ctx'1 tmplab))))
                                       (let var = smartAvar (A.Var pairarrty ZeroIdx)
                                        in smartApair (mapFst var) (mapSnd var)))
                            . f1))
            (Some envlab2 : stores1)  -- should store the IAI array for the indexing contributions
            (cmap1 `unionCMap` indexingContributions envlab2 idxInsts)

    Map _ ELPlain{} _ -> error "dual: unexpected Map ELPlain"

    ZipWith lab (ELSplit (SplitLambdaAD _ dualLambda fvlabs _ idxadjty idxInsts) tmplab) arg1 arg2 -> do
        let (adjoint, cmap') = collectAdjointCMap cmap (Local (tupleLabel' lab)) (resolveEnvLabs ctx (findPrimalBMap ctx lab)) ctx
            ArrayR sht arg1eltty = atypeOf1 arg1
            ArrayR _ arg2eltty = atypeOf1 arg2
            iaarrty = ArrayR sht idxadjty
            pairarrty = ArrayR sht (TupRpair (TupRpair arg1eltty arg2eltty) idxadjty)
        envlab0 <- genSingleId (labelType lab)
        envlab1 <- genSingleId (atypeOf1 arg1)
        envlab2 <- genSingleId (atypeOf1 arg2)
        envlab3 <- genSingleId iaarrty
        let ctx'1 = ctxPushS (fmapLabel D lab) envlab0 ctx
            ctx' = ctx'1 & ctxPushSEnvOnly envlab1
                         & ctxPushSEnvOnly envlab2
                         & ctxPushSEnvOnly envlab3
            cmap'' = addContrib (Local (alabelOf arg1))
                                (\ctx2 -> smartAvar (resolveEnvLab ctx2 envlab1))
                   . addContrib (Local (alabelOf arg2))
                                (\ctx2 -> smartAvar (resolveEnvLab ctx2 envlab2))
                   $ cmap'
        DualResult (ABuilder ctx1 f1) stores1 cmap1 <- dual ctx' cmap'' arg1
        DualResult (ABuilder ctx2 f2) stores2 cmap2 <- dual ctx1 cmap1 arg2
        traceM (unlines ["!dual ZipWith[" ++ showDLabel lab ++ "]:"
                        ,"  envlab0 = " ++ showDLabel envlab0
                        ,"  envlab1 = " ++ showDLabel envlab1 ++ "  (adjoint of node " ++ showDLabel (alabelOf arg1) ++ ")"
                        ,"  envlab2 = " ++ showDLabel envlab2 ++ "  (adjoint of node " ++ showDLabel (alabelOf arg2) ++ ")"
                        ,"  envlab3 = " ++ showDLabel envlab3
                        ,"  stores = " ++ show stores1
                        ,"  out cmap = " ++ showCMapA ctx2 (cmap2 `unionCMap` indexingContributions envlab3 idxInsts)
                        ])
        return $ DualResult
            (ABuilder ctx2 (Alet (LeftHandSideSingle (labelType lab)) adjoint .
                            Alet (LeftHandSidePair (LeftHandSidePair (LeftHandSideSingle (atypeOf1 arg1))
                                                                     (LeftHandSideSingle (atypeOf1 arg2)))
                                                   (LeftHandSideSingle iaarrty))
                                 (Alet (LeftHandSideSingle pairarrty)
                                       (ZipWith (nilLabel pairarrty)
                                                (ELPlain (dualLambda (lookupLambdaLabs ctx'1 fvlabs)))
                                                (smartAvar (A.Var (labelType lab) ZeroIdx))
                                                (avars (resolveEnvLabs ctx'1 (findPrimalBMap ctx'1 tmplab))))
                                       (let var = smartAvar (A.Var pairarrty ZeroIdx)
                                        in smartApair (smartApair (mapGet (TILeft (TILeft TIHere)) var)
                                                                  (mapGet (TILeft (TIRight TIHere)) var))
                                                      (mapSnd var)))
                            . f1 . f2))
            (Some envlab3 : stores1 ++ stores2)  -- should store the IAI array for the indexing contributions
            (cmap2 `unionCMap` indexingContributions envlab3 idxInsts)

    ZipWith _ ELPlain{} _ _ -> error "dual: unexpected ZipWith ELPlain"

    Fold lab combfun (Just initexp) arg1
      | TupRsingle (SingleScalarType (NumSingleType (FloatingNumType TypeFloat))) <- arrayRtype (labelType lab)
      -> do
        MatchLamBody lambdalhs lambdabody <- return (matchLamBody combfun)
        if expHasIndex lambdabody then error "Array index operations in a Fold lambda not yet supported for AD" else return ()
        if expHasIndex initexp then error "Array index operations in a Fold initial expression not yet supported for AD" else return ()

        ReplicateOneMore onemoreSlix onemoreExpf <- return (replicateOneMore (arrayRshape (labelType lab)))

        let (adjoint, cmap') = collectAdjointCMap cmap (Local (tupleLabel' lab)) (resolveEnvLabs ctx (findPrimalBMap ctx lab)) ctx
        envlab0 <- genSingleId (labelType lab)
        envlab1 <- genSingleId (atypeOf1 arg1)
        let ctx'1 = ctxPushS (fmapLabel D lab) envlab0 ctx
            ctx' = ctxPushSEnvOnly envlab1 ctx'1
            cmap'' = addContrib (Local (alabelOf arg1))
                                (\ctx2 ->
                                    -- zipWith (*) (replicate (shape a) adjoint) (usual_derivative)
                                    let tempvar = resolveEnvLab ctx2 envlab1
                                    in smartZipWith (timesLam numType)
                                        (Replicate (nilLabel (atypeOf1 arg1)) onemoreSlix (onemoreExpf (smartShape (Left tempvar)))
                                                   (smartAvar (resolveEnvLab ctx2 (untupleA (findAdjointBMap ctx2 lab)))))
                                        (smartAvar tempvar))
                                cmap'
        DualResult (ABuilder ctx1 f1) stores1 cmap1 <- dual ctx' cmap'' arg1
        traceM (unlines ["!dual Fold[" ++ showDLabel lab ++ "]:"
                        ,"  envlab0 = " ++ showDLabel envlab0
                        ,"  envlab1 = " ++ showDLabel envlab1
                        ,"  stores = " ++ show stores1
                        ,"  out cmap = " ++ showCMapA ctx1 cmap1
                        ])
        return $ DualResult
            (ABuilder ctx1 (Alet (LeftHandSideSingle (labelType lab)) adjoint .
                            Alet (LeftHandSideSingle (labelType envlab1))
                                 (case ADExp.reverseAD lambdalhs (resolveAlabs ctx'1 lambdabody) of
                                    ADExp.ReverseADResE lambdalhs' dualbody ->
                                        -- let sc = init (scanl f x0 a)
                                        -- in zipWith (*) (zipWith D₂f sc a)
                                        --                (tail (scanr (*) 1 (zipWith D₁f sc a)))
                                        let d1f = Lam lambdalhs' (Body (smartFst dualbody))
                                            d2f = Lam lambdalhs' (Body (smartSnd dualbody))
                                            weaken1 = A.weakenSucc A.weakenId
                                            (d1f', d2f') = (sinkFunAenv weaken1 d1f, sinkFunAenv weaken1 d2f)
                                            argvar = resolveEnvLab ctx'1 (untupleA (findPrimalBMap ctx'1 (alabelOf arg1)))
                                            argvar' = weaken weaken1 argvar
                                            initScan ty dir f e0 a =  -- init (scanl) / tail (scanr)
                                                let scan'type = let ArrayR (ShapeRsnoc shtype) elttype = ty
                                                                in TupRpair (TupRsingle ty) (TupRsingle (ArrayR shtype elttype))
                                                in Aget (nilLabel (TupRsingle ty)) (TILeft TIHere) (Scan' (nilLabel scan'type) dir f e0 a)
                                        in Alet (LeftHandSideSingle (labelType envlab1))
                                                (initScan (labelType envlab1) A.LeftToRight
                                                    (resolveAlabsFun ctx'1 combfun)
                                                    (resolveAlabs ctx'1 initexp)
                                                    (smartAvar argvar))
                                                (smartZipWith (timesLam numType)
                                                    (smartZipWith d2f' (smartAvar (A.Var (atypeOf1 arg1) ZeroIdx)) (smartAvar argvar'))
                                                    (initScan (atypeOf1 arg1) A.RightToLeft (timesLam numType)
                                                        (zeroForType' 1 numType)
                                                        (smartZipWith d1f' (smartAvar (A.Var (atypeOf1 arg1) ZeroIdx)) (smartAvar argvar')))))
                            . f1))
            stores1  -- don't need to store this node
            cmap1
      | otherwise -> error ("Fold over non-Float array of type " ++ show (labelType lab) ++ " not yet supported for AD")

    Fold lab combfun Nothing arg1
      | TupRsingle (SingleScalarType (NumSingleType (FloatingNumType TypeFloat))) <- arrayRtype (labelType lab)
      -> do
        MatchLamBody lambdalhs lambdabody <- return (matchLamBody combfun)
        if expHasIndex lambdabody then error "Array index operations in a Fold1 lambda not yet supported for AD" else return ()

        ReplicateOneMore onemoreSlix onemoreExpf <- return (replicateOneMore (arrayRshape (labelType lab)))

        let (adjoint, cmap') = collectAdjointCMap cmap (Local (tupleLabel' lab)) (resolveEnvLabs ctx (findPrimalBMap ctx lab)) ctx
        envlab0 <- genSingleId (labelType lab)
        envlab1 <- genSingleId (atypeOf1 arg1)
        let ctx'1 = ctxPushS (fmapLabel D lab) envlab0 ctx
            ctx' = ctxPushSEnvOnly envlab1 ctx'1
            cmap'' = addContrib (Local (alabelOf arg1))
                                (\ctx2 ->
                                    -- zipWith (*) (replicate (shape a) adjoint) (usual_derivative)
                                    let tempvar = resolveEnvLab ctx2 envlab1
                                    in smartZipWith (timesLam numType)
                                        (Replicate (nilLabel (atypeOf1 arg1)) onemoreSlix (onemoreExpf (smartShape (Left tempvar)))
                                                   (smartAvar (resolveEnvLab ctx2 (untupleA (findAdjointBMap ctx2 lab)))))
                                        (smartAvar tempvar))
                                cmap'
        DualResult (ABuilder ctx1 f1) stores1 cmap1 <- dual ctx' cmap'' arg1
        traceM (unlines ["!dual Fold1[" ++ showDLabel lab ++ "]:"
                        ,"  envlab0 = " ++ showDLabel envlab0
                        ,"  envlab1 = " ++ showDLabel envlab1
                        ,"  stores = " ++ show stores1
                        ,"  out cmap = " ++ showCMapA ctx1 cmap1
                        ])
        return $ DualResult
            (ABuilder ctx1 (Alet (LeftHandSideSingle (labelType lab)) adjoint .
                            Alet (LeftHandSideSingle (labelType envlab1))
                                 (case ADExp.reverseAD lambdalhs (resolveAlabs ctx'1 lambdabody) of
                                    ADExp.ReverseADResE lambdalhs' dualbody ->
                                        -- let sc = init (scanl1 f a)
                                        -- in zipWith (*) ([1] ++ zipWith D₂f sc (tail l))
                                        --                (scanr (*) 1 (zipWith D₁f sc (tail l)))
                                        let d1f = Lam lambdalhs' (Body (smartFst dualbody))
                                            d2f = Lam lambdalhs' (Body (smartSnd dualbody))
                                            weaken1 = A.weakenSucc A.weakenId
                                            (d1f', d2f') = (sinkFunAenv weaken1 d1f, sinkFunAenv weaken1 d2f)
                                            argvar = resolveEnvLab ctx'1 (untupleA (findPrimalBMap ctx'1 (alabelOf arg1)))
                                            argvar' = weaken weaken1 argvar
                                        in Alet (LeftHandSideSingle (atypeOf1 arg1))
                                                (smartInit (Scan (nilLabel (atypeOf1 arg1)) A.LeftToRight
                                                    (resolveAlabsFun ctx'1 combfun)
                                                    Nothing
                                                    (smartAvar argvar)))
                                                (smartZipWith (timesLam numType)
                                                    (smartCons (zeroForType' 1 numType)
                                                        (smartZipWith d2f' (smartAvar (A.Var (atypeOf1 arg1) ZeroIdx)) (smartTail (smartAvar argvar'))))
                                                    (Scan (nilLabel (atypeOf1 arg1)) A.RightToLeft (timesLam numType)
                                                        (Just (zeroForType' 1 numType))
                                                        (smartZipWith d1f' (smartAvar (A.Var (atypeOf1 arg1) ZeroIdx)) (smartTail (smartAvar argvar'))))))
                            . f1))
            stores1  -- don't need to store this node
            cmap1
      | otherwise -> error ("Fold1 over non-Float array of type " ++ show (labelType lab) ++ " not yet supported for AD")

    Sum lab arg1 -> do
        ReplicateOneMore slixType slixExpGen <- return (replicateOneMore (arrayRshape (labelType lab)))
        simpleArrayDual "Sum" lab arg1 ctx cmap
            (\ctx2 ->
                Replicate (nilLabel (atypeOf1 arg1))
                          slixType
                          (slixExpGen (smartShape (Left
                              (resolveEnvLab ctx2 (untupleA (findPrimalBMap ctx2 (alabelOf arg1)))))))
                          (smartAvar (resolveEnvLab ctx2 (untupleA (findAdjointBMap ctx2 lab)))))

    Replicate lab slixspec _ arg1 ->
        simpleArrayDual "Replicate" lab arg1 ctx cmap
            (\ctx2 ->
                Reduce (nilLabel (atypeOf1 arg1))
                       (reduceSpecFromReplicate slixspec)
                       (plusLam (arrayRtype (atypeOf1 arg1)))
                       (smartAvar (resolveEnvLab ctx2 (untupleA (findAdjointBMap ctx2 lab)))))

    Slice lab slixspec arg1 slexp ->
        simpleArrayDual "Slice" lab arg1 ctx cmap
            (\ctx2 ->
                Generate (nilLabel (atypeOf1 arg1))
                         (smartShape (Left
                            (resolveEnvLab ctx2 (untupleA (findPrimalBMap ctx2 (alabelOf arg1))))))
                         (ELPlain (sliceDualLambda slixspec
                                                   (resolveEnvLab ctx2 (untupleA (findAdjointBMap ctx2 lab)))
                                                   (resolveAlabs ctx2 slexp))))

    Reshape lab _ arg1 ->
        simpleArrayDual "Reshape" lab arg1 ctx cmap
            (\ctx2 ->
                Reshape (nilLabel (atypeOf1 arg1))
                        (smartShape (Left
                            (resolveEnvLab ctx2 (untupleA (findPrimalBMap ctx2 (alabelOf arg1))))))
                        (smartAvar (resolveEnvLab ctx2 (untupleA (findAdjointBMap ctx2 lab)))))

    Backpermute lab _ lam arg1
      | MatchLamBody funLHS funBody <- matchLamBody lam ->
        simpleArrayDual "Backpermute" lab arg1 ctx cmap
            (\ctx2 ->
                Permute (nilLabel (atypeOf1 arg1))
                        (plusLam (arrayRtype (atypeOf1 arg1)))
                        (generateConstantArray (atypeOf1 arg1) (smartShape (Left
                            (resolveEnvLab ctx2 (untupleA (findPrimalBMap ctx2 (alabelOf arg1)))))))
                        (Lam funLHS (Body (mkJust (resolveAlabs ctx2 funBody))))
                        (smartAvar (resolveEnvLab ctx2 (untupleA (findAdjointBMap ctx2 lab)))))

    Aget lab tidx arg1 -> do
        simpleArrayDual "Aget" lab arg1 ctx cmap
            (\ctx2 ->
                oneHotTup (atypeOf arg1) tidx
                          (resolveEnvLabs ctx2 (findPrimalBMap ctx2 (alabelOf arg1)))
                          (avars (resolveEnvLabs ctx2 (findAdjointBMap ctx2 lab))))

    Alet _ arg1 arg2 -> do
        -- The contribution is stored in the cmap under the label of the body,
        -- so it will be communicated without work here in Let.
        DualResult (ABuilder ctx2 f2) stores2 cmap2 <- dual ctx cmap arg2
        -- The contribution for the RHS is already stored in the cmap, nothing
        -- more to do.
        DualResult (ABuilder ctx1 f1) stores1 cmap1 <- dual ctx2 cmap2 arg1
        traceM (unlines ["!dual Alet[let " ++ showDLabel (alabelOf arg1) ++ " in " ++ showDLabel (alabelOf arg2) ++ "]:"
                        ,"  cmap2 ! " ++ show (labelLabel (alabelOf arg1)) ++ " has " ++
                              show (maybe 0 (\(AdjList f) -> length (f ctx2)) (DMap.lookup (Local (alabelOf arg1)) cmap2)) ++ " entries"
                        ,"  stores = " ++ show (stores1 ++ stores2)
                        ,"  out cmap = " ++ showCMapA ctx1 cmap1
                        ])
        return $ DualResult
            (ABuilder ctx1 (f2 . f1))
            (stores1 ++ stores2)
            cmap1

    Avar lab _ (PartLabel referLab referPart) -> do
        let (adjoint, cmap') = collectAdjointCMap cmap (Local (tupleLabel' lab)) (resolveEnvLabs ctx (findPrimalBMap ctx lab)) ctx
        envlab0 <- genSingleId (labelType lab)
        let ctx' = ctxPushS (fmapLabel D lab) envlab0 ctx
            cmap'' = addContrib (Local referLab)
                                (\ctx2 ->
                                    oneHotTup (labelType referLab) referPart
                                              (resolveEnvLabs ctx2 (findPrimalBMap ctx2 referLab))
                                              (avars (resolveEnvLabs ctx2 (findAdjointBMap ctx2 lab))))
                                cmap'
        traceM (unlines ["!dual Avar[" ++ showDLabel lab ++ " -> " ++ tiPrefixExp referPart ++ " " ++ showDLabel referLab ++ "]:"
                        ,"  envlabs = [" ++ showDLabel envlab0 ++ "]"
                        ,"  out cmap = " ++ showCMapA ctx' cmap''
                        ])
        return $ DualResult
            (ABuilder ctx' (Alet (LeftHandSideSingle (labelType lab)) adjoint))
            [Some envlab0]  -- Store this node! We need to keep the contribution around for the (out-of-this-tree) RHS.
            cmap''

    Aarg lab argsty tidx -> do
        let (adjoint, cmap') = collectAdjointCMap cmap (Local (tupleLabel' lab)) (resolveEnvLabs ctx (findPrimalBMap ctx lab)) ctx
        envlab0 <- genSingleId (labelType lab)
        let ctx' = ctxPushS (fmapLabel D lab) envlab0 ctx
            cmap'' = addContrib (Argument argsty)
                                (\ctx2 ->
                                    case lhsCopy argsty of
                                      LetBoundVars argslhs argsvars ->
                                        -- Bind a tuple of Aarg nodes in a let-binding, so that we have
                                        -- variables (argsvars) to pass to oneHotTup as primal vars.
                                        Alet argslhs (argumentTuple argsty)
                                             (oneHotTup argsty tidx
                                                        argsvars
                                                        (sinkAcc (A.weakenWithLHS argslhs)
                                                            (avars (resolveEnvLabs ctx2 (findAdjointBMap ctx2 lab))))))
                                cmap'
        traceM (unlines ["!dual Aarg[" ++ showDLabel lab ++ " -> " ++ tiPrefixAcc tidx ++ " A]:"
                        ,"  envlabs = [" ++ showDLabel envlab0 ++ "]"
                        ,"  out cmap = " ++ showCMapA ctx' cmap''
                        ])
        return $ DualResult
            (ABuilder ctx' (Alet (LeftHandSideSingle (labelType lab)) adjoint))
            [Some envlab0]  -- Store this node! We need to keep the contribution around for the (out-of-this-tree) argument adjoint collection.
            cmap''

    Scan _ _ _ _ _ -> error "AD: Scan currently unsupported"
    Scan' _ _ _ _ _ -> error "AD: Scan' currently unsupported"
    Reduce _ _ _ _ -> error "AD: Reduce currently unsupported"
    Permute _ _ _ _ _ -> error "AD: Permute currently unsupported"
  where
    timesLam :: NumType t -> Fun aenv () alab tenv ((t, t) -> t)
    timesLam ty =
        let sty = SingleScalarType (NumSingleType ty)
        in Lam (LeftHandSidePair (LeftHandSideSingle sty) (LeftHandSideSingle sty))
               (Body (smartMul ty (smartVar (A.Var sty (SuccIdx ZeroIdx))) (smartVar (A.Var sty ZeroIdx))))

    smartInnerPermute :: (forall env aenv'. OpenExp env aenv' () () () () Int
                                         -> OpenExp env aenv' () () () () Int)  -- ^ new inner dimension size
                      -> (forall env aenv'. OpenExp env aenv' () () () () Int
                                         -> OpenExp env aenv' () () () () Int)  -- ^ inner index transformer
                      -> OpenAcc aenv () () args (Array (sh, Int) t)
                      -> OpenAcc aenv () () args (Array (sh, Int) t)
    smartInnerPermute sizeExpr indexExpr a
      | TupRsingle ty@(ArrayR shtype _) <- atypeOf a
      , TupRpair tailsht _ <- shapeType shtype
      , LetBoundVars shlhs shvars <- lhsCopy tailsht =
          Alet (LeftHandSideSingle ty) a
               (Backpermute (nilLabel ty)
                   (Let (LeftHandSidePair shlhs (LeftHandSideSingle scalarType))
                        (smartShape (Left (A.Var ty ZeroIdx)))
                        (smartPair
                            (evars (weakenVars (A.weakenSucc A.weakenId) shvars))
                            (sizeExpr (smartVar (A.Var scalarType ZeroIdx)))))
                   (Lam (LeftHandSidePair shlhs (LeftHandSideSingle scalarType))
                        (Body (smartPair
                                  (evars (weakenVars (A.weakenSucc A.weakenId) shvars))
                                  (indexExpr (smartVar (A.Var scalarType ZeroIdx))))))
                   (smartAvar (A.Var ty ZeroIdx)))
    smartInnerPermute _ _ _ = error "impossible GADTs"

    smartTail :: OpenAcc aenv () () args (Array (sh, Int) t) -> OpenAcc aenv () () args (Array (sh, Int) t)
    smartTail = smartInnerPermute (\sz -> smartSub numType sz (Const scalarLabel 1))
                                  (\idx -> smartAdd numType idx (Const scalarLabel 1))

    smartInit :: OpenAcc aenv () () args (Array (sh, Int) t) -> OpenAcc aenv () () args (Array (sh, Int) t)
    smartInit = smartInnerPermute (\sz -> smartSub numType sz (Const scalarLabel 1))
                                  (\idx -> idx)

    smartCons :: (forall env aenv'. OpenExp env aenv' () () () () t)
              -> OpenAcc aenv () () args (Array (sh, Int) t)
              -> OpenAcc aenv () () args (Array (sh, Int) t)
    smartCons prefix a
      | TupRsingle ty@(ArrayR shtype _) <- atypeOf a
      , TupRpair tailsht _ <- shapeType shtype
      , LetBoundVars shlhs shvars <- lhsCopy tailsht =
          Alet (LeftHandSideSingle ty) a
               (Generate (nilLabel ty)
                   (Let (LeftHandSidePair shlhs (LeftHandSideSingle scalarType))
                        (smartShape (Left (A.Var ty ZeroIdx)))
                        (smartPair
                            (evars (weakenVars (A.weakenSucc A.weakenId) shvars))
                            (smartAdd numType (smartVar (A.Var scalarType ZeroIdx)) (Const scalarLabel 1))))
                   (ELPlain (Lam (LeftHandSidePair shlhs (LeftHandSideSingle scalarType))
                                 (Body (smartCond
                                           (smartGt singleType (smartVar (A.Var scalarType ZeroIdx)) (Const scalarLabel 0))
                                           (smartIndex
                                               (A.Var ty ZeroIdx)
                                               (smartPair
                                                   (evars (weakenVars (A.weakenSucc A.weakenId) shvars))
                                                   (smartSub numType (smartVar (A.Var scalarType ZeroIdx)) (Const scalarLabel 1))))
                                           prefix)))))
    smartCons _ _ = error "impossible GADTs"

simpleArrayDual :: (IsTupleType ArrayR s, Show (s t))
                => String
                -> DLabel NodeLabel s Int t
                -> OpenAcc progaenv () Int args a
                -> AContext Int aenv
                -> DMap (CMapKey ArrayR Int) (AdjList () Int args)  -- contribmap
                -> (forall aenv'. AContext Int aenv' -> OpenAcc aenv' () () args a)
                -> IdGen (DualResult aenv Int args)
simpleArrayDual name lab arg ctx cmap contribution = do
    let lab' = tupleLabel lab
        (adjoint, cmap') = collectAdjointCMap cmap (Local lab') (resolveEnvLabs ctx (findPrimalBMap ctx lab)) ctx
    (Exists envlhs, envlabs) <- genSingleIds (labelType lab')
    let ctx' = ctxPush envlhs (fmapLabel D lab') envlabs ctx
        cmap'' = addContrib (Local (alabelOf arg)) contribution cmap'
    DualResult (ABuilder ctx1 f1) stores1 cmap1 <- dual ctx' cmap'' arg
    traceM (unlines ["!dual " ++ name ++ "[" ++ showDLabel lab ++ "]:"
                    ,"  envlabs = " ++ showTupR showDLabel envlabs
                    ,"  stores = " ++ show stores1
                    ,"  out cmap = " ++ showCMapA ctx1 cmap1
                    ])
    return $ DualResult
        (ABuilder ctx1 (Alet envlhs adjoint . f1))
        stores1  -- don't need to store this node
        cmap1

-- Utility functions
-- -----------------

data MatchLamBody env aenv lab alab tenv t t' =
    forall env'.
        MatchLamBody (A.ELeftHandSide t env env') (OpenExp env' aenv lab alab () tenv t')

-- This function exists only to be able to bind a 'Lam lhs (Body body)' in a non-MonadFail
-- environment without hassle.
matchLamBody :: HasCallStack => OpenFun env aenv lab alab tenv (t -> t') -> MatchLamBody env aenv lab alab tenv t t'
matchLamBody (Lam lhs (Body body)) = MatchLamBody lhs body
matchLamBody _ = error "matchLamBody: function has more than one argument"

unionCMap :: Ord alab
          => DMap (CMapKey ArrayR alab) (AdjList lab alab args)
          -> DMap (CMapKey ArrayR alab) (AdjList lab alab args)
          -> DMap (CMapKey ArrayR alab) (AdjList lab alab args)
unionCMap = DMap.unionWithKey (const (<>))

-- Collect adjoint from the contribution map, and returns the map with this label's entries removed.
collectAdjointCMap :: DMap (CMapKey ArrayR Int) (AdjList () Int args)
                   -> CMapKey ArrayR Int t
                   -> A.ArrayVars aenv t  -- primal result of the queried-for node
                   -> AContext Int aenv
                   -> (OpenAcc aenv () () args t
                      ,DMap (CMapKey ArrayR Int) (AdjList () Int args))
collectAdjointCMap contribmap key pvars ctx =
    case DMap.lookup key contribmap of
        Just (AdjList listgen) ->
          let adj = arraysSum (cmapKeyType key) pvars (listgen ctx)
          in trace ("\x1B[1macc cmap collect: " ++ showCMapKey showDLabel key ++ " ==> " ++ show adj ++ "\x1B[0m") $
             (adj, DMap.delete key contribmap)
        Nothing -> -- if there are no contributions, well, the adjoint is an empty sum (i.e. zero)
                   let res = arraysSum (cmapKeyType key) pvars []
                   in trace ("\x1B[1macc cmap collect: " ++ showCMapKey showDLabel key ++ " ==> {} ==> " ++ show res ++ "\x1B[0m") $
                      (res, contribmap)

addContrib :: CMapKey ArrayR Int t
           -> (forall aenv. AContext Int aenv -> OpenAcc aenv () () args t)
           -> DMap (CMapKey ArrayR Int) (AdjList () Int args)
           -> DMap (CMapKey ArrayR Int) (AdjList () Int args)
addContrib key gen = DMap.insertWith (<>) key (AdjList (pure . gen))

lookupLambdaLabs :: AContext Int env  -- context
                 -> TupR (AAnyPartLabelN Int) t  -- free variable labels from SplitLambdaAD
                 -> A.ArrayVars env t  -- resolved labels pointing into the current labelenv
lookupLambdaLabs ctx =
    joinTupR .
        fmapTupR (\(AnyPartLabel (PartLabel lab tidx)) ->
                      pickTupR tidx (resolveEnvLabs ctx (findPrimalBMap ctx lab)))

-- | The function in an expression lambda may contain array indexing
-- operations, which should contribute adjoints to elements of the indexed
-- arrays. This function builds the contribution map entries (using Permute
-- operations) for the indexed arrays given the array of index adjoint info
-- tuples of the dual function in SplitLambdaAD, as well as the indexing
-- instantiator map in SplitLambdaAD.
-- TODO: split this up to avoid the 74-space-deep indentation
indexingContributions
    :: ADLabel Int (Array sh idxadj)  -- ^ Env label of the array of index adjoint info tuples
    -> DMap (AAnyPartLabelN Int) (IndexInstantiators idxadj)  -- ^ The indexing instantiator map from SplitLambdaAD
    -> DMap (CMapKey ArrayR Int) (AdjList () Int args)  -- ^ The contribution map from indexing
indexingContributions idxadjlab idxInstMap =
    let ArrayR shtype idxadjType = labelType idxadjlab
    in DMap.fromList
         [Local backingLab :=> AdjList (\ctx ->
            [let pvars = resolveEnvLabs ctx (findPrimalBMap ctx backingLab)
                 TupRsingle backingPVar = pickTupR backingPart pvars
                 contrib = Permute (nilLabel backingType)
                                   (plusLam backingEltType)
                                   (generateConstantArray backingType
                                        (Shape (nilLabel backingShapeT) (Left backingPVar)))
                                   (case lhsCopy (shapeType shtype) of  -- Lambda: map use-point index to backing index
                                      LetBoundVars idxlhs idxvars
                                        | LetBoundVars ialhs iavars <- lhsCopy idxadjType ->
                                            Lam idxlhs (Body
                                              (Let ialhs
                                                   (Index (nilLabel idxadjType)  -- get idxadj tuple
                                                          (Left (resolveEnvLab ctx idxadjlab))
                                                          scalarLabel
                                                          (evars idxvars))
                                                   (smartCond  -- if the Index was executed
                                                        (smartSnd (instantiator (evars iavars)))
                                                        (mkJust (smartGet (TILeft (TIRight TIHere))  -- get the index
                                                                          (instantiator (evars iavars))))
                                                        (mkNothing backingShapeT)))))  -- else return Nothing
                                   (Map (nilLabel (ArrayR shtype backingEltType))  -- Map: obtain the array of adjoints to be permuted
                                        (ELPlain
                                           (case lhsCopy idxadjType of
                                              LetBoundVars lhs vars ->
                                                Lam lhs (Body  -- Choose the adjoint item from the ((adj, idx), Bool) tuple
                                                  (smartGet (TILeft (TILeft TIHere))
                                                     (instantiator (evars vars))))))
                                        (smartAvar (resolveEnvLab ctx idxadjlab)))
             in oneHotTup fullBackingType backingPart pvars contrib
            | IndexInstantiator instantiator <- insts
            , let fullBackingType = labelType backingLab
                  TupRsingle backingType@(ArrayR backingSht backingEltType) =
                      pickTupR backingPart fullBackingType
                  backingShapeT = shapeType backingSht])
         | AnyPartLabel (PartLabel backingLab backingPart) :=> IndexInstantiators insts <- DMap.toList idxInstMap]

arrayPlus :: OpenAcc aenv () () args (Array sh t)
          -> OpenAcc aenv () () args (Array sh t)
          -> OpenAcc aenv () () args (Array sh t)
-- arrayPlus a1 a2
--   | TupRsingle arrty@(ArrayR _ ty) <- atypeOf a1
--   = ZipWith (nilLabel arrty) (ELPlain (uncurryFun (plusLam ty))) a1 a2
arrayPlus a1 a2 = case atypeOf1 a1 of
    arrty@(ArrayR ShapeRz ty) ->
      ZipWith (nilLabel arrty) (ELPlain (uncurryFun (plusLam ty))) a1 a2

    arrty@(ArrayR sht@(ShapeRsnoc _) ty)
      | LetBoundVars shlhs shvars <- lhsCopy (shapeType sht) ->
          Alet (LeftHandSidePair (LeftHandSideSingle arrty) (LeftHandSideSingle arrty))
               (smartApair a1 a2) $
            let a1var = A.Var arrty (SuccIdx ZeroIdx)
                a2var = A.Var arrty ZeroIdx
            in
              -- -- TODO: of these two, which is more efficient?
              -- Acond (nilLabel (TupRsingle arrty))
              --       (shapeIsZeroE sht (smartShape (Left a1var)))
              --       (smartAvar a2var)
              --       (Acond (nilLabel (TupRsingle arrty))
              --              (shapeIsZeroE sht (smartShape (Left a2var)))
              --              (smartAvar a1var)
              --              (ZipWith (nilLabel arrty) (ELPlain (uncurryFun (plusLam ty))) (smartAvar a1var) (smartAvar a2var)))
              Generate (nilLabel arrty)
                       (maxShapeE sht (smartShape (Left a1var)) (smartShape (Left a2var)))
                       (ELPlain (Lam shlhs (Body
                           (smartCond (shapeIsZeroE sht (smartShape (Left a1var)))
                                      (smartIndex a2var (evars shvars))
                                      (smartCond (shapeIsZeroE sht (smartShape (Left a2var)))
                                                 (smartIndex a1var (evars shvars))
                                                 (expPlus ty (smartIndex a1var (evars shvars))
                                                             (smartIndex a2var (evars shvars))))))))

arraySum :: ArrayR (Array sh t)
         -> A.ArrayVar aenv (Array sh t)  -- primal result
         -> [OpenAcc aenv () () args (Array sh t)]
         -> OpenAcc aenv () () args (Array sh t)
arraySum ty@(ArrayR sht _) pvar [] = 
    generateConstantArray ty (Shape (nilLabel (shapeType sht)) (Left pvar))
arraySum _ _ [a] = a
arraySum arrty pvar (a1:as) = arrayPlus a1 (arraySum arrty pvar as)

shapeIsZeroE :: ShapeR (sh, Int) -> OpenExp env aenv () alab args tenv (sh, Int) -> OpenExp env aenv () alab args tenv A.PrimBool
shapeIsZeroE (ShapeRsnoc ShapeRz) expr =
    smartEq singleType (smartSnd expr) (Const (nilLabel scalarType) 0)
shapeIsZeroE (ShapeRsnoc sht@(ShapeRsnoc _)) expr =
    smartLAnd (shapeIsZeroE sht (smartFst expr))
              (smartEq singleType (smartSnd expr) (Const (nilLabel scalarType) 0))

arraysSum :: ArraysR t
          -> A.ArrayVars aenv t  -- primal result
          -> [OpenAcc aenv () () args t]
          -> OpenAcc aenv () () args t
arraysSum TupRunit TupRunit _ = Anil (nilLabel TupRunit)
arraysSum (TupRsingle ty@ArrayR{}) (TupRsingle pvar) l =
    arraySum ty pvar l
arraysSum ty@(TupRpair t1 t2) (TupRpair pvars1 pvars2) l
  | Just (l1, l2) <- unzip <$> traverse (\case Apair _ a1 a2 -> Just (a1, a2) ; _ -> Nothing) l =
      Apair (nilLabel ty) (arraysSum t1 pvars1 l1) (arraysSum t2 pvars2 l2)
arraysSum ty _ l = trace ("\x1B[1;41m- - - - - - - - - - WARNING: arraysSum: non-paired case! - - - - - - - - - -\x1B[0m") $
                   foldl1 (tupleZipAcc' ty (const arrayPlus) (\_ _ -> False)) l

generateConstantArray :: ArrayR (Array sh t) -> Exp aenv () () () () sh -> OpenAcc aenv () () args (Array sh t)
generateConstantArray ty@(ArrayR sht eltty) she =
    Generate (nilLabel ty) she
             (ELPlain (Lam (LeftHandSideWildcard (shapeType sht)) (Body (zeroForType eltty))))

emptiesForType :: ArraysR t -> OpenAcc aenv () () args t
emptiesForType TupRunit = Anil (nilLabel TupRunit)
emptiesForType (TupRsingle ty@(ArrayR sht _)) = generateConstantArray ty (zeroForType (shapeType sht))
emptiesForType (TupRpair t1 t2) = smartApair (emptiesForType t1) (emptiesForType t2)

expGetLam :: TupleIdx t t' -> TypeR t -> Fun aenv () alab tenv (t -> t')
expGetLam ti ty
  | LetBoundVars lhs vars <- lhsCopy ty
  = Lam lhs (Body (evars (pickTupR ti vars)))

mapGet :: TupleIdx t t' -> OpenAcc aenv () () tenv (Array sh t) -> OpenAcc aenv () () tenv (Array sh t')
mapGet ti a =
  let TupRsingle (ArrayR sht ty) = atypeOf a
  in Map (nilLabel (ArrayR sht (pickTupR ti ty))) (ELPlain (expGetLam ti ty)) a

mapFst :: OpenAcc aenv () () tenv (Array sh (a, b)) -> OpenAcc aenv () () tenv (Array sh a)
mapFst = mapGet (TILeft TIHere)

mapSnd :: OpenAcc aenv () () tenv (Array sh (a, b)) -> OpenAcc aenv () () tenv (Array sh b)
mapSnd = mapGet (TIRight TIHere)

plusLam :: TypeR t -> Fun aenv () alab tenv (t -> t -> t)
plusLam ty
  | DeclareVars lhs1 _ varsgen1 <- declareVars ty
  , DeclareVars lhs2 weaken2 varsgen2 <- declareVars ty
  = Lam lhs1 . Lam lhs2 . Body $ expPlus ty (evars (varsgen1 weaken2)) (evars (varsgen2 A.weakenId))

uncurryFun :: Fun aenv lab alab tenv (a -> b -> c) -> Fun aenv lab alab tenv ((a, b) -> c)
uncurryFun (Lam l1 (Lam l2 (Body e))) = Lam (LeftHandSidePair l1 l2) (Body e)
uncurryFun _ = error "uncurryFun: impossible GADTs"

oneHotTup :: ArraysR t -> TupleIdx t t' -> A.ArrayVars aenv t -> OpenAcc aenv () () args t' -> OpenAcc aenv () () args t
oneHotTup _ TIHere _ ex = ex
oneHotTup ty@(TupRpair ty1 ty2) (TILeft ti) (TupRpair pvars1 pvars2) ex =
    Apair (nilLabel ty) (oneHotTup ty1 ti pvars1 ex) (arraysSum ty2 pvars2 [])
oneHotTup ty@(TupRpair ty1 ty2) (TIRight ti) (TupRpair pvars1 pvars2) ex =
    Apair (nilLabel ty) (arraysSum ty1 pvars1 []) (oneHotTup ty2 ti pvars2 ex)
oneHotTup _ _ _ _ = error "oneHotTup: impossible GADTs"

-- Remark: this function is uniquely defined by its types (ignoring bottoms). This is nice.
reduceSpecFromReplicate :: SliceIndex slix sl co sh -> ReduceSpec slix sl sh
reduceSpecFromReplicate SliceNil = RSpecNil
reduceSpecFromReplicate (SliceAll slix) = RSpecKeep (reduceSpecFromReplicate slix)
reduceSpecFromReplicate (SliceFixed slix) = RSpecReduce (reduceSpecFromReplicate slix)

data ReplicateOneMore sh =
    forall slix.
        ReplicateOneMore (SliceIndex slix sh ((), Int) (sh, Int))
                         (forall env aenv alab args tenv.
                              OpenExp env aenv () alab args tenv (sh, Int)
                           -> OpenExp env aenv () alab args tenv slix)

-- Produces a SliceIndex that can be passed to Replicate, and a function that
-- produces the slix expression parameter to Replicate, given an expression for
-- the desired full shape.
replicateOneMore :: ShapeR sh -> ReplicateOneMore sh
replicateOneMore sh
  | SliceCopy slix e <- sliceCopy sh
  = ReplicateOneMore (SliceFixed slix)
                     (\she -> Let (LeftHandSidePair (LeftHandSideWildcard (shapeType (sliceShapeR slix)))
                                                    (LeftHandSideSingle scalarType))
                                  she
                                  (smartPair e (smartVar (A.Var scalarType ZeroIdx))))

data SliceCopy sh =
    forall slix.
        SliceCopy (SliceIndex slix sh () sh)
                  (forall env aenv alab args tenv. OpenExp env aenv () alab args tenv slix)

sliceCopy :: ShapeR sh -> SliceCopy sh
sliceCopy ShapeRz = SliceCopy SliceNil (Nil magicLabel)
sliceCopy (ShapeRsnoc sh)
  | SliceCopy slix e <- sliceCopy sh
  = SliceCopy (SliceAll slix) (smartPair e (Nil magicLabel))


-- The dual of Slice is a Generate that picks the adjoint for the entries
-- sliced, and zero for the entries cut away. This is the lambda for that
-- Generate.
sliceDualLambda :: SliceIndex slix sl co sh
                -> A.Var ArrayR aenv (Array sl e)
                -> Exp aenv () alab () tenv slix
                -> Fun aenv () alab tenv (sh -> e)
sliceDualLambda slix adjvar@(A.Var (ArrayR _ eltty) _) slexpr
  | LetBoundVars indexlhs indexvars' <- lhsCopy (shapeType (sliceDomainR slix))
  , LetBoundVars slicelhs slicevars <- lhsCopy (sliceIndexTypeR slix)
  , let indexvars = weakenVars (A.weakenWithLHS slicelhs) indexvars'
  = Lam indexlhs . Body $
      Let slicelhs (sinkExp (A.weakenWithLHS indexlhs) slexpr) $
          Cond (nilLabel eltty)
               (genCond slix indexvars slicevars)
               (Index (nilLabel eltty) (Left adjvar) scalarLabel (evars (indexSlice slix indexvars)))
               (zeroForType eltty)
  where
    indexSlice :: SliceIndex slix sl co sh -> A.ExpVars env sh -> A.ExpVars env sl
    indexSlice SliceNil _ = TupRunit
    indexSlice (SliceAll slix') (TupRpair vars var) = TupRpair (indexSlice slix' vars) var
    indexSlice (SliceFixed slix') (TupRpair vars _) = indexSlice slix' vars
    indexSlice _ _ = error "impossible GADTs"

    genCond :: SliceIndex slix sl co sh -> A.ExpVars env sh -> A.ExpVars env slix -> OpenExp env aenv () alab args tenv A.PrimBool
    genCond SliceNil TupRunit TupRunit = mkBool True
    genCond (SliceAll slix') (TupRpair idxvs _) (TupRpair slvs _) = genCond slix' idxvs slvs
    genCond (SliceFixed slix') (TupRpair idxvs (TupRsingle idxv)) (TupRpair slvs (TupRsingle slv)) =
        PrimApp magicLabel A.PrimLAnd
            (smartPair (PrimApp magicLabel (A.PrimEq singleType)
                             (smartPair (smartVar idxv) (smartVar slv)))
                        (genCond slix' idxvs slvs))
    genCond _ _ _ = error "impossible GADTs"

sliceIndexTypeR :: SliceIndex slix sl co dim -> TypeR slix
sliceIndexTypeR SliceNil        = TupRunit
sliceIndexTypeR (SliceAll sl)   = TupRpair (sliceIndexTypeR sl) TupRunit
sliceIndexTypeR (SliceFixed sl) = TupRpair (sliceIndexTypeR sl) (TupRsingle scalarType)

resolveAlabs :: HasCallStack
             => AContext Int aenv
             -> OpenExp env aenv' lab Int args tenv t
             -> OpenExp env aenv lab alab' args tenv t
resolveAlabs ctx ex =
    inlineAvarLabels'
        (\(AnyPartLabel (PartLabel lab tidx)) ->
            untupleA (pickTupR tidx (resolveEnvLabs ctx (findPrimalBMap ctx lab))))
        ex

resolveAlabsFun :: HasCallStack
                => AContext Int aenv
                -> OpenFun env aenv' lab Int tenv t
                -> OpenFun env aenv lab alab' tenv t
resolveAlabsFun ctx (Lam lhs fun) = Lam lhs (resolveAlabsFun ctx fun)
resolveAlabsFun ctx (Body ex) = Body (resolveAlabs ctx ex)

minShapeE :: ShapeR sh -> OpenExp env aenv () alab args tenv sh -> OpenExp env aenv () alab args tenv sh -> OpenExp env aenv () alab args tenv sh
minShapeE sht = tupleZipExp' (shapeType sht) (\(SingleScalarType sty) e1 e2 -> smartMin sty e1 e2) (\_ _ -> False)

maxShapeE :: ShapeR sh -> OpenExp env aenv () alab args tenv sh -> OpenExp env aenv () alab args tenv sh -> OpenExp env aenv () alab args tenv sh
maxShapeE sht = tupleZipExp' (shapeType sht) (\(SingleScalarType sty) e1 e2 -> smartMax sty e1 e2) (\_ _ -> False)

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
