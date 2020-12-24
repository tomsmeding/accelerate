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
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Config
import Data.Array.Accelerate.Trafo.AD.Debug
import Data.Array.Accelerate.Trafo.AD.Exp
import qualified Data.Array.Accelerate.Trafo.AD.Heuristic as Heuristic
import Data.Array.Accelerate.Trafo.AD.Pretty
import Data.Array.Accelerate.Trafo.AD.Sink
import Data.Array.Accelerate.Trafo.AD.TupleZip
import Data.Array.Accelerate.Trafo.Substitution (rebuildLHS, weakenVars)
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
        resty = atypeOf expr
        argsRHS = untupleAccs
                      (zipWithTupR (\ty@ArrayR{} tidx -> Aarg (nilLabel ty) paramty tidx)
                                   paramty
                                   (tupleIndices paramty))
    (argsRHSlabel, expr') <- enlabelAccToplevel paramlhs argsRHS (generaliseArgs expr)

    traceM ("acc labeled: " ++ prettyPrint expr')

    PrimalResult (ABuilder primalCtx primalBuilder) _ _ <-
        primal (Context LEmpty mempty) expr'

    (Exists adjlhs, adjlabs) <- genSingleIds resty
    let dualCtxIn = let Context labelenv bindmap = ctxPush adjlhs (fmapLabel D (alabelOf expr')) adjlabs primalCtx
                        argsLabs = findPrimalBMap (Context labelenv bindmap) argsRHSlabel
                    in Context labelenv (DMap.insert (Argument paramty) argsLabs bindmap)
    DualResult (ABuilder dualCtx dualBuilder) _ _ dualCMap <- dual dualCtxIn expr'
    let argpvars = resolveEnvLabs dualCtx (findPrimalBMap dualCtx argsRHSlabel)
        (gradient, _) = collectAdjointCMap dualCMap (Argument paramty) argpvars dualCtx

    return $ ReverseADResA
        paramlhs
        (realiseArgs paramlhs
            (primalBuilder
             . Alet adjlhs (Generate (nilLabel (ArrayR ShapeRz (TupRsingle scalarType)))
                                     (Nil magicLabel)
                                     (ELPlain (Lam (LeftHandSideWildcard TupRunit)
                                                   (Body (Const (nilLabel scalarType) 1.0)))))
             . dualBuilder
             $ gradient))

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
        Aarg lab@(labelType -> ArrayR (shapeType -> sht) eltty) _ tidx ->
            case indexIntoLHS paramlhs tidx of
              Just idx -> let nillab = nilLabel (labelType lab)
                          in Avar nillab (A.Var (labelType lab) (argWeaken A.>:> idx))
                                  (PartLabel (tupleLabel nillab) TIHere)
              Nothing
                | LetBoundVars lhs _ <- lhsCopy sht
                -> Generate (nilLabel (labelType lab)) (zeroForType sht)
                            (ELPlain (Lam lhs (Body (zeroForType eltty))))

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
            ([Some envlab1, Some envlab2] ++ stores1)
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
            ([Some envlab1, Some envlab2] ++ stores1 ++ stores2)
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

data DualResult aenv alab args =
    DualResult (ABuilder aenv alab args)   -- Dual builder
               [Some (ADLabel Int)]        -- To-store "set" (really list)
               [Some (ADLabel Int)]        -- Computed "set" (really list)
               (DMap (CMapKey ArrayR Int)  -- Contribution map (only for let-bound things and array indexing)
                     (AdjList () alab args))

dual :: AContext Int aenv
     -> OpenAcc progaenv () Int args t
     -> IdGen (DualResult aenv Int args)
dual ctx = \case
    Aconst _ _ ->
        return (DualResult (ABuilder ctx id) [] [] mempty)

    Apair lab arg1 arg2 -> do
        let adjointLabs = findAdjointBMap ctx lab
            adjoint = avars (resolveEnvLabs ctx adjointLabs)
        (Exists lhs1, envlabs1) <- genSingleIds (atypeOf arg1)
        (Exists lhs2, envlabs2) <- genSingleIds (atypeOf arg2)
        let ctx' = ctx & ctxPush lhs1 (fmapLabel D (alabelOf arg1)) envlabs1
                       & ctxPush lhs2 (fmapLabel D (alabelOf arg2)) envlabs2
        DualResult (ABuilder ctx1 f1) stores1 compd1 cmap1 <- dual ctx' arg1
        DualResult (ABuilder ctx2 f2) stores2 compd2 cmap2 <- dual ctx1 arg2
        return $ DualResult
            (ABuilder ctx2 (Alet (LeftHandSidePair lhs1 lhs2) adjoint
                            . f1 . f2))
            (stores1 ++ stores2)  -- don't need to store this node
            (enumerateTupR envlabs1 ++ enumerateTupR envlabs2 ++ compd1 ++ compd2)
            (cmap1 `unionCMap` cmap2)

    Anil _ ->
        return (DualResult (ABuilder ctx id) [] [] mempty)

    Acond lab condexp argT argE -> do
        let adjointLabs = findAdjointBMap ctx lab
            Context labelenv bindmap = ctx
            ctxInT = Context labelenv
                             (DMap.insert (Local (fmapLabel D (alabelOf argT))) adjointLabs bindmap)
            ctxInE = Context labelenv
                             (DMap.insert (Local (fmapLabel D (alabelOf argE))) adjointLabs bindmap)
        DualResult (ABuilder ctxT fT) storesT compdT cmapT <- dual ctxInT argT
        DualResult (ABuilder ctxE fE) storesE compdE cmapE <- dual ctxInE argE
        Some' tmplabsT <- returnSome (tuplify (intersectOrd storesT compdT))
        Some' tmplabsE <- returnSome (tuplify (intersectOrd storesE compdE))
        let tmptyT = fmapTupR labelType tmplabsT
            tmptyE = fmapTupR labelType tmplabsE
            branchty = TupRpair tmptyT tmptyE
        LetBoundVars lhsT _ <- return (lhsCopy tmptyT)
        LetBoundVars lhsE _ <- return (lhsCopy tmptyE)
        let branchlhs = LeftHandSidePair lhsT lhsE
            labelenv' = labelenv & lpushLabTup lhsT tmplabsT
                                 & lpushLabTup lhsE tmplabsE
            bindmap' = dmapDisjointUnions
                          [bindmap
                          ,let Context _ bm = ctxT in bm DMap.\\ bindmap
                          ,let Context _ bm = ctxE in bm DMap.\\ bindmap]
        traceM (unlines ["!dual Acond[" ++ showDLabel lab ++ "]:"
                        ,"  adjointLabs = " ++ showTupR showDLabel adjointLabs
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
                      (Alet branchlhs
                            (Acond (nilLabel branchty)
                                   (resolveAlabs ctx condexp)
                                   (fT (smartApair
                                           (avars (resolveEnvLabs ctxT tmplabsT))
                                           (emptiesForType tmptyE)))
                                   (fE (smartApair
                                           (emptiesForType tmptyT)
                                           (avars (resolveEnvLabs ctxE tmplabsE)))))))
            (storesT ++ storesE)  -- don't need to store this node
            (enumerateTupR tmplabsT ++ enumerateTupR tmplabsE)
            (cmapT `unionCMap` cmapE)

    -- The expression determining the shape has an integral result, and can thus be
    -- ignored here. All that we do is collect the indexing contributions.
    Generate lab _ (ELSplit (SplitLambdaAD _ dualLambda fvlabs _ idxadjty idxInsts) tmplab) -> do
        let adjointLabs = findAdjointBMap ctx lab
            adjoint = avars (resolveEnvLabs ctx adjointLabs)
            sht = arrayRshape (labelType lab)
            iaarrty = ArrayR sht idxadjty
            pairarrty = ArrayR sht (TupRpair (shapeType sht) idxadjty)
        envlab1 <- genSingleId iaarrty
        let ctx' = ctxPushSEnvOnly envlab1 ctx
        return $ DualResult
            (ABuilder ctx' (Alet (LeftHandSideSingle iaarrty)
                                 (mapSnd
                                     (ZipWith (nilLabel pairarrty)
                                              (ELPlain (dualLambda (lookupLambdaLabs ctx fvlabs)))
                                              adjoint
                                              (avars (resolveEnvLabs ctx (findPrimalBMap ctx tmplab)))))))
            []  -- don't need to store this node
            [Some envlab1]
            (indexingContributions envlab1 idxInsts)

    Map lab (ELSplit (SplitLambdaAD _ dualLambda fvlabs _ idxadjty idxInsts) tmplab) arg1 -> do
        let adjointLabs = findAdjointBMap ctx lab
            adjoint = avars (resolveEnvLabs ctx adjointLabs)
            ArrayR sht argeltty = atypeOf1 arg1
            iaarrty = ArrayR sht idxadjty
            pairarrty = ArrayR sht (TupRpair argeltty idxadjty)
        envlab1 <- genSingleId (atypeOf1 arg1)
        envlab2 <- genSingleId iaarrty
        let ctx' = ctx & ctxPushS (fmapLabel D (alabelOf1 arg1)) envlab1
                       & ctxPushSEnvOnly envlab2
        DualResult (ABuilder ctx1 f1) stores1 compd1 cmap1 <- dual ctx' arg1
        traceM (unlines ["!dual Map[" ++ showDLabel lab ++ "]:"
                        ,"  adjointLabs = " ++ showTupR showDLabel adjointLabs
                        ,"  envlab1 = " ++ showDLabel envlab1 ++ "  (adjoint of node " ++ showDLabel (alabelOf arg1) ++ ")"
                        ,"  envlab2 = " ++ showDLabel envlab2
                        ,"  stores = " ++ show stores1
                        ,"  computed = " ++ show (Some envlab1 : Some envlab2 : compd1)
                        ,"  out cmap = " ++ showCMap (cmap1 `unionCMap` indexingContributions envlab2 idxInsts)
                        ])
        return $ DualResult
            (ABuilder ctx1 (Alet (LeftHandSidePair (LeftHandSideSingle (atypeOf1 arg1))
                                                   (LeftHandSideSingle iaarrty))
                                 (Alet (LeftHandSideSingle pairarrty)
                                       (ZipWith (nilLabel pairarrty)
                                                (ELPlain (dualLambda (lookupLambdaLabs ctx fvlabs)))
                                                adjoint
                                                (avars (resolveEnvLabs ctx (findPrimalBMap ctx tmplab))))
                                       (let var = smartAvar (A.Var pairarrty ZeroIdx)
                                        in smartApair (mapFst var) (mapSnd var)))
                            . f1))
            stores1  -- don't need to store this node
            (Some envlab1 : Some envlab2 : compd1)
            (cmap1 `unionCMap` indexingContributions envlab2 idxInsts)

    ZipWith lab (ELSplit (SplitLambdaAD _ dualLambda fvlabs _ idxadjty idxInsts) tmplab) arg1 arg2 -> do
        let adjointLabs = findAdjointBMap ctx lab
            adjoint = avars (resolveEnvLabs ctx adjointLabs)
            ArrayR sht arg1eltty = atypeOf1 arg1
            ArrayR _ arg2eltty = atypeOf1 arg2
            iaarrty = ArrayR sht idxadjty
            pairarrty = ArrayR sht (TupRpair (TupRpair arg1eltty arg2eltty) idxadjty)
        envlab1 <- genSingleId (atypeOf1 arg1)
        envlab2 <- genSingleId (atypeOf1 arg2)
        envlab3 <- genSingleId iaarrty
        let ctx' = ctx & ctxPushS (fmapLabel D (alabelOf1 arg1)) envlab1
                       & ctxPushS (fmapLabel D (alabelOf1 arg2)) envlab2
                       & ctxPushSEnvOnly envlab3
        DualResult (ABuilder ctx1 f1) stores1 compd1 cmap1 <- dual ctx' arg1
        DualResult (ABuilder ctx2 f2) stores2 compd2 cmap2 <- dual ctx1 arg2
        return $ DualResult
            (ABuilder ctx2 (Alet (LeftHandSidePair (LeftHandSidePair (LeftHandSideSingle (atypeOf1 arg1))
                                                                     (LeftHandSideSingle (atypeOf1 arg2)))
                                                   (LeftHandSideSingle iaarrty))
                                 (Alet (LeftHandSideSingle pairarrty)
                                       (ZipWith (nilLabel pairarrty)
                                                (ELPlain (dualLambda (lookupLambdaLabs ctx fvlabs)))
                                                adjoint
                                                (avars (resolveEnvLabs ctx (findPrimalBMap ctx tmplab))))
                                       (let var = smartAvar (A.Var pairarrty ZeroIdx)
                                        in smartApair (smartApair (mapGet (TILeft (TILeft TIHere)) var)
                                                                  (mapGet (TILeft (TIRight TIHere)) var))
                                                      (mapSnd var)))
                            . f1 . f2))
            (stores1 ++ stores2)  -- don't need to store this node
            (Some envlab1 : Some envlab2 : Some envlab3 : compd1 ++ compd2)
            (cmap1 `unionCMap` cmap2 `unionCMap` indexingContributions envlab3 idxInsts)

    -- Fold lab combfun (Just initexp) arg1 -> do
    --     SomeSplitLambdaAD (SplitLambdaAD primalLambda dualLambda fvlabs tmpty idxadjty idxInsts) <-
    --         return (splitLambdaAD (generaliseAenvFun combfun))

    --     let adjointLabs = findAdjointBMap ctx lab
    --         adjoint = avars (resolveEnvLabs ctx adjointLabs)
    --         ArrayR sht argeltty = atypeOf1 arg1
    --         iaarrty = ArrayR sht idxadjty
    --         pairarrty = ArrayR sht (TupRpair argeltty idxadjty)

    --     envlab1 <- genSingleId undefined
    --     envlab2 <- genSingleId undefined
    --     envlab3 <- genSingleId undefined

    --     let ctx'1 = ctxPushSEnvOnly envlab1 ctx
    --         ctx'2 = ctx'1 & ctxPushSEnvOnly envlab2
    --                       & ctxPushSEnvOnly envlab3

    --     MatchLamBody primalLHS primalBody <-
    --         return (matchLamBody (primalLambda (lookupLambdaLabs ctx'1 fvlabs)))
    --     MatchLamBody dualLHS dualBody <-
    --         return (matchLamBody (sinkFun (A.weakenWithLHS primalLHS)
    --                                       (dualLambda (lookupLambdaLabs ctx'1 fvlabs))))

    --     DualResult (ABuilder ctx1 f1) stores1 cmap1 <- dual ctx'2 arg1
    --     return $ DualResult
    --         (ABuilder ctx1
    --             (Alet (LeftHandSideSingle undefined)
    --                   (smartFstA (Scan' (nilLabel undefined)
    --                                     A.LeftToRight
    --                                     (resolveAlabsFun ctx combfun)
    --                                     (resolveAlabs ctx initexp)
    --                                     (avars (resolveEnvLabs ctx (findPrimalBMap ctx (alabelOf arg1))))))
    --              . Alet (LeftHandSidePair (LeftHandSideSingle undefined) (LeftHandSideSingle iaarrty))
    --                     (Alet (LeftHandSideSingle undefined)
    --                           (ZipWith (nilLabel undefined)
    --                                    (ELPlain (Lam primalLHS (Body (Let dualLHS primalBody dualBody))))
    --                                    (smartAvar (A.Var undefined ZeroIdx))
    --                                    (avars (resolveEnvLabs ctx'1 (findPrimalBMap ctx'1 (alabelOf arg1)))))
    --                           (let var = smartAvar (A.Var undefined ZeroIdx)
    --                            in smartApair (mapFst var) (mapSnd var)))
    --              . Alet (LeftHandSideSingle undefined)
    --                     (ZipWith undefined  -- multiply?
    --                              )
    --              . f1))
    --         stores1  -- don't need to store this node
    --         (cmap1 `unionCMap` indexingContributions envlab3 idxInsts)

    Fold _ _ _ _ -> error "AD: Fold currently unsupported"

    Sum lab arg1 -> do
        ReplicateOneMore slixType slixExpGen <- return (replicateOneMore (arrayRshape (labelType lab)))
        let adjointLabs = findAdjointBMap ctx lab
            adjoint = avars (resolveEnvLabs ctx adjointLabs)
            pvar = resolveEnvLab ctx (untupleA (findPrimalBMap ctx (alabelOf arg1)))
        envlab1 <- genSingleId (atypeOf1 arg1)
        let ctx' = ctxPushS (fmapLabel D (alabelOf1 arg1)) envlab1 ctx
        DualResult (ABuilder ctx1 f1) stores1 compd1 cmap1 <- dual ctx' arg1
        traceM (unlines ["!dual Sum[" ++ showDLabel lab ++ "]:"
                        ,"  adjointLabs = " ++ showTupR showDLabel adjointLabs
                        ,"  envlab1 = " ++ showDLabel envlab1 ++ "  (adjoint of node " ++ showDLabel (alabelOf arg1) ++ ")"
                        ,"  stores = " ++ show stores1
                        ,"  computed = " ++ show (Some envlab1 : compd1)
                        ,"  out cmap = " ++ showCMap cmap1
                        ])
        return $ DualResult
            (ABuilder ctx1 (Alet (LeftHandSideSingle (atypeOf1 arg1))
                                 (Replicate (nilLabel (atypeOf1 arg1))
                                            slixType
                                            (slixExpGen (smartShape pvar))
                                            adjoint)
                            . f1))
            stores1  -- don't need to store this node
            (Some envlab1 : compd1)
            cmap1

    Replicate lab slixspec _ arg1 -> do
        let adjointLabs = findAdjointBMap ctx lab
            adjoint = avars (resolveEnvLabs ctx adjointLabs)
            argty@(ArrayR _ eltty) = atypeOf1 arg1
        envlab1 <- genSingleId argty
        let ctx' = ctxPushS (fmapLabel D (alabelOf1 arg1)) envlab1 ctx
        DualResult (ABuilder ctx1 f1) stores1 compd1 cmap1 <- dual ctx' arg1
        return $ DualResult
            (ABuilder ctx1 (Alet (LeftHandSideSingle argty)
                                 (Reduce (nilLabel (atypeOf1 arg1))
                                         (reduceSpecFromReplicate slixspec)
                                         (plusLam eltty)
                                         adjoint)
                            . f1))
            stores1  -- don't need to store this node
            (Some envlab1 : compd1)
            cmap1

    Slice lab slixspec arg1 slexp -> do
        let adjointLabs = findAdjointBMap ctx lab
            adjointVar = resolveEnvLab ctx (untupleA adjointLabs)
            argty = atypeOf1 arg1
            argpvar = resolveEnvLab ctx (untupleA (findPrimalBMap ctx (alabelOf arg1)))
        envlab1 <- genSingleId argty
        let ctx' = ctxPushS (fmapLabel D (alabelOf1 arg1)) envlab1 ctx
        DualResult (ABuilder ctx1 f1) stores1 compd1 cmap1 <- dual ctx' arg1
        return $ DualResult
            (ABuilder ctx1 (Alet (LeftHandSideSingle argty)
                                 (Generate (nilLabel argty)
                                           (smartShape argpvar)
                                           (ELPlain (sliceDualLambda slixspec adjointVar (resolveAlabs ctx slexp))))
                            . f1))
            stores1  -- don't need to store this node
            (Some envlab1 : compd1)
            cmap1

    Reshape lab _ arg1 -> do
        let adjointLabs = findAdjointBMap ctx lab
            adjoint = avars (resolveEnvLabs ctx adjointLabs)
            argty = atypeOf1 arg1
            argpvar = resolveEnvLab ctx (untupleA (findPrimalBMap ctx (alabelOf arg1)))
        envlab1 <- genSingleId argty
        let ctx' = ctxPushS (fmapLabel D (alabelOf1 arg1)) envlab1 ctx
        DualResult (ABuilder ctx1 f1) stores1 compd1 cmap1 <- dual ctx' arg1
        return $ DualResult
            (ABuilder ctx1 (Alet (LeftHandSideSingle argty)
                                 (Reshape (nilLabel argty) (smartShape argpvar) adjoint)
                            . f1))
            stores1  -- don't need to store this node
            (Some envlab1 : compd1)
            cmap1

    Backpermute lab _ (Lam funLHS (Body funBody)) arg1 -> do
        let adjointLabs = findAdjointBMap ctx lab
            adjoint = avars (resolveEnvLabs ctx adjointLabs)
            argty@(ArrayR _ eltty) = atypeOf1 arg1
            argpvar = resolveEnvLab ctx (untupleA (findPrimalBMap ctx (alabelOf arg1)))
        envlab1 <- genSingleId argty
        let ctx' = ctxPushS (fmapLabel D (alabelOf1 arg1)) envlab1 ctx
        DualResult (ABuilder ctx1 f1) stores1 compd1 cmap1 <- dual ctx' arg1
        return $ DualResult
            (ABuilder ctx1 (Alet (LeftHandSideSingle argty)
                                 (Permute (nilLabel (atypeOf1 arg1))
                                          (plusLam eltty)
                                          (generateConstantArray (atypeOf1 arg1) (smartShape argpvar))
                                          (Lam funLHS (Body (mkJust (resolveAlabs ctx funBody))))
                                          adjoint)
                            . f1))
            stores1  -- don't need to store this node
            (Some envlab1 : compd1)
            cmap1

    Aget lab tidx arg1 -> do
        let adjointLabs = findAdjointBMap ctx lab
            adjoint = avars (resolveEnvLabs ctx adjointLabs)
            argty = atypeOf arg1
            argpvars = resolveEnvLabs ctx (findPrimalBMap ctx (alabelOf arg1))
        (Exists envlhs, envlabs1) <- genSingleIds argty
        let ctx' = ctxPush envlhs (fmapLabel D (alabelOf arg1)) envlabs1 ctx
        DualResult (ABuilder ctx1 f1) stores1 compd1 cmap1 <- dual ctx' arg1
        return $ DualResult
            (ABuilder ctx1 (Alet envlhs
                                 (oneHotTup argty tidx argpvars adjoint)
                            . f1))
            stores1  -- don't need to store this node
            (enumerateTupR envlabs1 ++ compd1)
            cmap1

    Alet _ arg1 arg2 -> do
        -- The parent has already stored the adjoint for the body, so we can
        -- directly traverse it.
        DualResult (ABuilder ctx2 f2) stores2 compd2 cmap2 <- dual ctx arg2
        -- Now we need to collect the contributions to the RHS, and traverse it
        -- with (a promise of) its adjoint stored in the context.
        (Exists lhs, envlabs) <- genSingleIds (atypeOf arg1)
        let ctx' = ctxPush lhs (fmapLabel D (alabelOf arg1)) envlabs ctx2
            pvars = resolveEnvLabs ctx2 (findPrimalBMap ctx2 (alabelOf arg1))
            (rhsAdjoint, cmap2') = collectAdjointCMap cmap2 (Local (alabelOf arg1)) pvars ctx2
        DualResult (ABuilder ctx1 f1) stores1 compd1 cmap1 <- dual ctx' arg1
        traceM (unlines ["!dual Let[let " ++ showDLabel (alabelOf arg1) ++ " in " ++ showDLabel (alabelOf arg2) ++ "]:"
                        ,"  envlabs = " ++ showTupR showDLabel envlabs
                        ,"  cmap2 ! " ++ show (labelLabel (alabelOf arg1)) ++ " has " ++ show (maybe 0 (\(AdjList f) -> length (f ctx')) (DMap.lookup (Local (alabelOf arg1)) cmap2)) ++ " entries"
                        ,"  stores = " ++ show (stores1 ++ stores2)
                        ,"  computed = " ++ show (compd2 ++ enumerateTupR envlabs ++ compd1)
                        ,"  out cmap = " ++ showCMap (cmap1 `unionCMap` cmap2')
                        ])
        return $ DualResult
            (ABuilder ctx1 (f2 . Alet lhs rhsAdjoint . f1))
            (stores1 ++ stores2)  -- don't need to store the right-hand side's adjoint
            (compd2 ++ enumerateTupR envlabs ++ compd1)
            (cmap1 `unionCMap` cmap2')

    Avar lab _ (PartLabel referLab referPart) -> do
        let adjointLabs = findAdjointBMap ctx lab
            cmap = DMap.singleton (Local referLab) (AdjList (\ctx' ->
                      -- Re-lookup the env labels, in case the bindmap changed. I
                      -- don't think that can ever happen, but let's be robust.
                      let adjointLabs' = findAdjointBMap ctx' lab
                          adjoint = avars (resolveEnvLabs ctx' adjointLabs')
                          pvars = resolveEnvLabs ctx' (findPrimalBMap ctx' referLab)
                      in [oneHotTup (labelType referLab) referPart pvars adjoint]))
        traceM (unlines ["!dual Avar[" ++ showDLabel lab ++ "]:"
                        ,"  adjointLabs = stores = " ++ showTupR showDLabel adjointLabs
                        ,"  out cmap = " ++ showCMap cmap
                        ])
        return $ DualResult
            (ABuilder ctx id)
            (enumerateTupR adjointLabs)  -- Store this node! We need to keep the contribution around.
            []                           -- But note that we didn't actually _compute_ anything.
            cmap

    Aarg lab argsty tidx -> do
        let adjointLabs = findAdjointBMap ctx lab
            cmap = DMap.singleton (Argument argsty) (AdjList (\ctx' ->
                      -- Re-lookup the env labels, in case the bindmap changed. I
                      -- don't think that can ever happen, but let's be robust.
                      let adjointLabs' = findAdjointBMap ctx' lab
                          adjoint = avars (resolveEnvLabs ctx' adjointLabs')
                          pvars = resolveEnvLabs ctx' (findArgumentPrimalBMap ctx' argsty)
                      in [oneHotTup argsty tidx pvars adjoint]))
        traceM (unlines ["!dual Aarg[" ++ showDLabel lab ++ "]:"
                        ,"  adjointLabs = stores = " ++ showTupR showDLabel adjointLabs
                        ,"  out cmap = " ++ showCMap cmap
                        ])
        return $ DualResult
            (ABuilder ctx id)
            (enumerateTupR adjointLabs)  -- Store this node! We need to keep the contribution around.
            []                           -- But note that we didn't actually _compute_ anything.
            cmap

    Scan _ _ _ _ _ -> error "AD: Scan currently unsupported"
    Scan' _ _ _ _ _ -> error "AD: Scan' currently unsupported"
    Reduce _ _ _ _ -> error "AD: Reduce currently unsupported"
    Permute _ _ _ _ _ -> error "AD: Permute currently unsupported"

    _ -> undefined

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
collectAdjointCMap contribmap key pvars =
    case DMap.lookup key contribmap of
        Just (AdjList listgen) -> (, DMap.delete key contribmap) . arraysSum (cmapKeyType key) pvars . listgen
        Nothing -> -- if there are no contributions, well, the adjoint is an empty sum (i.e. zero)
                   const (arraysSum (cmapKeyType key) pvars [], contribmap)

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
arrayPlus a1 a2
  | TupRsingle arrty@(ArrayR _ ty) <- atypeOf a1
  , Lam lhs1 (Lam lhs2 body) <- plusLam ty
  = ZipWith (nilLabel arrty) (ELPlain (Lam (LeftHandSidePair lhs1 lhs2) body)) a1 a2
arrayPlus _ _ = error "unreachable"

arraysSum :: ArraysR t
          -> A.ArrayVars aenv t  -- primal result
          -> [OpenAcc aenv () () args t]
          -> OpenAcc aenv () () args t
arraysSum TupRunit TupRunit _ = Anil (nilLabel TupRunit)
arraysSum (TupRsingle ty@(ArrayR sht _)) (TupRsingle pvar) [] =
    generateConstantArray ty (Shape (nilLabel (shapeType sht)) (Left pvar))
arraysSum ty@(TupRpair t1 t2) (TupRpair pvars1 pvars2) [] =
    Apair (nilLabel ty) (arraysSum t1 pvars1 []) (arraysSum t2 pvars2 [])
arraysSum ty _ l = foldl1 (tupleZipAcc' ty (const arrayPlus) (\_ _ -> False)) l

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

-- -- Returns the parent _node_ labels of the expression; if an expression only
-- -- refers to a part of a node, the whole node is included in the list.
-- expAParents :: OpenExp env aenv lab alab args tenv t -> [AAnyLabelN alab]
-- expAParents e = [AnyLabel lab | Some (AnyPartLabel (PartLabel lab _)) <- expALabels e]

-- -- Returns the parent _node_ labels of the function; if an expression only
-- -- refers to a part of a node, the whole node is included in the list.
-- funAParents :: OpenFun env aenv lab alab tenv t -> [AAnyLabelN alab]
-- funAParents fun = [AnyLabel lab | Some (AnyPartLabel (PartLabel lab _)) <- expFunALabels fun]

-- -- Returns the parent _node_ labels of the lambda; if an expression only
-- -- refers to a part of a node, the whole node is included in the list.
-- lamAParents :: ExpLambda1 aenv lab alab tenv sh t1 t2 -> [AAnyLabelN alab]
-- lamAParents (ELSplit (SplitLambdaAD _ _ fvtup _ _ instMap) _) =
--     [AnyLabel lab | Some (AnyPartLabel (PartLabel lab _)) <- enumerateTupR fvtup ++ DMap.keys instMap]
-- lamAParents (ELPlain fun) = funAParents fun

resolveAlabs :: HasCallStack
             => AContext Int aenv
             -> OpenExp env aenv' lab Int args tenv t
             -> OpenExp env aenv lab alab' args tenv t
resolveAlabs ctx ex =
    inlineAvarLabels'
        (\(AnyPartLabel (PartLabel lab tidx)) ->
            untupleA (pickTupR tidx (resolveEnvLabs ctx (findPrimalBMap ctx lab))))
        ex

-- TODO: apply this trick in more places where we _know_ it's not a tuple based on the type information
untupleA :: TupR s (Array sh t) -> s (Array sh t)
untupleA (TupRsingle x) = x

resolveAlabsFun :: HasCallStack
                => AContext Int aenv
                -> OpenFun env aenv' lab Int tenv t
                -> OpenFun env aenv lab alab' tenv t
resolveAlabsFun ctx (Lam lhs fun) = Lam lhs (resolveAlabsFun ctx fun)
resolveAlabsFun ctx (Body ex) = Body (resolveAlabs ctx ex)

-- Data.Some (Some) is not like this because it's a newtype for performance.
data Some' f = forall a. Some' (f a)
gadtSome :: Some f -> Some' f
gadtSome (Some x) = Some' x
returnSome :: Applicative m => Some f -> m (Some' f)
returnSome = pure . gadtSome
