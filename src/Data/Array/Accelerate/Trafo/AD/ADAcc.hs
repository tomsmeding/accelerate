{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Data.Array.Accelerate.Trafo.AD.ADAcc (
  reverseADA, ReverseADResA(..)
) where

import Data.List (intercalate, sortOn)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Map (DMap)
import Data.Dependent.Sum
import Data.Some (pattern Some)
import Data.Type.Equality
import Data.GADT.Compare (GCompare)

import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Environment as A
import qualified Data.Array.Accelerate.AST.Idx as A
import qualified Data.Array.Accelerate.AST.LeftHandSide as A
import Data.Array.Accelerate.AST.LeftHandSide (Exists(..))
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
import Data.Array.Accelerate.Trafo.AD.Algorithms
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

genIds :: ArraysR t -> IdGen (Exists (A.ALeftHandSide t env), TupR (ADLabelNS Int) t)
genIds TupRunit = return (Exists (A.LeftHandSideWildcard TupRunit), TupRunit)
genIds (TupRsingle ty) = (Exists (A.LeftHandSideSingle ty),) . TupRsingle <$> genIdNodeSingle ty
genIds (TupRpair t1 t2) = do
    (Exists lhs1, ids1) <- genIds t1
    (Exists lhs2, ids2) <- genIds t2
    return (Exists (A.LeftHandSidePair lhs1 lhs2), TupRpair ids1 ids2)

genSingleId :: ArrayR t -> IdGen (ADLabel Int t)
genSingleId = genId'

genSingleIds :: ArraysR t -> IdGen (Exists (A.ALeftHandSide t aenv), TupR (ADLabel Int) t)
genSingleIds TupRunit = return (Exists (A.LeftHandSideWildcard TupRunit), TupRunit)
genSingleIds (TupRsingle ty) = (Exists (A.LeftHandSideSingle ty),) . TupRsingle <$> genSingleId ty
genSingleIds (TupRpair t1 t2) = do
    (Exists lhs1, ids1) <- genSingleIds t1
    (Exists lhs2, ids2) <- genSingleIds t2
    return (Exists (A.LeftHandSidePair lhs1 lhs2), TupRpair ids1 ids2)


-- TODO: make this a data definition, not a tuple
type Exploded lab alab args res = (ADLabelN alab res, DMap (ADLabelN alab) (Acc lab alab args), DMap (A.Idx args) (ADLabelN alab))

showExploded :: (Ord alab, Show lab, Show alab) => Exploded lab alab args t -> String
showExploded (endlab, nodemap, argmap) =
    "(" ++ showDLabel endlab ++ ", " ++ showNodemap nodemap ++ ", " ++ showArgmap argmap ++ ")"

showNodemap :: (Ord alab, Show lab, Show alab) => DMap (ADLabelN alab) (Acc lab alab args) -> String
showNodemap nodemap =
    let tups = sortOn fst [(lab, (showDLabel dlab, show expr))
                          | dlab@(DLabel _ lab) :=> expr <- DMap.assocs nodemap]
        s = intercalate ", " ["(" ++ dlabshow ++ ") :=> " ++ exprshow
                             | (_, (dlabshow, exprshow)) <- tups]
    in "[" ++ s ++ "]"

showArgmap :: Show alab => DMap (A.Idx args) (ADLabelN alab) -> String
showArgmap argmap =
    let s = intercalate ", " ['A' : show (A.idxToInt argidx) ++ " :=> " ++ showDLabel dlab
                             | argidx :=> dlab <- DMap.assocs argmap]
    in "[" ++ s ++ "]"

-- Assumes the expression does not contain Arg
generaliseArgs :: HasCallStack => OpenAcc aenv lab alab args t -> OpenAcc aenv lab alab args' t
generaliseArgs (Aconst ty x) = Aconst ty x
generaliseArgs (Apair ty e1 e2) = Apair ty (generaliseArgs e1) (generaliseArgs e2)
generaliseArgs Anil = Anil
generaliseArgs (Acond ty e1 e2 e3) = Acond ty e1 (generaliseArgs e2) (generaliseArgs e3)
generaliseArgs (Map ty f e) = Map ty f (generaliseArgs e)
generaliseArgs (ZipWith ty f e1 e2) = ZipWith ty f (generaliseArgs e1) (generaliseArgs e2)
generaliseArgs (Fold ty f me0 a) = Fold ty f me0 (generaliseArgs a)
generaliseArgs (Scan ty dir f me0 a) = Scan ty dir f me0 (generaliseArgs a)
generaliseArgs (Scan' ty dir f e0 a) = Scan' ty dir f e0 (generaliseArgs a)
generaliseArgs (Backpermute ty dim f e) = Backpermute ty dim f (generaliseArgs e)
generaliseArgs (Replicate ty sht she e) = Replicate ty sht she (generaliseArgs e)
generaliseArgs (Slice ty sht e she) = Slice ty sht (generaliseArgs e) she
generaliseArgs (Reduce sht she f e) = Reduce sht she f (generaliseArgs e)
generaliseArgs (Reshape ty she e) = Reshape ty she (generaliseArgs e)
generaliseArgs (Sum ty a) = Sum ty (generaliseArgs a)
generaliseArgs (Generate ty she f) = Generate ty she f
generaliseArgs (Permute ty cf e1 pf e2) = Permute ty cf (generaliseArgs e1) pf (generaliseArgs e2)
generaliseArgs (Aget ty path ex) = Aget ty path (generaliseArgs ex)
generaliseArgs (Alet lhs rhs ex) = Alet lhs (generaliseArgs rhs) (generaliseArgs ex)
generaliseArgs (Avar v) = Avar v
generaliseArgs (Aarg _ _) = error "generaliseArgs: Arg found"
generaliseArgs (Alabel labs) = Alabel labs

data ReverseADResA t = forall aenv. ReverseADResA (A.ALeftHandSide t () aenv) (OpenAcc aenv (PDExp Int) (PDAcc Int) () t)

-- TODO: see the argument as one (1) tuple-typed variable of which the adjoint is requested. This should simplify this code a lot.
-- Action plan:
-- - 'expr' should be prefixed with a Let binding over that LHS, with Arg's as
--   right-hand sides. This is then a closed expression, which can be passed to
--   'explode' as usual.
--   - Arg is a new expression node type that models arguments with respect to
--     which we are differentiating. They get a type-level index into the
--     top-level LHS here.
-- - The rest of the computation considers Arg values constants (and so the
--   Const case in dual' can really ignore Const!).
-- - In the end, do a pass over the tree which FICTIONALLY adds a LHS at the
--   top, but really just shifts the environment. It should replace the Arg
--   values with references to this extended part of the environment. The real
--   LHS needs to be added by surrounding code.
reverseADA :: A.ALeftHandSide t () aenv -> OpenAcc aenv unused1 unused2 () (Array () Float) -> ReverseADResA t
reverseADA paramlhs expr
  | ExpandLHS paramlhs' paramWeaken <- expandLHS paramlhs
  , DeclareVars paramlhs'2 _ varsgen <- declareVars (A.lhsToTupR paramlhs)
  , Refl <- sameLHSsameEnv paramlhs' paramlhs'2 =
      let argsRHS = varsToArgs (varsgen A.weakenId)
          closedExpr = Alet paramlhs' argsRHS (generaliseArgs (sinkAcc paramWeaken expr))
          transformedExp = evalIdGen $ do
              exploded@(_, _, argLabelMap) <- explode LEmpty closedExpr
              traceM ("acc exploded: " ++ showExploded exploded)
              primaldual exploded $ \context ->
                  -- 'argsRHS' is an expression of type 't', and is a simple tuple expression
                  -- containing only Arg (and Pair/Nil) nodes. Since 't' is also exactly the
                  -- type of the gradient that we must produce here, we can transform
                  -- 'argsRHS' to our wishes.
                  -- These Arg nodes we can look up in argLabelMap to produce a DLabel, which
                  -- can on their turn be looked up in 'labelenv' using 'labValFind'. The
                  -- lookup produces an Idx, which, put in a Var, should replace the Arg in
                  -- 'argsRHS'.
                  trace ("\nacc context in core: " ++ showContext context) $
                  return $ produceGradient argLabelMap context argsRHS
      in
          trace ("Acc AD result: " ++ prettyPrint transformedExp) $
          ReverseADResA paramlhs' (realiseArgs transformedExp paramlhs')
  where
    varsToArgs :: A.ArrayVars aenv t -> OpenAcc aenv' lab alab aenv t
    varsToArgs TupRunit = Anil
    varsToArgs (TupRsingle (A.Var ty idx)) = Aarg ty idx
    varsToArgs (TupRpair vars1 vars2) =
      let ex1 = varsToArgs vars1
          ex2 = varsToArgs vars2
      in Apair (TupRpair (atypeOf ex1) (atypeOf ex2)) ex1 ex2

    -- TODO: produceGradient should take the ArrayVars value from BEFORE
    -- varsToArgs, not after. That eliminates the error case if the argument is
    -- not Nil/Pair/Arg.
    produceGradient :: DMap (Idx args) (ADLabelN Int)
                    -> AContext Int aenv
                    -> OpenAcc () unused1 unused2 args t
                    -> OpenAcc aenv unused3 (PDAcc Int) args' t
    produceGradient argLabelMap context@(Context labelenv bindmap) argstup = case argstup of
        Anil -> Anil
        Apair ty e1 e2 -> Apair ty (produceGradient argLabelMap context e1)
                                   (produceGradient argLabelMap context e2)
        Aarg ty idx
          | Just lab <- DMap.lookup idx argLabelMap
          , Just labs <- DMap.lookup (fmapLabel D lab) bindmap
          , Just vars <- alabValFinds labelenv labs
              -> avars vars
          | otherwise
              -> error $ "produceGradient: Adjoint of Arg (" ++ show ty ++ ") " ++
                            'A' : show (A.idxToInt idx) ++ " not computed"
        _ -> error "produceGradient: what?"

-- Produces an expression that can be put under a LHS that binds exactly the
-- 'args' of the original expression.
realiseArgs :: OpenAcc () lab alab args res -> A.ALeftHandSide t () args -> OpenAcc args lab alab () res
realiseArgs = \expr lhs -> go A.weakenId (A.weakenWithLHS lhs) expr
  where
    go :: args A.:> aenv' -> aenv A.:> aenv' -> OpenAcc aenv lab alab args res -> OpenAcc aenv' lab alab () res
    go argWeaken varWeaken expr = case expr of
        Aconst ty x -> Aconst ty x
        Apair ty e1 e2 -> Apair ty (go argWeaken varWeaken e1) (go argWeaken varWeaken e2)
        Anil -> Anil
        Acond ty e1 e2 e3 -> Acond ty (sinkExpAenv varWeaken e1) (go argWeaken varWeaken e2) (go argWeaken varWeaken e3)
        Map ty f e -> Map ty (fmapPlain (sinkFunAenv varWeaken) f) (go argWeaken varWeaken e)
        ZipWith ty f e1 e2 -> ZipWith ty (fmapPlain (sinkFunAenv varWeaken) f) (go argWeaken varWeaken e1) (go argWeaken varWeaken e2)
        Fold ty f me0 e -> Fold ty (sinkFunAenv varWeaken f) (sinkExpAenv varWeaken <$> me0) (go argWeaken varWeaken e)
        Scan ty dir f me0 e -> Scan ty dir (sinkFunAenv varWeaken f) (sinkExpAenv varWeaken <$> me0) (go argWeaken varWeaken e)
        Scan' ty dir f e0 e -> Scan' ty dir (sinkFunAenv varWeaken f) (sinkExpAenv varWeaken e0) (go argWeaken varWeaken e)
        Backpermute ty dim f e -> Backpermute ty (sinkExpAenv varWeaken dim) (sinkFunAenv varWeaken f) (go argWeaken varWeaken e)
        Permute ty cf def pf e -> Permute ty (sinkFunAenv varWeaken cf) (go argWeaken varWeaken def) (sinkFunAenv varWeaken pf) (go argWeaken varWeaken e)
        Sum ty e -> Sum ty (go argWeaken varWeaken e)
        Generate ty she f -> Generate ty (sinkExpAenv varWeaken she) (fmapPlain (sinkFunAenv varWeaken) f)
        Replicate ty slt sle e -> Replicate ty slt (sinkExpAenv varWeaken sle) (go argWeaken varWeaken e)
        Slice ty slt e sle -> Slice ty slt (go argWeaken varWeaken e) (sinkExpAenv varWeaken sle)
        Reduce ty slt f e -> Reduce ty slt (sinkFunAenv varWeaken f) (go argWeaken varWeaken e)
        Reshape ty she e -> Reshape ty (sinkExpAenv varWeaken she) (go argWeaken varWeaken e)
        Aget ty tidx ex -> Aget ty tidx (go argWeaken varWeaken ex)
        Alet lhs rhs ex
          | A.Exists lhs' <- rebuildLHS lhs ->
              Alet lhs' (go argWeaken varWeaken rhs)
                  (go (A.weakenWithLHS lhs' A..> argWeaken) (A.sinkWithLHS lhs lhs' varWeaken) ex)
        Avar (A.Var ty idx) -> Avar (A.Var ty (varWeaken A.>:> idx))
        Aarg ty@ArrayR{} idx -> Avar (A.Var ty (argWeaken A.>:> idx))
        Alabel _ -> error "realiseArgs: unexpected Label"

-- Map will NOT contain Let or Var. Note that it may contain Label due to Let-bindings.
explode :: LabVal NodeLabel ArrayR Int aenv -> OpenAcc aenv unused1 unused2 args t -> IdGen (Exploded (PDExp Int) Int args t)
explode labelenv e =
    trace ("acc explode: exploding " ++ showsAcc (ShowEnv (const "L?") (const "AL?") 0 () []) 9 e "") $
    explode' labelenv e

-- As for expressions, the LabVal here contains node labels which happen to be
-- single-array typed. These labels end up in labelised expressions, which is
-- the reason why array labels in expressions need to go through the bindmap
-- before looking them up.
explode' :: LabVal NodeLabel ArrayR Int aenv -> OpenAcc aenv unused1 unused2 args t -> IdGen (Exploded (PDExp Int) Int args t)
explode' labelenv = \case
    e | trace ("acc explode': | " ++ showsAcc (ShowEnv (const "L?") (const "AL?") 0 () ['t' : show i | i <- [1::Int ..]]) 0 e "" ++ "   labelenv = " ++ showLabelenv labelenv) False -> undefined
    Aconst ty x -> do
        lab <- genId (TupRsingle ty)
        return (lab, DMap.singleton lab (Aconst ty x), mempty)
    Apair ty e1 e2 -> do
        (lab1, mp1, argmp1) <- explode' labelenv e1
        (lab2, mp2, argmp2) <- explode' labelenv e2
        lab <- genId ty
        let pruned = Apair ty (Alabel lab1) (Alabel lab2)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mp2, itemmp]
            argmp = DMap.unionWithKey (error "explode: Overlapping arg's") argmp1 argmp2
        return (lab, mp, argmp)
    Anil -> do
        lab <- genId TupRunit
        return (lab, DMap.singleton lab Anil, mempty)
    Acond ty e e1 e2 -> do
        let e' = snd . labeliseExpA labelenv . generaliseLabA . generaliseLab $ e
        (lab1, mp1, argmp1) <- explode' labelenv e1
        (lab2, mp2, argmp2) <- explode' labelenv e2
        lab <- genId ty
        let pruned = Acond ty e' (Alabel lab1) (Alabel lab2)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mp2, itemmp]
            argmp = DMap.unionsWithKey (error "explode: Overlapping arg's") [argmp1, argmp2]
        return (lab, mp, argmp)
    Map ty@(ArrayR sht _) (ELPlain e) a
      | SomeSplitLambdaAD e'@(SplitLambdaAD _ _ _ tmpty _ _) <- splitLambdaAD labelenv (generaliseLabFun e)
      -> do
        tmplab <- genSingleId (ArrayR sht tmpty)
        (lab1, mp1, argmp1) <- explode' labelenv a
        lab <- genId (TupRsingle ty)
        let pruned = Map ty (ELSplit e' tmplab) (Alabel lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    Map _ ELSplit{} _ -> error "explode: Unexpected Map SplitLambdaAD"
    ZipWith ty@(ArrayR sht _) (ELPlain e) a1 a2
      | SomeSplitLambdaAD e'@(SplitLambdaAD _ _ _ tmpty _ _) <- splitLambdaAD labelenv (generaliseLabFun e)
      -> do
        tmplab <- genSingleId (ArrayR sht tmpty)
        (lab1, mp1, argmp1) <- explode' labelenv a1
        (lab2, mp2, argmp2) <- explode' labelenv a2
        lab <- genId (TupRsingle ty)
        let pruned = ZipWith ty (ELSplit e' tmplab) (Alabel lab1) (Alabel lab2)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mp2, itemmp]
            argmp = DMap.unionsWithKey (error "explode: Overlapping arg's") [argmp1, argmp2]
        return (lab, mp, argmp)
    ZipWith _ ELSplit{} _ _ -> error "explode: Unexpected ZipWith SplitLambdaAD"
    Fold ty e me0 a -> do
        -- TODO: This does NOT split the lambda in Fold. This is because
        -- currently, we do recompute-all for the Fold lambda, not store-all;
        -- this is not because we can't, but because I haven't implemented that
        -- yet. Also I think it may be better to not do it at all anyway.
        let e' = snd . labeliseFunA labelenv . generaliseLabFunA . generaliseLabFun $ e
            me0' = snd . labeliseExpA labelenv . generaliseLabA . generaliseLab <$> me0
        (lab1, mp1, argmp1) <- explode' labelenv a
        lab <- genId (TupRsingle ty)
        let pruned = Fold ty e' me0' (Alabel lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    Backpermute ty dim f a -> do
        let f' = snd . labeliseFunA labelenv . generaliseLabFunA . generaliseLabFun $ f
            dim' = snd . labeliseExpA labelenv . generaliseLabA . generaliseLab $ dim
        (lab1, mp1, argmp1) <- explode' labelenv a
        lab <- genId (TupRsingle ty)
        let pruned = Backpermute ty dim' f' (Alabel lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    Sum ty a -> do
        (lab1, mp1, argmp1) <- explode' labelenv a
        lab <- genId (TupRsingle ty)
        let pruned = Sum ty (Alabel lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    Generate ty@(ArrayR sht _) she (ELPlain f)
      | SomeSplitLambdaAD f'@(SplitLambdaAD _ _ _ tmpty _ _) <- splitLambdaAD labelenv (generaliseLabFun f)
      -> do
        tmplab <- genSingleId (ArrayR sht tmpty)
        let she' = snd . labeliseExpA labelenv . generaliseLabA . generaliseLab $ she
        lab <- genId (TupRsingle ty)
        let pruned = Generate ty she' (ELSplit f' tmplab)
        let itemmp = DMap.singleton lab pruned
        return (lab, itemmp, DMap.empty)
    Generate _ _ ELSplit{} -> error "explode: Unexpected Generate SplitLambdaAD"
    Replicate ty slt she a -> do
        let she' = snd . labeliseExpA labelenv . generaliseLabA . generaliseLab $ she
        (lab1, mp1, argmp1) <- explode' labelenv a
        lab <- genId (TupRsingle ty)
        let pruned = Replicate ty slt she' (Alabel lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    Slice ty slt a she -> do
        let she' = snd . labeliseExpA labelenv . generaliseLabA . generaliseLab $ she
        (lab1, mp1, argmp1) <- explode' labelenv a
        lab <- genId (TupRsingle ty)
        let pruned = Slice ty slt (Alabel lab1) she'
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    Reshape ty she a -> do
        let she' = snd . labeliseExpA labelenv . generaliseLabA . generaliseLab $ she
        (lab1, mp1, argmp1) <- explode' labelenv a
        lab <- genId (TupRsingle ty)
        let pruned = Reshape ty she' (Alabel lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    Alet lhs rhs body -> do
        (lab1, mp1, argmp1) <- explode' labelenv rhs
        (_, labs) <- genIds (atypeOf rhs)
        let (env', mpLHS) = lpushLHS_Get lhs labs labelenv (Alabel lab1)
        (lab2, mp2, argmp2) <- explode' env' body
        let mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mpLHS, mp2]
            argmp = DMap.unionWithKey (error "explode: Overlapping arg's") argmp1 argmp2
        return (lab2, mp, argmp)
    Avar (A.Var _ idx) -> do
        return (tupleLabel (prjL idx labelenv), mempty, mempty)
    Aarg ty idx -> do
        lab <- genId (TupRsingle ty)
        return (lab, DMap.singleton lab (Aarg ty idx), DMap.singleton idx lab)
    Aget _ _ _ -> error "explode: Unexpected Aget"
    Alabel _ -> error "explode: Unexpected Alabel"
    Reduce _ _ _ _ -> error "explode: Unexpected Reduce, should only be created in dual"
    Permute _ _ _ _ _ -> error "explode: Unexpected Permute, can't do AD on Permute yet"
    Scan _ _ _ _ _ -> error "explode: Unexpected Scan, can't do AD on Scan yet"
    Scan' _ _ _ _ _ -> error "explode: Unexpected Scan', can't do AD on Scan' yet"
  where
    lpushLHS_Get :: A.ALeftHandSide t aenv aenv' -> TupR (ADLabelNS Int) t -> LabVal NodeLabel ArrayR Int aenv -> Acc lab Int args t -> (LabVal NodeLabel ArrayR Int aenv', DMap (ADLabelN Int) (Acc lab Int args))
    lpushLHS_Get lhs labs labelenv' rhs = case (lhs, labs) of
        (A.LeftHandSidePair lhs1 lhs2, TupRpair labs1 labs2) ->
            let (labelenv1, mp1) = lpushLHS_Get lhs1 labs1 labelenv' (smartFstA rhs)
                (labelenv2, mp2) = lpushLHS_Get lhs2 labs2 labelenv1 (smartSndA rhs)
            in (labelenv2, DMap.unionWithKey (error "lpushLHS_Get: Overlapping id's") mp1 mp2)
        (A.LeftHandSideSingle _, TupRsingle lab) -> (LPush labelenv' lab, DMap.singleton (tupleLabel lab) rhs)
        (A.LeftHandSideWildcard _, _) -> (labelenv', mempty)
        _ -> error "lpushLHS_Get: impossible GADTs"

computeLabelorder :: Exploded (PDExp Int) Int args t -> [AAnyLabelN Int]
computeLabelorder exploded@(endlab, nodemap, _) =
    topsort' (\(AnyLabel l) -> labelLabel l)
             alllabels
             (\(AnyLabel l) -> parentmap Map.! labelLabel l)
  where
    parentsOf :: AAnyLabelN Int -> [AAnyLabelN Int]
    parentsOf (AnyLabel lbl) = accLabelParents (nodemap `dmapFind` lbl)

    -- Add the labels corresponding to argument nodes if they're not already
    -- found by the floodfill. If an argument is unused, we still want to visit
    -- it (if only to store 0 for the adjoint because there are no
    -- contributions).
    alllabels :: [AAnyLabelN Int]
    alllabels = Set.toList $ floodfill (AnyLabel endlab) parentsOf mempty <> collectArgLabels exploded

    parentmap :: Map Int [AAnyLabelN Int]
    parentmap = Map.fromList [(labelLabel numlbl, parentsOf l)
                             | l@(AnyLabel numlbl) <- alllabels]

primaldual :: Exploded (PDExp Int) Int args (Array () Float)
           -> (forall aenv. AContext Int aenv -> IdGen (OpenAcc aenv (PDExp Int) (PDAcc Int) args t))
           -> IdGen (Acc (PDExp Int) (PDAcc Int) args t)
primaldual exploded cont =
    primal exploded (\ctx -> dual exploded (computeLabelorder exploded) ctx cont)

-- Resulting computation will only use P, never D
primal :: Exploded (PDExp Int) Int args res
       -> (forall aenv. AContext Int aenv -> IdGen (OpenAcc aenv (PDExp Int) (PDAcc Int) args t))
       -> IdGen (Acc (PDExp Int) (PDAcc Int) args t)
primal exploded@(endlab, nodemap, _) cont =
    primal' nodemap endlab (Context LEmpty mempty) $ \ctx1 ->
        primalAll nodemap (Set.toList (collectArgLabels exploded)) ctx1 cont

primalAll :: DMap (ADLabelN Int) (Acc (PDExp Int) Int args)
          -> [AAnyLabelN Int]
          -> AContext Int aenv
          -> (forall aenv'. AContext Int aenv' -> IdGen (OpenAcc aenv' (PDExp Int) (PDAcc Int) args res))
          -> IdGen (OpenAcc aenv (PDExp Int) (PDAcc Int) args res)
primalAll _ [] ctx cont = cont ctx
primalAll nodemap (AnyLabel lbl : labs) ctx cont =
    primal' nodemap lbl ctx (\ctx' -> primalAll nodemap labs ctx' cont)

-- TODO: can't primal' just return the created bindmap entry, so that it
-- doesn't need to be looked up in the bindmap all the time?
primal' :: DMap (ADLabelN Int) (Acc (PDExp Int) Int args)
        -> ADLabelN Int t
        -> AContext Int aenv
        -> (forall aenv'. AContext Int aenv' -> IdGen (OpenAcc aenv' (PDExp Int) (PDAcc Int) args res))
        -> IdGen (OpenAcc aenv (PDExp Int) (PDAcc Int) args res)
primal' nodemap lbl ctx cont
  | trace ("primal': computing " ++ show lbl) False = undefined
  | fmapLabel P lbl `DMap.member` (let Context _ bindmap = ctx in bindmap) =
      cont ctx
  | not (uniqueLabVal (let Context labelenv _ = ctx in labelenv)) =  -- TODO: remove this check
      error "Non-unique label valuation in primal'!"
  | otherwise =
      case nodemap `dmapFind` lbl of
          Aconst ty value -> do
              let Context labelenv bindmap = ctx
              lblS <- genSingleId ty
              Alet (A.LeftHandSideSingle ty) (Aconst ty value)
                   <$> cont (Context (LPush labelenv lblS)
                                     (DMap.insert (fmapLabel P lbl) (TupRsingle lblS) bindmap))

          Apair _ (Alabel arglab1) (Alabel arglab2) ->
            primalAll nodemap [AnyLabel arglab1, AnyLabel arglab2] ctx $ \(Context labelenv bindmap) ->
              -- Note: We don't re-bind the constructed tuple into a new let
              -- binding with fresh labels here; we just point the node label
              -- for this Pair expression node to the pre-existing scalar labels.
              let labs = TupRpair (bindmap `dmapFind` fmapLabel P arglab1)
                                  (bindmap `dmapFind` fmapLabel P arglab2)
              in cont (Context labelenv
                               (DMap.insert (fmapLabel P lbl) labs bindmap))

          Anil ->
              -- No scalar labels are allocated for a Nil node, but we should still
              -- record that empty set of labels.
              let Context labelenv bindmap = ctx
              in cont (Context labelenv
                               (DMap.insert (fmapLabel P lbl) TupRunit bindmap))

          -- TODO: inlining of the produced halves into the branches of the
          -- generated Cond operation, so that the halves are really only
          -- computed if needed.
          -- TODO: Also think about: what if the code contains:
          --   (cond c t e) + (cond (not c) e t)
          -- Because both t and e are shared, they cannot be inlined, and will
          -- thus always be computed, even if in the end only one is needed in
          -- all situations. But then, don't write code like that.
          Acond restype condexpr (Alabel thenlab) (Alabel elselab) ->
            primalAll nodemap (expAParents condexpr ++ [AnyLabel thenlab, AnyLabel elselab]) ctx $ \(Context labelenv bindmap) ->
              let thenlabs = bindmap `dmapFind` fmapLabel P thenlab
                  elselabs = bindmap `dmapFind` fmapLabel P elselab
              in case (alabValFinds labelenv thenlabs
                      ,alabValFinds labelenv elselabs) of
                  (Just thenvars, Just elsevars) -> do
                      (Exists lhs, labs) <- genSingleIds restype
                      Alet lhs (Acond restype (resolveAlabs (Context labelenv bindmap) condexpr)
                                              (avars thenvars) (avars elsevars))
                           <$> cont (Context (lpushLabTup lhs labs labelenv)
                                             (DMap.insert (fmapLabel P lbl) labs bindmap))
                  _ ->
                      error "primal: Acond arguments did not compute arguments"

          Map restype@(ArrayR resshape reselty) lambda@(ELSplit (SplitLambdaAD lambdaPrimal _ lambdaLabs lambdaTmpType _ _) lambdaTmpLab) (Alabel arglab) ->
            primalAll nodemap (lamAParents lambda ++ [AnyLabel arglab]) ctx $ \(Context labelenv bindmap) ->
              let lambdaLabs' = lookupLambdaLabs bindmap lambdaLabs
                  TupRsingle arglabS@(DLabel argtypeS _) = bindmap `dmapFind` fmapLabel P arglab
              in case (alabValFind labelenv arglabS, alabValFinds labelenv lambdaLabs') of
                  (Just argidx, Just lambdaVars) -> do
                      lab <- genSingleId restype
                      let pairArrType = ArrayR resshape (TupRpair reselty lambdaTmpType)
                          tmpArrType = ArrayR resshape lambdaTmpType
                          instantiatedLambda = lambdaPrimal lambdaVars
                          computePrimal = Map pairArrType (ELPlain instantiatedLambda)
                                                          (Avar (A.Var argtypeS argidx))
                          -- For small functions, recompute the primal for the dual usage
                          producer
                            -- Note: the primal-transformed lambda is a lot larger than the input lambda, but it doesn't do
                            -- more _work_ as far as functionSize is concerned. Thus this heuristic application is sensible.
                            | Heuristic.functionSize instantiatedLambda < getConfigVar SmallFunSize
                            = smartPairA (mapFst computePrimal) (mapSnd computePrimal)
                            | otherwise
                            = Alet (A.LeftHandSideSingle pairArrType) computePrimal
                                   (let var = Avar (A.Var pairArrType ZeroIdx)
                                    in smartPairA (mapFst var) (mapSnd var))
                      Alet (A.LeftHandSidePair (A.LeftHandSideSingle restype) (A.LeftHandSideSingle tmpArrType))
                           producer
                           <$> cont (Context (LPush (LPush labelenv lab) lambdaTmpLab)
                                             (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                  _ ->
                      error $ "primal: Map arguments did not compute arguments: lbl = " ++ showDLabel lbl ++ "; arglab = " ++ showDLabel arglab ++ "; arglabS = " ++ showDLabel arglabS ++ "; lambdaLabs = " ++ showTupR show lambdaLabs ++ "; lambdaLabs' = " ++ showTupR show lambdaLabs' ++ "; CONTEXT = " ++ showContext (Context labelenv bindmap)

          ZipWith restype@(ArrayR resshape reselty) lambda@(ELSplit (SplitLambdaAD lambdaPrimal _ lambdaLabs lambdaTmpType _ _) lambdaTmpLab) (Alabel arglab1) (Alabel arglab2) ->
            primalAll nodemap (lamAParents lambda ++ [AnyLabel arglab1, AnyLabel arglab2]) ctx $ \(Context labelenv bindmap) ->
              let lambdaLabs' = lookupLambdaLabs bindmap lambdaLabs
                  TupRsingle arglab1S = bindmap `dmapFind` fmapLabel P arglab1
                  TupRsingle arglab2S = bindmap `dmapFind` fmapLabel P arglab2
              in case (alabValFind labelenv arglab1S, alabValFind labelenv arglab2S, alabValFinds labelenv lambdaLabs') of
                  (Just argidx1, Just argidx2, Just lambdaVars) -> do
                      lab <- genSingleId restype
                      let pairArrType = ArrayR resshape (TupRpair reselty lambdaTmpType)
                          tmpArrType = ArrayR resshape lambdaTmpType
                          instantiatedLambda = lambdaPrimal lambdaVars
                          computePrimal = ZipWith pairArrType (ELPlain instantiatedLambda)
                                                              (Avar (A.Var (labelType arglab1S) argidx1))
                                                              (Avar (A.Var (labelType arglab2S) argidx2))
                          -- For small functions, recompute the primal for the dual usage
                          producer
                            | Heuristic.functionSize instantiatedLambda < getConfigVar SmallFunSize
                            = smartPairA (mapFst computePrimal) (mapSnd computePrimal)
                            | otherwise
                            = Alet (A.LeftHandSideSingle pairArrType)
                                   computePrimal
                                   (let var = Avar (A.Var pairArrType ZeroIdx)
                                    in smartPairA (mapFst var) (mapSnd var))
                      Alet (A.LeftHandSidePair (A.LeftHandSideSingle restype) (A.LeftHandSideSingle tmpArrType))
                           producer
                           <$> cont (Context (LPush (LPush labelenv lab) lambdaTmpLab )
                                             (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                  _ ->
                      error "primal: ZipWith arguments did not compute arguments"

          Fold restype combfun e0expr (Alabel arglab) ->
            primalAll nodemap (funAParents combfun ++ maybe [] expAParents e0expr ++ [AnyLabel arglab]) ctx $ \(Context labelenv bindmap) ->
              let TupRsingle arglabS@(DLabel argtype _) = bindmap `dmapFind` fmapLabel P arglab
              in case alabValFind labelenv arglabS of
                  Just argidx -> do
                      lab <- genSingleId restype
                      Alet (A.LeftHandSideSingle restype)
                           (Fold restype (resolveAlabsFun (Context labelenv bindmap) combfun)
                                         (resolveAlabs (Context labelenv bindmap) <$> e0expr)
                                         (Avar (A.Var argtype argidx)))
                           <$> cont (Context (LPush labelenv lab)
                                             (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                  _ ->
                      error "primal: Fold arguments did not compute arguments"

          Sum restype (Alabel arglab) ->
            primal' nodemap arglab ctx $ \(Context labelenv bindmap) ->
              let TupRsingle arglabS@(DLabel argtype _) = bindmap `dmapFind` fmapLabel P arglab
              in case alabValFind labelenv arglabS of
                  Just argidx -> do
                      lab <- genSingleId restype
                      Alet (A.LeftHandSideSingle restype)
                           (Sum restype (Avar (A.Var argtype argidx)))
                           <$> cont (Context (LPush labelenv lab)
                                             (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                  _ ->
                      error "primal: Sum arguments did not compute arguments"

          Generate restype@(ArrayR resshape reselty) shexp lambda@(ELSplit (SplitLambdaAD lambdaPrimal _ lambdaLabs lambdaTmpType _ _) lambdaTmpLab) ->
            primalAll nodemap (expAParents shexp ++ lamAParents lambda) ctx $ \(Context labelenv bindmap) ->
              let lambdaLabs' = lookupLambdaLabs bindmap lambdaLabs
              in case alabValFinds labelenv lambdaLabs' of
                  Just lambdaVars -> do
                      lab <- genSingleId restype
                      let pairEltType = TupRpair reselty lambdaTmpType
                          pairArrType = ArrayR resshape pairEltType
                          tmpArrType = ArrayR resshape lambdaTmpType
                          instantiatedLambda = lambdaPrimal lambdaVars
                          computePrimal = Generate pairArrType (resolveAlabs (Context labelenv bindmap) shexp)
                                                               (ELPlain instantiatedLambda)
                          -- For small functions, recompute the primal for the dual usage
                          producer
                            | Heuristic.functionSize instantiatedLambda < getConfigVar SmallFunSize
                            = smartPairA (mapFst computePrimal) (mapSnd computePrimal)
                            | otherwise
                            = Alet (A.LeftHandSideSingle pairArrType) computePrimal
                                   (let var = Avar (A.Var pairArrType ZeroIdx)
                                    in smartPairA (mapFst var) (mapSnd var))
                      Alet (A.LeftHandSidePair (A.LeftHandSideSingle restype) (A.LeftHandSideSingle tmpArrType))
                           producer
                           <$> cont (Context (LPush (LPush labelenv lab) lambdaTmpLab)
                                             (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                  _ ->
                      error $ "primal: Generate arguments did not compute arguments"

          Replicate restype shtype shexp (Alabel arglab) ->
            primalAll nodemap (expAParents shexp ++ [AnyLabel arglab]) ctx $ \(Context labelenv bindmap) ->
              let TupRsingle arglabS@(DLabel argtype _) = bindmap `dmapFind` fmapLabel P arglab
              in case alabValFind labelenv arglabS of
                   Just argidx -> do
                      lab <- genSingleId restype
                      Alet (A.LeftHandSideSingle restype)
                           (Replicate restype shtype (resolveAlabs (Context labelenv bindmap) shexp) (Avar (A.Var argtype argidx)))
                           <$> cont (Context (LPush labelenv lab)
                                             (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                   _ ->
                      error "primal: Replicate arguments did not compute arguments"

          Slice restype shtype (Alabel arglab) shexp ->
            primalAll nodemap (expAParents shexp ++ [AnyLabel arglab]) ctx $ \(Context labelenv bindmap) ->
              let TupRsingle arglabS@(DLabel argtype _) = bindmap `dmapFind` fmapLabel P arglab
              in case alabValFind labelenv arglabS of
                   Just argidx -> do
                      lab <- genSingleId restype
                      Alet (A.LeftHandSideSingle restype)
                           (Slice restype shtype (Avar (A.Var argtype argidx)) (resolveAlabs (Context labelenv bindmap) shexp))
                           <$> cont (Context (LPush labelenv lab)
                                             (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                   _ ->
                      error "primal: Slice arguments did not compute arguments"

          Reshape restype shexp (Alabel arglab) ->
            primalAll nodemap (expAParents shexp ++ [AnyLabel arglab]) ctx $ \(Context labelenv bindmap) ->
              let TupRsingle arglabS@(DLabel argtype _) = bindmap `dmapFind` fmapLabel P arglab
              in case alabValFind labelenv arglabS of
                   Just argidx -> do
                      lab <- genSingleId restype
                      Alet (A.LeftHandSideSingle restype)
                           (Reshape restype (resolveAlabs (Context labelenv bindmap) shexp) (Avar (A.Var argtype argidx)))
                           <$> cont (Context (LPush labelenv lab)
                                             (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                   _ ->
                      error "primal: Reshape arguments did not compute arguments"

          Backpermute restype shexp indexfunc (Alabel arglab) ->
            primalAll nodemap (expAParents shexp ++ funAParents indexfunc ++ [AnyLabel arglab]) ctx $ \(Context labelenv bindmap) ->
              let TupRsingle arglabS@(DLabel argtype _) = bindmap `dmapFind` fmapLabel P arglab
              in case alabValFind labelenv arglabS of
                   Just argidx -> do
                      lab <- genSingleId restype
                      Alet (A.LeftHandSideSingle restype)
                           (Backpermute restype (resolveAlabs (Context labelenv bindmap) shexp)
                                                (resolveAlabsFun (Context labelenv bindmap) indexfunc)
                                                (Avar (A.Var argtype argidx)))
                           <$> cont (Context (LPush labelenv lab)
                                             (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                   _ ->
                      error "primal: Backpermute arguments did not compute arguments"

          Aget _ path (Alabel arglab) ->
            primal' nodemap arglab ctx $ \(Context labelenv bindmap) ->
              let pickedlabs = pickTupR path (bindmap `dmapFind` fmapLabel P arglab)
              in -- Note: We don't re-bind the picked tuple into a new let binding
                 -- with fresh labels here; we just point the node label for this
                 -- Get expression node to the pre-existing scalar labels.
                 cont (Context labelenv
                               (DMap.insert (fmapLabel P lbl) pickedlabs bindmap))

          Aarg ty idx -> do
              let Context labelenv bindmap = ctx
              labS <- genSingleId ty
              Alet (A.LeftHandSideSingle ty) (Aarg ty idx)
                   <$> cont (Context (LPush labelenv labS)
                                     (DMap.insert (fmapLabel P lbl) (TupRsingle labS) bindmap))

          Alabel arglab ->
            primal' nodemap arglab ctx $ \(Context labelenv bindmap) ->
              let arglabs = bindmap `dmapFind` fmapLabel P arglab
              in -- Note: We don't re-bind the labeled tuple into a new let binding
                 -- with fresh labels here; we just point the node label for this
                 -- Label expression node to the pre-existing scalar labels.
                 cont (Context labelenv
                               (DMap.insert (fmapLabel P lbl) arglabs bindmap))

          _ ->
              error "primal: Unexpected node shape in Exploded"

-- List of adjoints, collected for a particular label.
-- The exact variable references in the adjoints are dependent on the Let stack, thus the
-- environment (and the bindmap) is needed.
newtype AdjList lab alab args t = AdjList (forall aenv. AContext alab aenv -> [OpenAcc aenv lab (PDAcc alab) args t])

dual :: Exploded (PDExp Int) Int args (Array () Float)
     -> [AAnyLabelN Int]
     -> AContext Int aenv
     -> (forall aenv'. AContext Int aenv' -> IdGen (OpenAcc aenv' (PDExp Int) (PDAcc Int) args t))
     -> IdGen (OpenAcc aenv (PDExp Int) (PDAcc Int) args t)
dual (endlab, nodemap, _) labelorder context cont =
    let -- TODO: Can I use those scalarType shortcut methods to easily produce more type witnesses elsewhere?
        oneArr = Generate (ArrayR ShapeRz (TupRsingle scalarType))
                          Nil
                          (ELPlain (Lam (A.LeftHandSideWildcard TupRunit)
                                        (Body (Const scalarType 1.0))))
        contribmap = DMap.singleton (fmapLabel D endlab)
                                    (AdjList (const [oneArr]))
    in trace ("\nacc labelorder: " ++ show [labelLabel l | AnyLabel l <- labelorder]) $
       dual' nodemap labelorder context contribmap cont

dual' :: DMap (ADLabelN Int) (Acc (PDExp Int) Int args)
      -> [AAnyLabelN Int]
      -> AContext Int aenv
      -> DMap (ADLabelN (PDAcc Int)) (AdjList (PDExp Int) Int args)
      -> (forall aenv'. AContext Int aenv' -> IdGen (OpenAcc aenv' (PDExp Int) (PDAcc Int) args res))
      -> IdGen (OpenAcc aenv (PDExp Int) (PDAcc Int) args res)
dual' _ [] context _ cont = cont context
dual' nodemap (AnyLabel lbl : restlabels) (Context labelenv bindmap) contribmap cont =
    -- trace ("dual': computing " ++ show lbl) $
    case nodemap `dmapFind` lbl of
      -- We aren't interested in the adjoint of constant nodes -- seeing as
      -- they don't have any parents to contribute to.
      Aconst _ _ ->
          dual' nodemap restlabels (Context labelenv bindmap) contribmap cont

      -- Argument nodes don't have any nodes to contribute to either, but we do
      -- need to calculate and store their adjoint.
      Aarg restypeS _ -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
          lblS <- genSingleId restypeS
          Alet (A.LeftHandSideSingle restypeS) adjoint
               <$> dual' nodemap restlabels (Context (LPush labelenv lblS)
                                                     (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                         contribmap cont

      Acond restype condexp (Alabel thenlab) (Alabel elselab) -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution thenlab (lbl :@ TLNil) TLNil $ \adjvars (pvars :@ TLNil) _ labelenv' ->
                                    Acond restype (resolveAlabs (Context labelenv' bindmap) condexp)
                                                  (avars adjvars) (arraysSum restype pvars [])
                                ,Contribution elselab (lbl :@ TLNil) TLNil $ \adjvars (pvars :@ TLNil) _ labelenv' ->
                                    Acond restype (resolveAlabs (Context labelenv' bindmap) condexp)
                                                  (arraysSum restype pvars []) (avars adjvars)]
                                contribmap
          (Exists lhs, labs) <- genSingleIds restype
          Alet lhs adjoint
               <$> dual' nodemap restlabels (Context (lpushLabTup lhs labs labelenv)
                                                     (DMap.insert (fmapLabel D lbl) labs bindmap))
                         contribmap' cont

      Map restype (ELSplit (SplitLambdaAD _ lambdaDual lambdaLabs lambdaTmpType idxadjType idxInstMap) lambdaTmpLab) (Alabel arglab) -> do
          let lambdaLabs' = lookupLambdaLabs bindmap lambdaLabs
              TupRsingle (ArrayR shtype argelttype) = labelType arglab
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              pairArrType = ArrayR shtype (TupRpair argelttype idxadjType)
          templab <- genSingleId pairArrType
          let contribmap' = updateContribmap lbl
                                ([Contribution arglab TLNil (TupRsingle templab :@ TLNil) $
                                    \_ _ (TupRsingle tempVar :@ TLNil) _ ->
                                        mapFst (Avar tempVar)]
                                 ++ indexingContributions templab idxInstMap)
                                contribmap
          lab <- genSingleId restype
          Alet (A.LeftHandSideSingle restype) adjoint
               <$> let labelenv' = LPush labelenv lab
                   in case (alabValFind labelenv' lambdaTmpLab, alabValFinds labelenv' lambdaLabs') of
                        (Just lambdaTmpVar, Just fvvars) ->
                            Alet (A.LeftHandSideSingle pairArrType)
                                 (ZipWith pairArrType (ELPlain (lambdaDual fvvars))
                                          (Avar (A.Var restype ZeroIdx))
                                          (Avar (A.Var (ArrayR shtype lambdaTmpType) lambdaTmpVar)))
                                 <$> dual' nodemap restlabels (Context (LPush labelenv' templab)
                                                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lab) bindmap))
                                           contribmap' cont
                        _ -> error $ "dual Map: lambda tmp var and/or fvvars not computed"

      ZipWith restype (ELSplit (SplitLambdaAD _ lambdaDual lambdaLabs lambdaTmpType idxadjType idxInstMap) lambdaTmpLab) (Alabel arglab1) (Alabel arglab2) -> do
          -- The dual lambda computes, for each primal-output array element, a _tuple_
          -- containing the element adjoints for the left and right argument to
          -- the ZipWith. What we want is to "unzip" this array to get the two
          -- adjoint contribution arrays. However, we cannot do this whole
          -- computation at the point of the arguments as we usually do in a
          -- Contribution, because then we compute the ZipWith adjoint twice.
          -- Thus, we compute it once here, immediately, and then in the
          -- Contribution's ignore the ZipWith's adjoint and use the computed
          -- tuple-array directly.
          let lambdaLabs' = lookupLambdaLabs bindmap lambdaLabs
              TupRsingle (ArrayR shtype arg1elt) = labelType arglab1
              TupRsingle (ArrayR _      arg2elt) = labelType arglab2
              pairArrType = ArrayR shtype (TupRpair (TupRpair arg1elt arg2elt) idxadjType)
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
          templab <- genSingleId pairArrType
          let contribmap' = updateContribmap lbl
                                ([Contribution arglab1 TLNil (TupRsingle templab :@ TLNil) $
                                     \_ _ (TupRsingle tempVar :@ TLNil) _ ->
                                         mapGet (TILeft (TILeft TIHere)) (Avar tempVar)
                                 ,Contribution arglab2 TLNil (TupRsingle templab :@ TLNil) $
                                     \_ _ (TupRsingle tempVar :@ TLNil) _ ->
                                         mapGet (TILeft (TIRight TIHere)) (Avar tempVar)]
                                 ++ indexingContributions templab idxInstMap)
                                contribmap
          lab <- genSingleId restype
          Alet (A.LeftHandSideSingle restype) adjoint
               <$> let labelenv' = LPush labelenv lab
                   in case (alabValFind labelenv' lambdaTmpLab, alabValFinds labelenv' lambdaLabs') of
                          (Just lambdaTmpVar, Just fvvars) ->
                              Alet (A.LeftHandSideSingle (labelType templab))
                                   (ZipWith (labelType templab) (ELPlain (lambdaDual fvvars))
                                            (Avar (A.Var restype ZeroIdx))
                                            (Avar (A.Var (ArrayR shtype lambdaTmpType) lambdaTmpVar)))
                              <$> dual' nodemap restlabels (Context (LPush labelenv' templab)
                                                                    (DMap.insert (fmapLabel D lbl) (TupRsingle lab) bindmap))
                                        contribmap' cont
                          _ -> error $ "dual ZipWith: lambda tmp var and/or fvvars not computed"

      Sum restype@(ArrayR sht _) (Alabel arglab) -> do
          let TupRsingle argtypeS = labelType arglab
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) TLNil $
                                    \(TupRsingle adjvar) (TupRsingle pvar :@ TLNil) _ _ ->
                                        case elhsCopy (shapeType sht) of
                                            LetBoundExpE lhs shvars ->
                                                let lhs' = A.LeftHandSidePair lhs
                                                              (A.LeftHandSideWildcard (TupRsingle scalarType))
                                                in Generate argtypeS (Shape (Left pvar))
                                                            (ELPlain (Lam lhs' (Body (Index (Left adjvar) (Left (evars shvars))))))]
                                contribmap
          lab <- genSingleId restype
          Alet (A.LeftHandSideSingle restype) adjoint
               <$> dual' nodemap restlabels (Context (LPush labelenv lab)
                                                     (DMap.insert (fmapLabel D lbl) (TupRsingle lab) bindmap))
                         contribmap' cont

      -- TODO: This does not contribute any derivative to the initial expression; this is a remnant from the time before array indexing support.
      Fold restype@(ArrayR resshape _) origf@(Lam lambdalhs (Body lambdabody)) (Just initexp) (Alabel arglab)
        | expHasIndex lambdabody -> error "Array index operations in a Fold lambda not yet supported for AD"
        | expHasIndex initexp -> error "Array index operations in a Fold initial expression not yet supported for AD"
        | TupRsingle (SingleScalarType (NumSingleType elttypeN@(FloatingNumType TypeFloat))) <- etypeOf lambdabody
        , ReplicateOneMore onemoreSlix onemoreExpf <- replicateOneMore resshape -> do
          let argtype = labelType arglab
              TupRsingle argtypeS = argtype
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
          templab <- genSingleId argtypeS
          let contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil (TupRsingle templab :@ TLNil) $
                                    \(TupRsingle adjvar) _ (TupRsingle tempvar :@ TLNil) _ ->
                                        -- zipWith (*) (replicate (shape a) adjoint) (usual_derivative)
                                        smartZipWith (timesLam elttypeN)
                                            (Replicate argtypeS onemoreSlix (onemoreExpf (Shape (Left tempvar))) (Avar adjvar))
                                            (Avar tempvar)]
                                contribmap
          lab <- genSingleId restype
          -- Compute the derivative here once, so that it only needs to be
          -- combined with the local adjoint on every use, instead of having to
          -- recompute this whole thing.
          let labelenv' = LPush labelenv lab
          case alabValFinds labelenv' (bindmap `dmapFind` fmapLabel P arglab) of
            Just (TupRsingle argvar) ->
                Alet (A.LeftHandSideSingle restype) adjoint
                . Alet (A.LeftHandSideSingle (labelType templab))
                       (case ADExp.reverseAD lambdalhs (resolveAlabs (Context labelenv' bindmap) lambdabody) of
                          ADExp.ReverseADResE lambdalhs' dualbody ->
                              -- let sc = init (scanl f x0 a)
                              -- in zipWith (*) (zipWith D₂f sc a)
                              --                (tail (scanr (*) 1 (zipWith D₁f sc a)))
                              let d1f = Lam lambdalhs' (Body (smartFst dualbody))
                                  d2f = Lam lambdalhs' (Body (smartSnd dualbody))
                                  weaken1 = A.weakenSucc' A.weakenId
                                  argvar' = weaken weaken1 argvar
                                  (d1f', d2f') = (sinkFunAenv weaken1 d1f, sinkFunAenv weaken1 d2f)
                                  initScan ty dir f e0 a =  -- init (scanl) / tail (scanr)
                                      let scan'type = let ArrayR (ShapeRsnoc shtype) elttype = ty
                                                      in TupRpair (TupRsingle ty) (TupRsingle (ArrayR shtype elttype))
                                      in Aget (TupRsingle ty) (TILeft TIHere) (Scan' scan'type dir f e0 a)
                              in Alet (A.LeftHandSideSingle argtypeS)
                                      (initScan argtypeS A.LeftToRight
                                          (resolveAlabsFun (Context labelenv' bindmap) origf)
                                          (resolveAlabs (Context labelenv' bindmap) initexp)
                                          (Avar argvar))
                                      (smartZipWith (timesLam elttypeN)
                                          (smartZipWith d2f' (Avar (A.Var argtypeS ZeroIdx)) (Avar argvar'))
                                          (initScan argtypeS A.RightToLeft (timesLam elttypeN)
                                              (zeroForType' 1 elttypeN)
                                              (smartZipWith d1f' (Avar (A.Var argtypeS ZeroIdx)) (Avar argvar')))))
                <$> dual' nodemap restlabels (Context (LPush labelenv' templab)
                                                      (DMap.insert (fmapLabel D lbl) (TupRsingle lab) bindmap))
                          contribmap' cont
            _ -> error $ "dual Fold: argument primal was not computed"

      Fold restype@(ArrayR resshape _) origf@(Lam lambdalhs (Body lambdabody)) Nothing (Alabel arglab)
        | expHasIndex lambdabody -> error "Array index operations in a Fold lambda not yet supported for AD"
        | TupRsingle (SingleScalarType (NumSingleType elttypeN@(FloatingNumType TypeFloat))) <- etypeOf lambdabody
        , ReplicateOneMore onemoreSlix onemoreExpf <- replicateOneMore resshape -> do
          let argtype = labelType arglab
              TupRsingle argtypeS = argtype
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
          templab <- genSingleId argtypeS
          let contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil (TupRsingle templab :@ TLNil) $
                                    \(TupRsingle adjvar) _ (TupRsingle tempvar :@ TLNil) _ ->
                                        -- zipWith (*) (replicate (shape a) adjoint) (usual_derivative)
                                        smartZipWith (timesLam elttypeN)
                                            (Replicate argtypeS onemoreSlix (onemoreExpf (Shape (Left tempvar))) (Avar adjvar))
                                            (Avar tempvar)]
                                contribmap
          lab <- genSingleId restype
          -- Compute the derivative here once, so that it only needs to be
          -- combined with the local adjoint on every use, instead of having to
          -- recompute this whole thing.
          let labelenv' = LPush labelenv lab
          case alabValFinds labelenv' (bindmap `dmapFind` fmapLabel P arglab) of
            Just (TupRsingle argvar) ->
                Alet (A.LeftHandSideSingle restype) adjoint
                . Alet (A.LeftHandSideSingle (labelType templab))
                       (case ADExp.reverseAD lambdalhs (resolveAlabs (Context labelenv' bindmap) lambdabody) of
                          ADExp.ReverseADResE lambdalhs' dualbody ->
                              -- let sc = init (scanl1 f a)
                              -- in zipWith (*) ([1] ++ zipWith D₂f sc (tail l))
                              --                (scanr (*) 1 (zipWith D₁f sc (tail l)))
                              let d1f = Lam lambdalhs' (Body (smartFst dualbody))
                                  d2f = Lam lambdalhs' (Body (smartSnd dualbody))
                                  weaken1 = A.weakenSucc' A.weakenId
                                  argvar' = weaken weaken1 argvar
                                  (d1f', d2f') = (sinkFunAenv weaken1 d1f, sinkFunAenv weaken1 d2f)
                              in Alet (A.LeftHandSideSingle argtypeS)
                                      (smartInit (Scan argtypeS A.LeftToRight
                                          (resolveAlabsFun (Context labelenv' bindmap) origf)
                                          Nothing
                                          (Avar argvar)))
                                      (smartZipWith (timesLam elttypeN)
                                          (smartCons (zeroForType' 1 elttypeN)
                                              (smartZipWith d2f' (Avar (A.Var argtypeS ZeroIdx)) (smartTail (Avar argvar'))))
                                          (Scan argtypeS A.RightToLeft (timesLam elttypeN)
                                              (Just (zeroForType' 1 elttypeN))
                                              (smartZipWith d1f' (Avar (A.Var argtypeS ZeroIdx)) (smartTail (Avar argvar'))))))
                <$> dual' nodemap restlabels (Context (LPush labelenv' templab)
                                                      (DMap.insert (fmapLabel D lbl) (TupRsingle lab) bindmap))
                          contribmap' cont
            _ -> error $ "dual Fold: argument primal was not computed"

      -- Note: Don't need to do anything with the expression determining the
      -- shape of the result; its output is integer-valued and thus has zero
      -- adjoint, so it won't contribute non-zero'ly to anything.
      Generate restype@(ArrayR shtype _) _ (ELSplit (SplitLambdaAD _ lambdaDual lambdaLabs lambdaTmpType idxadjType idxInstMap) lambdaTmpLab) -> do
          let lambdaLabs' = lookupLambdaLabs bindmap lambdaLabs
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              -- The argument type of the lambda is the shape type of the output array.
              pairArrType = ArrayR shtype (TupRpair (shapeType shtype) idxadjType)
          templab <- genSingleId pairArrType
          let contribmap' = updateContribmap lbl
                                (indexingContributions templab idxInstMap)
                                contribmap
          lab <- genSingleId restype
          Alet (A.LeftHandSideSingle restype) adjoint
               <$> let labelenv' = LPush labelenv lab
                   in case (alabValFind labelenv' lambdaTmpLab, alabValFinds labelenv' lambdaLabs') of
                        (Just lambdaTmpVar, Just fvvars) ->
                            Alet (A.LeftHandSideSingle pairArrType)
                                 (ZipWith pairArrType (ELPlain (lambdaDual fvvars))
                                          (Avar (A.Var restype ZeroIdx))
                                          (Avar (A.Var (ArrayR shtype lambdaTmpType) lambdaTmpVar)))
                                 <$> dual' nodemap restlabels (Context (LPush labelenv' templab)
                                                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lab) bindmap))
                                           contribmap' cont
                        _ -> error $ "dual Generate: lambda tmp var and/or fvvars not computed"

      Replicate restype@(ArrayR _ eltty) shtype _ (Alabel arglab) -> do
          let TupRsingle argtypeS = labelType arglab
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil TLNil $
                                    \(TupRsingle adjvar) _ _ _ ->
                                        Reduce argtypeS (reduceSpecFromReplicate shtype)
                                               (plusLam eltty) (Avar adjvar)]
                                contribmap
          lab <- genSingleId restype
          Alet (A.LeftHandSideSingle restype) adjoint
               <$> dual' nodemap restlabels (Context (LPush labelenv lab)
                                                     (DMap.insert (fmapLabel D lbl) (TupRsingle lab) bindmap))
                         contribmap' cont

      Slice restype shtype (Alabel arglab) slexpr -> do
          let TupRsingle argtypeS = labelType arglab
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) TLNil $
                                    \(TupRsingle adjvar) (TupRsingle argpvar :@ TLNil) _ labelenv' ->
                                        let slexpr' = resolveAlabs (Context labelenv' bindmap) slexpr
                                        in Generate argtypeS (Shape (Left argpvar))
                                                    (ELPlain (sliceDualLambda shtype adjvar slexpr'))]
                                contribmap
          lab <- genSingleId restype
          Alet (A.LeftHandSideSingle restype) adjoint
               <$> dual' nodemap restlabels (Context (LPush labelenv lab)
                                                     (DMap.insert (fmapLabel D lbl) (TupRsingle lab) bindmap))
                         contribmap' cont

      Reshape restype@(ArrayR _ eltty) _ (Alabel arglab) -> do
          let TupRsingle (ArrayR shtype' _) = labelType arglab
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) TLNil $
                                    \(TupRsingle adjvar) (TupRsingle pvar :@ TLNil) _ _ ->
                                        Reshape (ArrayR shtype' eltty) (Shape (Left pvar)) (Avar adjvar)]
                                contribmap
          lab <- genSingleId restype
          Alet (A.LeftHandSideSingle restype) adjoint
               <$> dual' nodemap restlabels (Context (LPush labelenv lab)
                                                     (DMap.insert (fmapLabel D lbl) (TupRsingle lab) bindmap))
                         contribmap' cont

      Backpermute restype@(ArrayR _ eltty) _ (Lam indexfuncLHS (Body indexfuncBody)) (Alabel arglab) -> do
          let TupRsingle argtype = labelType arglab
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) TLNil $
                                    \(TupRsingle adjvar) (TupRsingle pvar :@ TLNil) _ labelenv' ->
                                        Permute argtype (plusLam eltty)
                                                (generateConstantArray argtype (Shape (Left pvar)))
                                                (Lam indexfuncLHS . Body $
                                                   mkJust (resolveAlabs (Context labelenv' bindmap)
                                                                        indexfuncBody))
                                                (Avar adjvar)]
                                contribmap
          lab <- genSingleId restype
          Alet (A.LeftHandSideSingle restype) adjoint
               <$> dual' nodemap restlabels (Context (LPush labelenv lab)
                                                     (DMap.insert (fmapLabel D lbl) (TupRsingle lab) bindmap))
                         contribmap' cont

      Aget restype path (Alabel arglab) -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) TLNil $
                                    \adjvars (argvars :@ TLNil) _ _ ->
                                        oneHotTup (labelType arglab) path argvars (avars adjvars)]
                                contribmap
          (Exists lhs, labs) <- genSingleIds restype
          Alet lhs adjoint
              <$> dual' nodemap restlabels (Context (lpushLabTup lhs labs labelenv)
                                                    (DMap.insert (fmapLabel D lbl) labs bindmap))
                        contribmap' cont

      Apair restype (Alabel arglab1) (Alabel arglab2) -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab1 TLNil TLNil $ \(TupRpair adjvars1 _) _ _ _ ->
                                    avars adjvars1
                                ,Contribution arglab2 TLNil TLNil $ \(TupRpair _ adjvars2) _ _ _ ->
                                    avars adjvars2]
                                contribmap
          (Exists lhs, labs) <- genSingleIds restype
          Alet lhs adjoint
              <$> dual' nodemap restlabels (Context (lpushLabTup lhs labs labelenv)
                                                    (DMap.insert (fmapLabel D lbl) labs bindmap))
                        contribmap' cont

      Anil ->
          -- Nothing to compute here, but we still need to register this expression label
          -- in the bindmap.
          dual' nodemap restlabels (Context labelenv
                                            (DMap.insert (fmapLabel D lbl) TupRunit bindmap))
                contribmap cont

      Alabel arglab -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil TLNil $ \adjvars _ _ _ ->
                                    avars adjvars]
                                contribmap
          (Exists lhs, labs) <- genSingleIds (labelType arglab)
          Alet lhs adjoint
               <$> dual' nodemap restlabels (Context (lpushLabTup lhs labs labelenv)
                                                     (DMap.insert (fmapLabel D lbl) labs bindmap))
                         contribmap' cont

      expr -> error ("\n!! " ++ show expr)
  where
    smartZipWith :: Fun aenv lab alab () ((e1, e2) -> e)
                 -> OpenAcc aenv lab alab args (Array sh e1)
                 -> OpenAcc aenv lab alab args (Array sh e2)
                 -> OpenAcc aenv lab alab args (Array sh e)
    smartZipWith f@(Lam _ (Body body)) a1 a2 =
        let TupRsingle (ArrayR shtype _) = atypeOf a1
        in ZipWith (ArrayR shtype (etypeOf body)) (ELPlain f) a1 a2
    smartZipWith _ _ _ = error "impossible GADTs"

    smartInnerPermute :: (forall env aenv'. OpenExp env aenv' lab alab () () Int
                                         -> OpenExp env aenv' lab alab () () Int)  -- ^ new inner dimension size
                      -> (forall env aenv'. OpenExp env aenv' lab alab () () Int
                                         -> OpenExp env aenv' lab alab () () Int)  -- ^ inner index transformer
                      -> OpenAcc aenv lab alab args (Array (sh, Int) t)
                      -> OpenAcc aenv lab alab args (Array (sh, Int) t)
    smartInnerPermute sizeExpr indexExpr a
      | TupRsingle ty@(ArrayR shtype _) <- atypeOf a
      , TupRpair tailsht _ <- shapeType shtype
      , LetBoundExpE shlhs shvars <- elhsCopy tailsht =
          Alet (A.LeftHandSideSingle ty) a
               (Backpermute ty
                   (Let (A.LeftHandSidePair shlhs (A.LeftHandSideSingle scalarType))
                        (Shape (Left (A.Var ty ZeroIdx)))
                        (smartPair
                            (evars (weakenVars (A.weakenSucc A.weakenId) shvars))
                            (sizeExpr (Var (A.Var scalarType ZeroIdx)))))
                   (Lam (A.LeftHandSidePair shlhs (A.LeftHandSideSingle scalarType))
                        (Body (smartPair
                                  (evars (weakenVars (A.weakenSucc A.weakenId) shvars))
                                  (indexExpr (Var (A.Var scalarType ZeroIdx))))))
                   (Avar (A.Var ty ZeroIdx)))
    smartInnerPermute _ _ _ = error "impossible GADTs"

    smartTail :: OpenAcc aenv lab alab args (Array (sh, Int) t) -> OpenAcc aenv lab alab args (Array (sh, Int) t)
    smartTail = smartInnerPermute (\sz -> smartSub numType sz (Const scalarType 1))
                                  (\idx -> smartAdd numType idx (Const scalarType 1))

    smartInit :: OpenAcc aenv lab alab args (Array (sh, Int) t) -> OpenAcc aenv lab alab args (Array (sh, Int) t)
    smartInit = smartInnerPermute (\sz -> smartSub numType sz (Const scalarType 1))
                                  (\idx -> idx)

    smartCons :: (forall env aenv'. OpenExp env aenv' lab alab () () t)
              -> OpenAcc aenv lab alab args (Array (sh, Int) t)
              -> OpenAcc aenv lab alab args (Array (sh, Int) t)
    smartCons prefix a
      | TupRsingle ty@(ArrayR shtype elttype) <- atypeOf a
      , TupRpair tailsht _ <- shapeType shtype
      , LetBoundExpE shlhs shvars <- elhsCopy tailsht =
          Alet (A.LeftHandSideSingle ty) a
               (Generate ty
                   (Let (A.LeftHandSidePair shlhs (A.LeftHandSideSingle scalarType))
                        (Shape (Left (A.Var ty ZeroIdx)))
                        (smartPair
                            (evars (weakenVars (A.weakenSucc A.weakenId) shvars))
                            (smartAdd numType (Var (A.Var scalarType ZeroIdx)) (Const scalarType 1))))
                   (ELPlain (Lam (A.LeftHandSidePair shlhs (A.LeftHandSideSingle scalarType))
                                 (Body (Cond elttype
                                             (smartGt singleType (Var (A.Var scalarType ZeroIdx)) (Const scalarType 0))
                                             Nothing
                                             (Index (Left (A.Var ty ZeroIdx))
                                                    (Left (smartPair
                                                            (evars (weakenVars (A.weakenSucc A.weakenId) shvars))
                                                            (smartSub numType (Var (A.Var scalarType ZeroIdx)) (Const scalarType 1)))))
                                             Nothing
                                             prefix)))))
    smartCons _ _ = error "impossible GADTs"

    timesLam :: NumType t -> Fun aenv lab alab tenv ((t, t) -> t)
    timesLam ty =
        let sty = SingleScalarType (NumSingleType ty)
        in Lam (A.LeftHandSidePair (A.LeftHandSideSingle sty) (A.LeftHandSideSingle sty))
               (Body (smartMul ty (Var (A.Var sty (SuccIdx ZeroIdx))) (Var (A.Var sty ZeroIdx))))

-- Utility functions
-- -----------------

infixr :@
data TypedList f tys where
    TLNil :: TypedList f '[]
    (:@) :: f t -> TypedList f tys -> TypedList f (t ': tys)

tlmap :: (forall t. f t -> g t) -> TypedList f tys -> TypedList g tys
tlmap _ TLNil = TLNil
tlmap f (x :@ xs) = f x :@ tlmap f xs

data Contribution node args =
    forall parents labtups t.
        Contribution (ADLabelN Int t)  -- to which label are we contributing an adjoint
                     (TypedList (ADLabelN Int) parents)  -- labels you need the primary value of
                     (TypedList (TupR (ADLabel Int)) labtups)  -- scalar-level labels you need vars of
                     (forall aenv. A.ArrayVars aenv node                  -- current node's adjoint
                                -> TypedList (A.ArrayVars aenv) parents   -- requested primal values
                                -> TypedList (A.ArrayVars aenv) labtups   -- requested primal values
                                -> ALabVal Int aenv                       -- the scalar labelenv at instantiation
                                -> OpenAcc aenv (PDExp Int) (PDAcc Int) args t) -- contribution

-- Note: Before this code was extracted into a separate function, its
-- functionality was inlined in the branches of dual'. Because of that, the
-- branches needed explicit type signatures (and thus be separate functions),
-- since the definition of the contribution function had too intricate type
-- variables for GHC to figure out.
-- Now that this is a separate function, though, the type signature here (and
-- the typing of Contribution) removes the need of the branches of dual' to
-- have a separate type signature, significantly simplifying the structure of
-- the code.
updateContribmap :: ADLabelN Int node
                 -> [Contribution node args]
                 -> DMap (ADLabelN (PDAcc Int)) (AdjList (PDExp Int) Int args)
                 -> DMap (ADLabelN (PDAcc Int)) (AdjList (PDExp Int) Int args)
updateContribmap lbl =
    flip . foldr $ \(Contribution lab parentlabs scalarlabss gen) ->
        addContribution (fmapLabel D lab) $ \(Context labelenv bindmap) ->
            let currentlabs = bindmap `dmapFind` fmapLabel D lbl
            in case (alabValFinds labelenv currentlabs
                    ,findAll (Context labelenv bindmap) parentlabs
                    ,findAll' labelenv scalarlabss) of
                (Just adjvars, parvars, scalvars) -> gen adjvars parvars scalvars labelenv
                _ -> error $ "updateContribmap: node D " ++ show lbl ++ " was not computed"
  where
    findAll :: AContext Int aenv -> TypedList (ADLabelN Int) parents -> TypedList (A.ArrayVars aenv) parents
    findAll (Context labelenv bindmap) =
        tlmap $ \lab ->
            let labs = bindmap `dmapFind` fmapLabel P lab
            in fromMaybe (err lab) (alabValFinds labelenv labs)
      where err lab = error $ "updateContribmap(findAll): arg P " ++ show lab ++ " was not computed"

    findAll' :: ALabVal Int aenv -> TypedList (TupR (ADLabel Int)) parents -> TypedList (A.ArrayVars aenv) parents
    findAll' labelenv =
        tlmap $ \labs -> fromMaybe (err labs) (alabValFinds labelenv labs)
      where err (labs :: TupR (ADLabel Int) t) =
              error $ "updateContribmap(findAll'): arg " ++ showTupR show labs ++ " was not computed"

addContribution :: Ord alab
                => ADLabelN (PDAcc alab) t
                -> (forall aenv. AContext alab aenv -> OpenAcc aenv lab (PDAcc alab) args t)
                -> DMap (ADLabelN (PDAcc alab)) (AdjList lab alab args)
                -> DMap (ADLabelN (PDAcc alab)) (AdjList lab alab args)
addContribution lbl contribution =
    DMap.insertWith (\(AdjList f1) (AdjList f2) -> AdjList (\context -> f1 context ++ f2 context))
                    lbl
                    (AdjList (pure . contribution))

collectAdjoint :: DMap (ADLabelN (PDAcc Int)) (AdjList lab Int args)
               -> ADLabelN Int item
               -> AContext Int aenv
               -> OpenAcc aenv lab (PDAcc Int) args item
collectAdjoint contribmap lbl (Context labelenv bindmap)
  | Just pvars <- alabValFinds labelenv (bindmap `dmapFind` fmapLabel P lbl)
  = case DMap.lookup (fmapLabel D lbl) contribmap of
        Just (AdjList listgen) -> arraysSum (labelType lbl) pvars (listgen (Context labelenv bindmap))
        Nothing -> arraysSum (labelType lbl) pvars []  -- if there are no contributions, well, the adjoint is an empty sum (i.e. zero)
collectAdjoint _ _ _ = error "Impossible GADTs"

lookupLambdaLabs :: ABindMap Int  -- bindmap
                 -> TupR (ADLabelNS Int) t  -- free variable labels from SplitLambdaAD
                 -> TupR (ADLabel Int) t  -- resolved labels pointing into the current labelenv
lookupLambdaLabs bindmap' =
    fmapTupR $ \lamlab -> case bindmap' `dmapFind` fmapLabel P (tupleLabel lamlab) of
                              TupRsingle singlelab -> singlelab
                              _ -> error "Unexpected non-scalar label in free array variables in lambdaLabs"

-- | The function in an expression lambda may contain array indexing
-- operations, which should contribute adjoints to elements of the indexed
-- arrays. This function builds the 'Contribution' values (using Permute
-- operations) for the indexed arrays given the array of output values of the
-- dual function in SplitLambdaAD, as well as the indexing instantiator map in
-- SplitLambdaAD.
indexingContributions
    :: ADLabel Int (Array sh (t, idxadj))  -- ^ Single-label of the array of outputs of the dual split-lambda
    -> DMap (ADLabelNS Int) (IndexInstantiators idxadj)  -- ^ The indexing instantiator map from SplitLambdaAD
    -> [Contribution node args]  -- ^ The contributions to indexed arrays in the lambda (the current @node@ is irrelevant)
indexingContributions templab idxInstMap =
    let ArrayR shtype (TupRpair argelttype idxadjType) = labelType templab
    in -- Note: 'tupleLabel' is warranted because array labels in expressions, being
       -- _variables_, originate from let-created variables in the original AST, and
       -- thus their labels are node labels.
       [Contribution (tupleLabel backingLab) (tupleLabel backingLab :@ TLNil) (TupRsingle templab :@ TLNil) $
          \_ (TupRsingle backingPVar :@ TLNil) (TupRsingle tempVar :@ TLNil) _ ->
              Permute backingType
                      (plusLam backingEltType)
                      (generateConstantArray backingType (Shape (Left backingPVar)))
                      (case elhsCopy (shapeType shtype) of  -- Lambda: map use-point index to backing index
                        LetBoundExpE lhs vars
                          | LetBoundExpE idxlhs idxvars <- elhsCopy backingShapeT ->
                              Lam lhs $ Body $
                                Let idxlhs
                                    (smartSnd $  -- Choose the index item from the (adj, idx) tuple
                                      instantiator $
                                        smartSnd $
                                          Index (Left tempVar) (Left (evars vars)))
                                    (condHeadIsNegative (evars idxvars)  -- if we know for sure the index is negative (i.e. Index wasn't executed in the primal), return Nothing
                                        (mkNothing backingShapeT)
                                        (mkJust (evars idxvars))))
                      (Map (ArrayR shtype backingEltType)  -- Map: obtain the array of adjoints to be permuted
                           (ELPlain $
                              case elhsCopy idxadjType of
                                LetBoundExpE lhs vars ->
                                  Lam (A.LeftHandSidePair (A.LeftHandSideWildcard argelttype) lhs) $ Body $
                                    smartFst $  -- Choose the adjoint item from the (adj, idx) tuple
                                      instantiator (evars vars))
                           (Avar tempVar))
       | backingLab :=> IndexInstantiators insts <- DMap.toList idxInstMap
       , IndexInstantiator instantiator <- insts
       , let backingType@(ArrayR backingSht backingEltType) = labelType backingLab
             backingShapeT = shapeType backingSht]
  where
    -- If there is a head and it's negative, produce @e1@, otherwise @e2@.
    condHeadIsNegative :: OpenExp env aenv lab alab args tenv t
                       -> OpenExp env aenv lab alab args tenv a
                       -> OpenExp env aenv lab alab args tenv a
                       -> OpenExp env aenv lab alab args tenv a
    condHeadIsNegative subject e1 e2 = case etypeOf subject of
        TupRpair _ ty@(TupRsingle (SingleScalarType sty)) ->
          Cond (etypeOf e1)
               (PrimApp (TupRsingle scalarType) (A.PrimLt sty)
                        (smartPair (smartSnd subject) (zeroForType ty)))
               Nothing e1 Nothing e2
        _ -> e2  -- if there is no head, then it certainly isn't negative

arrayPlus :: OpenAcc aenv lab alab args (Array sh t)
          -> OpenAcc aenv lab alab args (Array sh t)
          -> OpenAcc aenv lab alab args (Array sh t)
arrayPlus a1 a2
  | TupRsingle arrty@(ArrayR _ ty) <- atypeOf a1
  , Lam lhs1 (Lam lhs2 body) <- plusLam ty
  = ZipWith arrty (ELPlain (Lam (A.LeftHandSidePair lhs1 lhs2) body)) a1 a2
arrayPlus _ _ = error "unreachable"

arraysSum :: ArraysR t
          -> A.ArrayVars aenv t  -- primal result
          -> [OpenAcc aenv lab alab args t]
          -> OpenAcc aenv lab alab args t
arraysSum TupRunit TupRunit _ = Anil
arraysSum (TupRsingle ty@ArrayR{}) (TupRsingle pvar) [] = generateConstantArray ty (Shape (Left pvar))
arraysSum ty@(TupRpair t1 t2) (TupRpair pvars1 pvars2) [] = Apair ty (arraysSum t1 pvars1 []) (arraysSum t2 pvars2 [])
arraysSum ty _ l = foldl1 (tupleZipAcc' ty (const arrayPlus) (\_ _ -> False)) l

generateConstantArray :: ArrayR (Array sh t) -> Exp aenv lab alab () () sh -> OpenAcc aenv lab alab args (Array sh t)
generateConstantArray (ArrayR sht ty) she =
    Generate (ArrayR sht ty) she
             (ELPlain (Lam (A.LeftHandSideWildcard (shapeType sht)) (Body (zeroForType ty))))

expGetLam :: TupleIdx t t' -> TypeR t -> Fun aenv lab alab tenv (t -> t')
expGetLam ti ty
  | LetBoundExpE lhs vars <- elhsCopy ty
  = Lam lhs (Body (evars (pickTupR ti vars)))

mapGet :: TupleIdx t t' -> OpenAcc aenv lab alab tenv (Array sh t) -> OpenAcc aenv lab alab tenv (Array sh t')
mapGet ti a =
  let TupRsingle (ArrayR sht ty) = atypeOf a
  in Map (ArrayR sht (pickTupR ti ty)) (ELPlain (expGetLam ti ty)) a

mapFst :: OpenAcc aenv lab alab tenv (Array sh (a, b)) -> OpenAcc aenv lab alab tenv (Array sh a)
mapFst = mapGet (TILeft TIHere)

mapSnd :: OpenAcc aenv lab alab tenv (Array sh (a, b)) -> OpenAcc aenv lab alab tenv (Array sh b)
mapSnd = mapGet (TIRight TIHere)

plusLam :: TypeR t -> Fun aenv lab alab tenv (t -> t -> t)
plusLam ty
  | DeclareVars lhs1 _ varsgen1 <- declareVars ty
  , DeclareVars lhs2 weaken2 varsgen2 <- declareVars ty
  = Lam lhs1 . Lam lhs2 . Body $ expPlus ty (evars (varsgen1 weaken2)) (evars (varsgen2 A.weakenId))

oneHotTup :: ArraysR t -> TupleIdx t t' -> A.ArrayVars aenv t -> OpenAcc aenv lab alab args t' -> OpenAcc aenv lab alab args t
oneHotTup _ TIHere _ ex = ex
oneHotTup ty@(TupRpair ty1 ty2) (TILeft ti) (TupRpair pvars1 pvars2) ex =
    Apair ty (oneHotTup ty1 ti pvars1 ex) (arraysSum ty2 pvars2 [])
oneHotTup ty@(TupRpair ty1 ty2) (TIRight ti) (TupRpair pvars1 pvars2) ex =
    Apair ty (arraysSum ty1 pvars1 []) (oneHotTup ty2 ti pvars2 ex)
oneHotTup _ _ _ _ = error "oneHotTup: impossible GADTs"

-- Remark: this function is uniquely defined by its types (ignoring bottoms). This is nice.
reduceSpecFromReplicate :: SliceIndex slix sl co sh -> ReduceSpec slix sl sh
reduceSpecFromReplicate SliceNil = RSpecNil
reduceSpecFromReplicate (SliceAll slix) = RSpecKeep (reduceSpecFromReplicate slix)
reduceSpecFromReplicate (SliceFixed slix) = RSpecReduce (reduceSpecFromReplicate slix)

data ReplicateOneMore sh =
    forall slix.
        ReplicateOneMore (SliceIndex slix sh ((), Int) (sh, Int))
                         (forall env aenv lab alab args tenv.
                              OpenExp env aenv lab alab args tenv (sh, Int)
                           -> OpenExp env aenv lab alab args tenv slix)

-- Produces a SliceIndex that can be passed to Replicate, and a function that
-- produces the slix expression parameter to Replicate, given an expression for
-- the desired full shape.
replicateOneMore :: ShapeR sh -> ReplicateOneMore sh
replicateOneMore sh
  | SliceCopy slix e <- sliceCopy sh
  = ReplicateOneMore (SliceFixed slix)
                     (\she -> Let (A.LeftHandSidePair (A.LeftHandSideWildcard (shapeType (sliceShapeR slix)))
                                                      (A.LeftHandSideSingle scalarType))
                                  she
                                  (smartPair e (Var (A.Var scalarType ZeroIdx))))

data SliceCopy sh =
    forall slix.
        SliceCopy (SliceIndex slix sh () sh)
                  (forall env aenv lab alab args tenv. OpenExp env aenv lab alab args tenv slix)

sliceCopy :: ShapeR sh -> SliceCopy sh
sliceCopy ShapeRz = SliceCopy SliceNil Nil
sliceCopy (ShapeRsnoc sh)
  | SliceCopy slix e <- sliceCopy sh
  = SliceCopy (SliceAll slix) (smartPair e Nil)


-- The dual of Slice is a Generate that picks the adjoint for the entries
-- sliced, and zero for the entries cut away. This is the lambda for that
-- Generate.
sliceDualLambda :: SliceIndex slix sl co sh
                -> A.Var ArrayR aenv (Array sl e)
                -> Exp aenv lab alab () tenv slix
                -> Fun aenv lab alab tenv (sh -> e)
sliceDualLambda slix adjvar@(A.Var (ArrayR _ eltty) _) slexpr
  | LetBoundExpE indexlhs indexvars' <- elhsCopy (shapeType (sliceDomainR slix))
  , LetBoundExpE slicelhs slicevars <- elhsCopy (sliceIndexTypeR slix)
  , let indexvars = weakenVars (A.weakenWithLHS slicelhs) indexvars'
  = Lam indexlhs . Body $
      Let slicelhs (sinkExp (A.weakenWithLHS indexlhs) slexpr) $
          Cond eltty
               (genCond slix indexvars slicevars)
               Nothing
               (Index (Left adjvar) (Left (evars (indexSlice slix indexvars))))
               Nothing
               (zeroForType eltty)
  where
    indexSlice :: SliceIndex slix sl co sh -> A.ExpVars env sh -> A.ExpVars env sl
    indexSlice SliceNil _ = TupRunit
    indexSlice (SliceAll slix') (TupRpair vars var) = TupRpair (indexSlice slix' vars) var
    indexSlice (SliceFixed slix') (TupRpair vars _) = indexSlice slix' vars
    indexSlice _ _ = error "impossible GADTs"

    genCond :: SliceIndex slix sl co sh -> A.ExpVars env sh -> A.ExpVars env slix -> OpenExp env aenv lab alab args tenv A.PrimBool
    genCond SliceNil TupRunit TupRunit = mkBool True
    genCond (SliceAll slix') (TupRpair idxvs _) (TupRpair slvs _) = genCond slix' idxvs slvs
    genCond (SliceFixed slix') (TupRpair idxvs (TupRsingle idxv)) (TupRpair slvs (TupRsingle slv)) =
        PrimApp (TupRsingle scalarType) A.PrimLAnd
            (smartPair (PrimApp (TupRsingle scalarType) (A.PrimEq singleType)
                             (smartPair (Var idxv) (Var slv)))
                        (genCond slix' idxvs slvs))
    genCond _ _ _ = error "impossible GADTs"

sliceIndexTypeR :: SliceIndex slix sl co dim -> TypeR slix
sliceIndexTypeR SliceNil        = TupRunit
sliceIndexTypeR (SliceAll sl)   = TupRpair (sliceIndexTypeR sl) TupRunit
sliceIndexTypeR (SliceFixed sl) = TupRpair (sliceIndexTypeR sl) (TupRsingle scalarType)

-- Errors if any parents are not Label nodes, or if called on a Let or Var node.
accLabelParents :: OpenAcc aenv lab alab args t -> [AAnyLabelN alab]
accLabelParents = \case
    Aconst _ _ -> []
    Apair _ e1 e2 -> fromLabel e1 ++ fromLabel e2
    Anil -> []
    Acond _ ce e1 e2 -> expAParents ce ++ fromLabel e1 ++ fromLabel e2
    Map _ lam e -> fromLabel e ++ lamAParents lam
    ZipWith _ lam e1 e2 -> fromLabel e1 ++ fromLabel e2 ++ lamAParents lam
    Generate _ e lam -> expAParents e ++ lamAParents lam
    Fold _ f me0 e -> funAParents f ++ maybe [] expAParents me0 ++ fromLabel e
    Scan _ _ f me0 e -> funAParents f ++ maybe [] expAParents me0 ++ fromLabel e
    Scan' _ _ f e0 e -> funAParents f ++ expAParents e0 ++ fromLabel e
    Sum _ e -> fromLabel e
    Replicate _ _ she e -> expAParents she ++ fromLabel e
    Slice _ _ e she -> fromLabel e ++ expAParents she
    Reshape _ she e -> expAParents she ++ fromLabel e
    Backpermute _ she f e -> expAParents she ++ funAParents f ++ fromLabel e
    Aget _ _ e -> fromLabel e
    Aarg _ _ -> []
    Alabel lab -> [AnyLabel lab]
    Alet _ _ _ -> unimplemented "Alet"
    Avar _ -> unimplemented "Avar"
    Reduce _ _ _ _ -> error "Unexpected Reduce in accLabelParents (should only be created in dual)"
    Permute _ _ _ _ _ -> error "Unexpected Permute in accLabelParents"
  where
    unimplemented name =
        error ("accLabelParents: Unimplemented for " ++ name ++ ", semantics unclear")

    fromLabel (Alabel lab) = [AnyLabel lab]
    fromLabel _ = error "accLabelParents: Parent is not a label"

expAParents :: OpenExp env aenv lab alab args tenv t -> [AAnyLabelN alab]
expAParents e = [AnyLabel (tupleLabel lab) | AnyLabel lab <- expALabels e]

funAParents :: OpenFun env aenv lab alab tenv t -> [AAnyLabelN alab]
funAParents fun = [AnyLabel (tupleLabel lab) | AnyLabel lab <- expFunALabels fun]

lamAParents :: ExpLambda1 aenv lab alab tenv sh t1 t2 -> [AAnyLabelN alab]
lamAParents (ELSplit (SplitLambdaAD _ _ fvtup _ _ instMap) _) =
    [AnyLabel (tupleLabel lab) | Some lab <- enumerateTupR fvtup ++ DMap.keys instMap]
lamAParents (ELPlain fun) = funAParents fun

resolveAlabs :: (HasCallStack, Ord alab, Show alab)
             => AContext alab aenv
             -> OpenExp env aenv' lab alab args tenv t
             -> OpenExp env aenv lab alab' args tenv t
resolveAlabs (Context labelenv bindmap) =
    inlineAvarLabels' $ \lab ->
        case bindmap `dmapFind` tupleLabel (fmapLabel P lab) of
            labs -> case alabValFinds labelenv labs of
                Just (TupRsingle var) -> var
                Just _ -> error $ "Array label in labelised expression refers to tuple?: " ++ show lab
                Nothing -> error $ "Array label in labelised expression not found in env: " ++ show lab

resolveAlabsFun :: (Ord alab, Show alab)
                => AContext alab aenv
                -> OpenFun env aenv' lab alab tenv t
                -> OpenFun env aenv lab alab' tenv t
resolveAlabsFun ctx (Lam lhs fun) = Lam lhs (resolveAlabsFun ctx fun)
resolveAlabsFun ctx (Body e) = Body (resolveAlabs ctx e)

collectArgLabels :: Ord alab => Exploded lab alab args t -> Set (AAnyLabelN alab)
collectArgLabels (_, _, argmap) = Set.fromList [AnyLabel lab | _ :=> lab <- DMap.toList argmap]

dmapFind :: (HasCallStack, GCompare f) => DMap f g -> f a -> g a
dmapFind mp elt = case DMap.lookup elt mp of
                    Just res -> res
                    Nothing -> error "dmapFind: not found"

-- TODO: make smartFstA and smartSndA non-quadratic (should be easy)
smartFstA :: OpenAcc aenv lab alab args (t1, t2) -> OpenAcc aenv lab alab args t1
smartFstA (Apair _ ex _) = ex
smartFstA (Aget (TupRpair t1 _) tidx ex) = Aget t1 (insertFst tidx) ex
  where insertFst :: TupleIdx t (t1, t2) -> TupleIdx t t1
        insertFst TIHere = TILeft TIHere
        insertFst (TILeft ti) = TILeft (insertFst ti)
        insertFst (TIRight ti) = TIRight (insertFst ti)
smartFstA ex
  | TupRpair t1 _ <- atypeOf ex
  = Aget t1 (TILeft TIHere) ex
smartFstA _ = error "smartFstA: impossible GADTs"

smartSndA :: OpenAcc aenv lab alab args (t1, t2) -> OpenAcc aenv lab alab args t2
smartSndA (Apair _ _ ex) = ex
smartSndA (Aget (TupRpair _ t2) tidx ex) = Aget t2 (insertSnd tidx) ex
  where insertSnd :: TupleIdx t (t1, t2) -> TupleIdx t t2
        insertSnd TIHere = TIRight TIHere
        insertSnd (TILeft ti) = TILeft (insertSnd ti)
        insertSnd (TIRight ti) = TIRight (insertSnd ti)
smartSndA ex
  | TupRpair _ t2 <- atypeOf ex
  = Aget t2 (TIRight TIHere) ex
smartSndA _ = error "smartSndA: impossible GADTs"

smartPairA :: OpenAcc aenv lab alab args a -> OpenAcc aenv lab alab args b -> OpenAcc aenv lab alab args (a, b)
smartPairA a b = Apair (TupRpair (atypeOf a) (atypeOf b)) a b
