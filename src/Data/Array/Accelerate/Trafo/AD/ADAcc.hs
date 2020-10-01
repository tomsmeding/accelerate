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
import Data.Array.Accelerate.Trafo.AD.ADExp (splitLambdaAD, labeliseExp, labeliseFun, inlineAvarLabels')
import Data.Array.Accelerate.Trafo.AD.Algorithms
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Debug
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.Pretty
import Data.Array.Accelerate.Trafo.AD.Sink
import Data.Array.Accelerate.Trafo.Substitution (rebuildLHS)
import Data.Array.Accelerate.Trafo.Var (declareVars, DeclareVars(..))


type AContext = Context ArrayR PDAuxTagAcc


genId :: ArraysR t -> IdGen (ADLabelT Int t)
genId = genId'

genSingleId :: ArrayR t -> IdGen (ADLabel Int t)
genSingleId = genId'

genSingleIds :: ArraysR t -> IdGen (Exists (A.LeftHandSide ArrayR t aenv), TupR (ADLabel Int) t)
genSingleIds TupRunit = return (Exists (A.LeftHandSideWildcard TupRunit), TupRunit)
genSingleIds (TupRsingle ty) = (Exists (A.LeftHandSideSingle ty),) . TupRsingle <$> genSingleId ty
genSingleIds (TupRpair t1 t2) = do
    (Exists lhs1, ids1) <- genSingleIds t1
    (Exists lhs2, ids2) <- genSingleIds t2
    return (Exists (A.LeftHandSidePair lhs1 lhs2), TupRpair ids1 ids2)


-- TODO: make this a data definition, not a tuple
type Exploded lab alab args res = (ADLabelT alab res, DMap (ADLabelT alab) (Acc lab alab args), DMap (A.Idx args) (ADLabelT alab))

showExploded :: (Ord alab, Show lab, Show alab) => Exploded lab alab args t -> String
showExploded (endlab, nodemap, argmap) =
    "(" ++ showDLabel endlab ++ ", " ++ showNodemap nodemap ++ ", " ++ showArgmap argmap ++ ")"

showNodemap :: (Ord alab, Show lab, Show alab) => DMap (ADLabelT alab) (Acc lab alab args) -> String
showNodemap nodemap =
    let tups = sortOn fst [(lab, (showDLabel dlab, show expr))
                          | dlab@(DLabel _ lab) :=> expr <- DMap.assocs nodemap]
        s = intercalate ", " ["(" ++ dlabshow ++ ") :=> " ++ exprshow
                             | (_, (dlabshow, exprshow)) <- tups]
    in "[" ++ s ++ "]"

showArgmap :: Show alab => DMap (A.Idx args) (ADLabelT alab) -> String
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
generaliseArgs (Backpermute ty dim f e) = Backpermute ty dim f (generaliseArgs e)
generaliseArgs (Replicate ty sht she e) = Replicate ty sht she (generaliseArgs e)
generaliseArgs (Reduce sht she f e) = Reduce sht she f (generaliseArgs e)
generaliseArgs (Reshape ty she e) = Reshape ty she (generaliseArgs e)
generaliseArgs (Sum ty a) = Sum ty (generaliseArgs a)
generaliseArgs (Generate ty she f) = Generate ty she f
generaliseArgs (Aget ty path ex) = Aget ty path (generaliseArgs ex)
generaliseArgs (Alet lhs rhs ex) = Alet lhs (generaliseArgs rhs) (generaliseArgs ex)
generaliseArgs (Avar v) = Avar v
generaliseArgs (Aarg _ _) = error "generaliseArgs: Arg found"
generaliseArgs (Alabel labs) = Alabel labs

-- Assumes the expression does not contain references to the array environment; TODO: this is a false assumption in general, but makes the input language easier for now
doesNotContainArrayVars :: HasCallStack => OpenExp env aenv lab alab args t -> OpenExp env aenv' lab alab args t
doesNotContainArrayVars (Const ty x) = Const ty x
doesNotContainArrayVars (PrimApp ty op ex) = PrimApp ty op (doesNotContainArrayVars ex)
doesNotContainArrayVars (Pair ty e1 e2) = Pair ty (doesNotContainArrayVars e1) (doesNotContainArrayVars e2)
doesNotContainArrayVars Nil = Nil
doesNotContainArrayVars (Cond ty e1 e2 e3) = Cond ty (doesNotContainArrayVars e1) (doesNotContainArrayVars e2) (doesNotContainArrayVars e3)
doesNotContainArrayVars (Shape _) = error "doesNotContainArrayVars: Shape found"
doesNotContainArrayVars (ShapeSize sht e) = ShapeSize sht (doesNotContainArrayVars e)
doesNotContainArrayVars (Get ty path ex) = Get ty path (doesNotContainArrayVars ex)
doesNotContainArrayVars (Let lhs rhs ex) = Let lhs (doesNotContainArrayVars rhs) (doesNotContainArrayVars ex)
doesNotContainArrayVars (Var v) = Var v
doesNotContainArrayVars (Arg ty idx) = Arg ty idx
doesNotContainArrayVars (Label lab) = Label lab

-- Assumes the expression does not contain references to the array environment; TODO: this is a false assumption in general, but makes the input language easier for now
doesNotContainArrayVarsF :: HasCallStack => OpenFun env aenv lab alab t -> OpenFun env aenv' lab alab t
doesNotContainArrayVarsF (Lam lhs fun) = Lam lhs (doesNotContainArrayVarsF fun)
doesNotContainArrayVarsF (Body e) = Body (doesNotContainArrayVars e)

-- Assumes the expression does not contain Label
generaliseLabFun :: HasCallStack => OpenFun env aenv lab alab t -> OpenFun env aenv lab' alab t
generaliseLabFun (Lam lhs fun) = Lam lhs (generaliseLabFun fun)
generaliseLabFun (Body ex) = Body (generaliseLab ex)

-- Assumes the expression does not contain labelised array variable references
generaliseLabFunA :: HasCallStack => OpenFun env aenv lab alab t -> OpenFun env aenv lab alab' t
generaliseLabFunA (Lam lhs fun) = Lam lhs (generaliseLabFunA fun)
generaliseLabFunA (Body ex) = Body (generaliseLabA ex)

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

    produceGradient :: DMap (Idx args) (ADLabelT Int)
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
        Map ty f e -> Map ty (sinkFunAenv varWeaken <$> f) (go argWeaken varWeaken e)
        ZipWith ty f e1 e2 -> ZipWith ty (sinkFunAenv varWeaken <$> f) (go argWeaken varWeaken e1) (go argWeaken varWeaken e2)
        Fold ty f me0 e -> Fold ty (sinkFunAenv varWeaken <$> f) (sinkExpAenv varWeaken <$> me0) (go argWeaken varWeaken e)
        Backpermute ty dim f e -> Backpermute ty (sinkExpAenv varWeaken dim) (sinkFunAenv varWeaken f) (go argWeaken varWeaken e)
        Permute ty cf def pf e -> Permute ty (sinkFunAenv varWeaken cf) (go argWeaken varWeaken def) (sinkFunAenv varWeaken pf) (go argWeaken varWeaken e)
        Sum ty e -> Sum ty (go argWeaken varWeaken e)
        Generate ty she f -> Generate ty (sinkExpAenv varWeaken she) (sinkFunAenv varWeaken <$> f)
        Replicate ty slt sle e -> Replicate ty slt (sinkExpAenv varWeaken sle) (go argWeaken varWeaken e)
        Reduce ty slt f e -> Reduce ty slt (sinkFunAenv varWeaken f) (go argWeaken varWeaken e)
        Reshape ty she e -> Reshape ty (sinkExpAenv varWeaken she) (go argWeaken varWeaken e)
        Aget ty tidx ex -> Aget ty tidx (go argWeaken varWeaken ex)
        Alet lhs rhs ex
          | A.Exists lhs' <- rebuildLHS lhs ->
              Alet lhs' (go argWeaken varWeaken rhs)
                  (go (A.weakenWithLHS lhs' A..> argWeaken) (A.sinkWithLHS lhs lhs' varWeaken) ex)
        Avar (A.Var ty idx) -> Avar (A.Var ty (varWeaken A.>:> idx))
        Aarg ty@(ArrayR _ _) idx -> Avar (A.Var ty (argWeaken A.>:> idx))
        Alabel _ -> error "realiseArgs: unexpected Label"

-- Map will NOT contain:
-- - Let or Var
-- - Label: the original expression should not have included Label
explode :: ALabVal Int aenv -> OpenAcc aenv unused1 unused2 args t -> IdGen (Exploded (PDExp Int) Int args t)
explode labelenv e =
    trace ("acc explode: exploding " ++ showsAcc (ShowEnv (const "L?") (const "AL?") 0 () []) 9 e "") $
    explode' labelenv e

explode' :: ALabVal Int aenv -> OpenAcc aenv unused1 unused2 args t -> IdGen (Exploded (PDExp Int) Int args t)
explode' labelenv = \case
    e | trace ("acc explode': | " ++ showsAcc (ShowEnv (const "L?") (const "AL?") 0 () ['t' : show i | i <- [1::Int ..]]) 0 e "") False -> undefined
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
        let e' = snd . labeliseExp labelenv . generaliseLabA . generaliseLab $ e
        (lab1, mp1, argmp1) <- explode' labelenv e1
        (lab2, mp2, argmp2) <- explode' labelenv e2
        lab <- genId ty
        let pruned = Acond ty e' (Alabel lab1) (Alabel lab2)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mp2, itemmp]
            argmp = DMap.unionsWithKey (error "explode: Overlapping arg's") [argmp1, argmp2]
        return (lab, mp, argmp)
    Map ty@(ArrayR sht _) (Right e) a -> do
        traceM $ "Calling splitLambdaAD with array labelenv: " ++ showLabelenv labelenv
        e' <- splitLambdaAD labelenv (genSingleId . ArrayR sht) (generaliseLabFun e)
        (lab1, mp1, argmp1) <- explode' labelenv a
        lab <- genId (TupRsingle ty)
        let pruned = Map ty (Left e') (Alabel lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    Map _ (Left _) _ -> error "explode: Unexpected Map SplitLambdaAD"
    ZipWith ty@(ArrayR sht _) (Right e) a1 a2 -> do
        e' <- splitLambdaAD labelenv (genSingleId . ArrayR sht) (generaliseLabFun e)
        (lab1, mp1, argmp1) <- explode' labelenv a1
        (lab2, mp2, argmp2) <- explode' labelenv a2
        lab <- genId (TupRsingle ty)
        let pruned = ZipWith ty (Left e') (Alabel lab1) (Alabel lab2)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mp2, itemmp]
            argmp = DMap.unionsWithKey (error "explode: Overlapping arg's") [argmp1, argmp2]
        return (lab, mp, argmp)
    ZipWith _ (Left _) _ _ -> error "explode: Unexpected ZipWith SplitLambdaAD"
    Fold ty@(ArrayR sht _) (Right e) me0 a -> do
        e' <- splitLambdaAD labelenv (genSingleId . ArrayR sht) (generaliseLabFun e)
        let me0' = snd . labeliseExp labelenv . generaliseLabA . generaliseLab <$> me0
        (lab1, mp1, argmp1) <- explode' labelenv a
        lab <- genId (TupRsingle ty)
        let pruned = Fold ty (Left e') me0' (Alabel lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    Fold _ (Left _) _ _ -> error "explode: Unexpected Fold SplitLambdaAD"
    Backpermute ty dim f a -> do
        let f' = snd . labeliseFun labelenv . generaliseLabFunA . generaliseLabFun $ f
            dim' = snd . labeliseExp labelenv . generaliseLabA . generaliseLab $ dim
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
    Generate _ _ _ -> error "explode: TODO Generate"
    ex@(Replicate ty slt she a) -> do
        let she' = snd . labeliseExp labelenv . generaliseLabA . generaliseLab $ she
        (lab1, mp1, argmp1) <- explode' labelenv a
        lab <- genId (atypeOf ex)
        let pruned = Replicate ty slt she' (Alabel lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    ex@(Reshape ty she a) -> do
        let she' = snd . labeliseExp labelenv . generaliseLabA . generaliseLab $ she
        (lab1, mp1, argmp1) <- explode' labelenv a
        lab <- genId (atypeOf ex)
        let pruned = Reshape ty she' (Alabel lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    Alet lhs rhs body -> do
        (lab1, mp1, argmp1) <- explode' labelenv rhs
        (_, labs) <- genSingleIds (atypeOf rhs)
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
  where
    lpushLHS_Get :: A.ALeftHandSide t aenv aenv' -> TupR (ADLabel Int) t -> ALabVal Int aenv -> Acc lab Int args t -> (ALabVal Int aenv', DMap (ADLabelT Int) (Acc lab Int args))
    lpushLHS_Get lhs labs labelenv' rhs = case (lhs, labs) of
        (A.LeftHandSidePair lhs1 lhs2, TupRpair labs1 labs2) ->
            let (labelenv1, mp1) = lpushLHS_Get lhs1 labs1 labelenv' (smartFst rhs)
                (labelenv2, mp2) = lpushLHS_Get lhs2 labs2 labelenv1 (smartSnd rhs)
            in (labelenv2, DMap.unionWithKey (error "lpushLHS_Get: Overlapping id's") mp1 mp2)
        (A.LeftHandSideSingle _, TupRsingle lab) -> (LPush labelenv' lab, DMap.singleton (tupleLabel lab) rhs)
        (A.LeftHandSideWildcard _, _) -> (labelenv', mempty)
        _ -> error "lpushLHS_Get: impossible GADTs"

computeLabelorder :: Exploded (PDExp Int) Int args t -> [AnyLabelT Int]
computeLabelorder (endlab, nodemap, _) =
    topsort' (\(AnyLabel l) -> labelLabel l)
             alllabels
             (\(AnyLabel l) -> parentmap Map.! labelLabel l)
  where
    parentsOf :: AnyLabelT Int -> [AnyLabelT Int]
    parentsOf (AnyLabel lbl) = accLabelParents (nodemap `dmapFind` lbl)

    alllabels :: [AnyLabelT Int]
    alllabels = Set.toList $ floodfill (AnyLabel endlab) parentsOf mempty

    parentmap :: Map Int [AnyLabelT Int]
    parentmap = Map.fromList [(labelLabel numlbl, parentsOf l)
                             | l@(AnyLabel numlbl) <- alllabels]

showContext :: (Ord alab, Show alab) => AContext alab aenv -> String
showContext (Context labelenv bindmap) = "Context " ++ showLabelenv labelenv ++ " " ++ showBindmap bindmap

showLabelenv :: Show alab => ALabVal alab aenv -> String
showLabelenv LEmpty = "[]"
showLabelenv (LPush env lab) = "[" ++ go env ++ showDLabel lab ++ "]"
  where
    go :: Show alab => ALabVal alab aenv -> String
    go LEmpty = ""
    go (LPush env' lab') = go env' ++ showDLabel lab' ++ ", "

showBindmap :: (Ord alab, Show alab) => DMap (ADLabelT (PDAcc alab)) (TupR (ADLabel alab)) -> String
showBindmap bindmap =
    let tups = sortOn fst [(lab, (showDLabel dlab, showTupR showDLabel labs))
                          | dlab@(DLabel _ lab) :=> labs <- DMap.assocs bindmap]
        s = intercalate ", " ["(" ++ dlabshow ++ ") :=> " ++ labsshow
                             | (_, (dlabshow, labsshow)) <- tups]
    in "[" ++ s ++ "]"

primaldual :: Exploded (PDExp Int) Int args (Array () Float)
           -> (forall aenv. AContext Int aenv -> IdGen (OpenAcc aenv (PDExp Int) (PDAcc Int) args t))
           -> IdGen (Acc (PDExp Int) (PDAcc Int) args t)
primaldual exploded cont =
    let labelorder = computeLabelorder exploded
    in primal exploded (reverse labelorder) (\ctx -> dual exploded labelorder ctx cont)

-- Resulting computation will only use P, never D
primal :: Exploded (PDExp Int) Int args res
       -> [AnyLabelT Int]
       -> (forall aenv. AContext Int aenv -> IdGen (OpenAcc aenv (PDExp Int) (PDAcc Int) args t))
       -> IdGen (Acc (PDExp Int) (PDAcc Int) args t)
primal (_, nodemap, _) labelorder = primal' nodemap labelorder (Context LEmpty mempty)

-- TODO: can't primal' just return the created bindmap entry, so that it
-- doesn't need to be looked up in the bindmap all the time?
primal' :: DMap (ADLabelT Int) (Acc (PDExp Int) Int args)
        -> [AnyLabelT Int]
        -> AContext Int aenv
        -> (forall aenv'. AContext Int aenv' -> IdGen (OpenAcc aenv' (PDExp Int) (PDAcc Int) args res))
        -> IdGen (OpenAcc aenv (PDExp Int) (PDAcc Int) args res)
primal' _ [] context cont = cont context
primal' nodemap (AnyLabel lbl : restlabels) (Context labelenv bindmap) cont
  | trace ("primal': computing " ++ show lbl) False = undefined
  | fmapLabel P lbl `DMap.member` bindmap =
      cont (Context labelenv bindmap)
  | not (uniqueLabVal labelenv) =  -- TODO: remove this check
      error "Non-unique label valuation in primal'!"
  | otherwise =
      case nodemap `dmapFind` lbl of
          Aconst ty value -> do
              lblS <- genSingleId ty
              Alet (A.LeftHandSideSingle ty) (Aconst ty value)
                   <$> primal' nodemap restlabels
                               (Context (LPush labelenv lblS)
                                        (DMap.insert (fmapLabel P lbl) (TupRsingle lblS) bindmap))
                               cont

          Apair _ (Alabel arglab1) (Alabel arglab2) ->
              let labs = TupRpair (bindmap `dmapFind` fmapLabel P arglab1)
                                  (bindmap `dmapFind` fmapLabel P arglab2)
              in -- Note: We don't re-bind the constructed tuple into a new let
                 -- binding with fresh labels here; we just point the tuple label
                 -- for this Pair expression node to the pre-existing scalar labels.
                 primal' nodemap restlabels
                         (Context labelenv
                                  (DMap.insert (fmapLabel P lbl) labs bindmap))
                         cont

          Anil ->
              -- No scalar labels are allocated for a Nil node, but we should still
              -- record that empty set of labels.
              primal' nodemap restlabels
                      (Context labelenv
                               (DMap.insert (fmapLabel P lbl) TupRunit bindmap))
                      cont

          -- TODO: inlining of the produced halves into the branches of the
          -- generated Cond operation, so that the halves are really only
          -- computed if needed.
          -- TODO: Also think about: what if the code contains:
          --   (cond c t e) + (cond (not c) e t)
          -- Because both t and e are shared, they cannot be inlined, and will
          -- thus always be computed, even if in the end only one is needed in
          -- all situations. But then, don't write code like that.
          Acond restype condexpr (Alabel thenlab) (Alabel elselab) ->
              let thenlabs = bindmap `dmapFind` fmapLabel P thenlab
                  elselabs = bindmap `dmapFind` fmapLabel P elselab
              in case (alabValFinds labelenv thenlabs
                      ,alabValFinds labelenv elselabs) of
                  (Just thenvars, Just elsevars) -> do
                      (Exists lhs, labs) <- genSingleIds restype
                      Alet lhs (Acond restype (resolveAlabs (Context labelenv bindmap) condexpr)
                                              (avars thenvars) (avars elsevars))
                           <$> primal' nodemap restlabels
                                       (Context (lpushLabTup labelenv lhs labs)
                                                (DMap.insert (fmapLabel P lbl) labs bindmap))
                                       cont
                  _ ->
                      error "primal: Cond arguments did not compute arguments"

          Map restype@(ArrayR resshape reselty) (Left (SplitLambdaAD lambdaPrimal _ lambdaLabs (lambdaTmpType, lambdaTmpLab))) (Alabel arglab) ->
              let lambdaLabs' = lookupLambdaLabs bindmap lambdaLabs
                  TupRsingle arglabS@(DLabel argtypeS _) = bindmap `dmapFind` fmapLabel P arglab
              in case (alabValFind labelenv arglabS, alabValFinds labelenv lambdaLabs') of
                  (Just argidx, Just lambdaVars) -> do
                      lab <- genSingleId restype
                      let pairEltType = TupRpair reselty lambdaTmpType
                          pairArrType = ArrayR resshape pairEltType
                          tmpArrType = ArrayR resshape lambdaTmpType
                      Alet (A.LeftHandSidePair (A.LeftHandSideSingle restype) (A.LeftHandSideSingle tmpArrType))
                           (Alet (A.LeftHandSideSingle pairArrType)
                                 (Map pairArrType (Right (fmapAlabFun (fmapLabel P) (lambdaPrimal lambdaVars)))
                                                  (Avar (A.Var argtypeS argidx)))
                                 (smartPair
                                      (Map restype (Right (expFstLam pairEltType)) (Avar (A.Var pairArrType ZeroIdx)))
                                      (Map tmpArrType (Right (expSndLam pairEltType)) (Avar (A.Var pairArrType ZeroIdx)))))
                           <$> primal' nodemap restlabels
                                       (Context (LPush (LPush labelenv lab) lambdaTmpLab)
                                                (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                                       cont
                  _ ->
                      error $ "primal: Map arguments did not compute arguments: lbl = " ++ showDLabel lbl ++ "; arglab = " ++ showDLabel arglab ++ "; arglabS = " ++ showDLabel arglabS ++ "; lambdaLabs = " ++ showTupR show lambdaLabs ++ "; lambdaLabs' = " ++ showTupR show lambdaLabs' ++ "; CONTEXT = " ++ showContext (Context labelenv bindmap)

          ZipWith restype@(ArrayR resshape reselty) (Left (SplitLambdaAD lambdaPrimal _ lambdaLabs (lambdaTmpType, lambdaTmpLab))) (Alabel arglab1) (Alabel arglab2) ->
              let lambdaLabs' = lookupLambdaLabs bindmap lambdaLabs
                  TupRsingle arglab1S = bindmap `dmapFind` fmapLabel P arglab1
                  TupRsingle arglab2S = bindmap `dmapFind` fmapLabel P arglab2
              in case (alabValFind labelenv arglab1S, alabValFind labelenv arglab2S, alabValFinds labelenv lambdaLabs') of
                  (Just argidx1, Just argidx2, Just lambdaVars) -> do
                      lab <- genSingleId restype
                      let pairEltType = TupRpair reselty lambdaTmpType
                          pairArrType = ArrayR resshape pairEltType
                          tmpArrType = ArrayR resshape lambdaTmpType
                      Alet (A.LeftHandSidePair (A.LeftHandSideSingle restype) (A.LeftHandSideSingle tmpArrType))
                           (Alet (A.LeftHandSideSingle pairArrType)
                                 (ZipWith pairArrType (Right (fmapAlabFun (fmapLabel P) (lambdaPrimal lambdaVars)))
                                                      (Avar (A.Var (labelType arglab1S) argidx1))
                                                      (Avar (A.Var (labelType arglab2S) argidx2)))
                                 (smartPair
                                      (Map restype (Right (expFstLam pairEltType)) (Avar (A.Var pairArrType ZeroIdx)))
                                      (Map tmpArrType (Right (expSndLam pairEltType)) (Avar (A.Var pairArrType ZeroIdx)))))
                           <$> primal' nodemap restlabels
                                       (Context (LPush (LPush labelenv lab) lambdaTmpLab )
                                                (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                                       cont
                  _ ->
                      error "primal: ZipWith arguments did not compute arguments"

          Fold restype (Left lambda) e0expr (Alabel arglab) ->
              let TupRsingle arglabS@(DLabel argtype _) = bindmap `dmapFind` fmapLabel P arglab
              in case alabValFind labelenv arglabS of
                  Just argidx -> do
                      lab <- genSingleId restype
                      Alet (A.LeftHandSideSingle restype)
                           (Fold restype (Left (fmapAlabSplitLambdaAD (fmapLabel P) lambda))
                                         (resolveAlabs (Context labelenv bindmap) <$> e0expr)
                                         (Avar (A.Var argtype argidx)))
                           <$> primal' nodemap restlabels
                                       (Context (LPush labelenv lab)
                                                (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                                       cont
                  _ ->
                      error "primal: Fold arguments did not compute arguments"

          Sum restype (Alabel arglab) ->
              let TupRsingle arglabS@(DLabel argtype _) = bindmap `dmapFind` fmapLabel P arglab
              in case alabValFind labelenv arglabS of
                  Just argidx -> do
                      lab <- genSingleId restype
                      Alet (A.LeftHandSideSingle restype)
                           (Sum restype (Avar (A.Var argtype argidx)))
                           <$> primal' nodemap restlabels
                                       (Context (LPush labelenv lab)
                                                (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                                       cont
                  _ ->
                      error "primal: Sum arguments did not compute arguments"

          Replicate restype shtype shexp (Alabel arglab) ->
              let TupRsingle arglabS@(DLabel argtype _) = bindmap `dmapFind` fmapLabel P arglab
              in case alabValFind labelenv arglabS of
                   Just argidx -> do
                      lab <- genSingleId restype
                      Alet (A.LeftHandSideSingle restype)
                           (Replicate restype shtype (resolveAlabs (Context labelenv bindmap) shexp) (Avar (A.Var argtype argidx)))
                           <$> primal' nodemap restlabels
                                       (Context (LPush labelenv lab)
                                                (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                                       cont
                   _ ->
                      error "primal: Replicate arguments did not compute arguments"

          Reshape restype shexp (Alabel arglab) ->
              let TupRsingle arglabS@(DLabel argtype _) = bindmap `dmapFind` fmapLabel P arglab
              in case alabValFind labelenv arglabS of
                   Just argidx -> do
                      lab <- genSingleId restype
                      Alet (A.LeftHandSideSingle restype)
                           (Reshape restype (resolveAlabs (Context labelenv bindmap) shexp) (Avar (A.Var argtype argidx)))
                           <$> primal' nodemap restlabels
                                       (Context (LPush labelenv lab)
                                                (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                                       cont
                   _ ->
                      error "primal: Reshape arguments did not compute arguments"

          Backpermute restype shexp indexfunc (Alabel arglab) ->
              let TupRsingle arglabS@(DLabel argtype _) = bindmap `dmapFind` fmapLabel P arglab
              in case alabValFind labelenv arglabS of
                   Just argidx -> do
                      lab <- genSingleId restype
                      Alet (A.LeftHandSideSingle restype)
                           (Backpermute restype (resolveAlabs (Context labelenv bindmap) shexp)
                                                (resolveAlabsFun (Context labelenv bindmap) indexfunc)
                                                (Avar (A.Var argtype argidx)))
                           <$> primal' nodemap restlabels
                                       (Context (LPush labelenv lab)
                                                (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap))
                                       cont
                   _ ->
                      error "primal: Reshape arguments did not compute arguments"

          Aget _ path (Alabel arglab) ->
              let pickedlabs = pickDLabels path (bindmap `dmapFind` fmapLabel P arglab)
              in -- Note: We don't re-bind the picked tuple into a new let binding
                 -- with fresh labels here; we just point the tuple label for this
                 -- Get expression node to the pre-existing scalar labels.
                 primal' nodemap restlabels
                         (Context labelenv
                                  (DMap.insert (fmapLabel P lbl) pickedlabs bindmap))
                         cont

          Aarg ty idx -> do
              labS <- genSingleId ty
              Alet (A.LeftHandSideSingle ty) (Aarg ty idx)
                   <$> primal' nodemap restlabels
                               (Context (LPush labelenv labS)
                                        (DMap.insert (fmapLabel P lbl) (TupRsingle labS) bindmap))
                               cont

          Alabel arglab ->
              let arglabs = bindmap `dmapFind` fmapLabel P arglab
              in -- Note: We don't re-bind the labeled tuple into a new let binding
                 -- with fresh labels here; we just point the tuple label for this
                 -- Label expression node to the pre-existing scalar labels.
                 primal' nodemap restlabels
                         (Context labelenv
                                  (DMap.insert (fmapLabel P lbl) arglabs bindmap))
                         cont

          _ ->
              error "primal: Unexpected node shape in Exploded"
  where
    smartPair :: OpenAcc aenv lab alab args a -> OpenAcc aenv lab alab args b -> OpenAcc aenv lab alab args (a, b)
    smartPair a b = Apair (TupRpair (atypeOf a) (atypeOf b)) a b

    lookupLambdaLabs :: DMap (DLabel (TupR ArrayR) (PDAcc Int)) (TupR (ADLabel Int))  -- bindmap
                     -> TupR (ADLabel Int) t  -- free variable labels from SplitLambdaAD
                     -> TupR (ADLabel Int) t  -- resolved labels pointing into the current labelenv
    lookupLambdaLabs bindmap' =
        fmapTupR $ \lamlab -> case bindmap' `dmapFind` fmapLabel P (tupleLabel lamlab) of
                                  TupRsingle singlelab -> singlelab
                                  _ -> error "Unexpected non-scalar label in free array variables in lambdaLabs"

-- List of adjoints, collected for a particular label.
-- The exact variable references in the adjoints are dependent on the Let stack, thus the
-- environment (and the bindmap) is needed.
newtype AdjList lab alab args t = AdjList (forall aenv. AContext alab aenv -> [OpenAcc aenv lab (PDAcc alab) args t])

type AnyLabelT = AnyLabel ArraysR

dual :: Exploded (PDExp Int) Int args (Array () Float)
     -> [AnyLabelT Int]
     -> AContext Int aenv
     -> (forall aenv'. AContext Int aenv' -> IdGen (OpenAcc aenv' (PDExp Int) (PDAcc Int) args t))
     -> IdGen (OpenAcc aenv (PDExp Int) (PDAcc Int) args t)
dual (endlab, nodemap, _) labelorder context cont =
    let -- TODO: Can I use those scalarType shortcut methods to easily produce more type witnesses elsewhere?
        oneArr = Generate (ArrayR ShapeRz (TupRsingle scalarType))
                          Nil
                          (Right (Lam (A.LeftHandSideWildcard TupRunit)
                                      (Body (Const scalarType 1.0))))
        contribmap = DMap.singleton (fmapLabel D endlab)
                                    (AdjList (const [oneArr]))
    in trace ("\nacc labelorder: " ++ show [labelLabel l | AnyLabel l <- labelorder]) $
       dual' nodemap labelorder context contribmap cont

dual' :: DMap (ADLabelT Int) (Acc (PDExp Int) Int args)
      -> [AnyLabelT Int]
      -> AContext Int aenv
      -> DMap (ADLabelT (PDAcc Int)) (AdjList (PDExp Int) Int args)
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
               <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                     (DMap.insert (fmapLabel D lbl) labs bindmap))
                         contribmap' cont

      Map restype (Left (SplitLambdaAD _ lambdaDual lambdaLabs (_, lambdaTmpLab))) (Alabel arglab) -> do
          let TupRsingle argtypeS = labelType arglab
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil (lambdaLabs :@ TupRsingle lambdaTmpLab :@ TLNil) $
                                    \(TupRsingle adjvar) _ (fvvars :@ TupRsingle lambdaTmpVar :@ TLNil) _ ->
                                        ZipWith argtypeS (Right (fmapAlabFun (fmapLabel P) (lambdaDual fvvars)))
                                                (Avar adjvar) (Avar lambdaTmpVar)]
                                contribmap
          -- technically don't need the tuple machinery here, but for consistency
          (Exists lhs, labs) <- genSingleIds (TupRsingle restype)
          Alet lhs adjoint
               <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                     (DMap.insert (fmapLabel D lbl) labs bindmap))
                         contribmap' cont

      ZipWith restype (Left (SplitLambdaAD _ lambdaDual lambdaLabs (lambdaTmpType, lambdaTmpLab))) (Alabel arglab1) (Alabel arglab2) -> do
          -- This one works a bit differently from the other duals. The dual
          -- lambda computes, for each primal-output array element, a _tuple_
          -- containing the element adjoints for the left and right argument to
          -- the ZipWith. What we want is to "unzip" this array to get the two
          -- adjoint contribution arrays. However, we cannot do this whole
          -- computation at the point of the arguments as we usually do in a
          -- Contribution, because then we compute the ZipWith adjoint twice.
          -- Thus, we compute it once here, immediately, and then in the
          -- Contribution's ignore the ZipWith's adjoint and use the computed
          -- tuple-array directly.
          let TupRsingle argtype1S@(ArrayR shtype arg1elt) = labelType arglab1
              TupRsingle argtype2S@(ArrayR _      arg2elt) = labelType arglab2
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
          templab <- genSingleId (ArrayR shtype (TupRpair arg1elt arg2elt))
          let contribmap' = updateContribmap lbl
                                [Contribution arglab1 TLNil (TupRsingle templab :@ TLNil) $
                                    \_ _ (TupRsingle tempVar :@ TLNil) _ ->
                                        Map argtype1S (Right (expFstLam (TupRpair arg1elt arg2elt))) (Avar tempVar)
                                ,Contribution arglab2 TLNil (TupRsingle templab :@ TLNil) $
                                    \_ _ (TupRsingle tempVar :@ TLNil) _ ->
                                        Map argtype2S (Right (expSndLam (TupRpair arg1elt arg2elt))) (Avar tempVar)]
                                contribmap
          lab <- genSingleId restype
          Alet (A.LeftHandSideSingle restype) adjoint
               <$> let labelenv' = LPush labelenv lab
                   in case (alabValFind labelenv' lambdaTmpLab, alabValFinds labelenv' lambdaLabs) of
                          (Just lambdaTmpVar, Just fvvars) ->
                              Alet (A.LeftHandSideSingle (labelType templab))
                                   (ZipWith (labelType templab) (Right (fmapAlabFun (fmapLabel P) (lambdaDual fvvars)))
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
                                                            (Right (Lam lhs' (Body (Index (Left adjvar) (evars shvars)))))]
                                contribmap
          (Exists lhs, labs) <- genSingleIds (TupRsingle restype)
          Alet lhs adjoint
               <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                     (DMap.insert (fmapLabel D lbl) labs bindmap))
                         contribmap' cont

      Replicate restype@(ArrayR _ eltty) shtype _ (Alabel arglab) -> do
          let TupRsingle argtypeS = labelType arglab
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil TLNil $
                                    \(TupRsingle adjvar) _ _ _ ->
                                        Reduce argtypeS (reduceSpecFromReplicate shtype)
                                               (plusLam eltty) (Avar adjvar)]
                                contribmap
          (Exists lhs, labs) <- genSingleIds (TupRsingle restype)
          Alet lhs adjoint
               <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                     (DMap.insert (fmapLabel D lbl) labs bindmap))
                         contribmap' cont

      Reshape restype@(ArrayR _ eltty) _ (Alabel arglab) -> do
          let TupRsingle (ArrayR shtype' _) = labelType arglab
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) TLNil $
                                    \(TupRsingle adjvar) (TupRsingle pvar :@ TLNil) _ _ ->
                                        Reshape (ArrayR shtype' eltty) (Shape (Left pvar)) (Avar adjvar)]
                                contribmap
          (Exists lhs, labs) <- genSingleIds (TupRsingle restype)
          Alet lhs adjoint
               <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                     (DMap.insert (fmapLabel D lbl) labs bindmap))
                         contribmap' cont

      Backpermute restype@(ArrayR _ eltty) _ (Lam indexfuncLHS (Body indexfuncBody)) (Alabel arglab) -> do
          let TupRsingle argtype@(ArrayR shtypeArg _) = labelType arglab
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) TLNil $
                                    \(TupRsingle adjvar) (TupRsingle pvar :@ TLNil) _ labelenv' ->
                                        Permute argtype (plusLam eltty)
                                                (arraySum argtype (Shape (Left pvar)) [])
                                                (case declareVars (shapeType shtypeArg) of
                                                   DeclareVars lhsArg _ varsgenArg ->
                                                      Lam indexfuncLHS . Body $
                                                          Let lhsArg (resolveAlabs (Context labelenv' bindmap) indexfuncBody)
                                                              (mkJust (evars (varsgenArg A.weakenId))))
                                                (Avar adjvar)]
                                contribmap
          (Exists lhs, labs) <- genSingleIds (TupRsingle restype)
          Alet lhs adjoint
               <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                     (DMap.insert (fmapLabel D lbl) labs bindmap))
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
              <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
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
              <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
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
               <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                     (DMap.insert (fmapLabel D lbl) labs bindmap))
                         contribmap' cont

      expr -> trace ("\n!! " ++ show expr) undefined

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
        Contribution (ADLabelT Int t)  -- to which label are we contributing an adjoint
                     (TypedList (ADLabelT Int) parents)  -- labels you need the primary value of
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
updateContribmap :: ADLabelT Int node
                 -> [Contribution node args]
                 -> DMap (ADLabelT (PDAcc Int)) (AdjList (PDExp Int) Int args)
                 -> DMap (ADLabelT (PDAcc Int)) (AdjList (PDExp Int) Int args)
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
    findAll :: AContext Int aenv -> TypedList (ADLabelT Int) parents -> TypedList (A.ArrayVars aenv) parents
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
                => ADLabelT (PDAcc alab) t
                -> (forall aenv. AContext alab aenv -> OpenAcc aenv lab (PDAcc alab) args t)
                -> DMap (ADLabelT (PDAcc alab)) (AdjList lab alab args)
                -> DMap (ADLabelT (PDAcc alab)) (AdjList lab alab args)
addContribution lbl contribution =
    DMap.insertWith (\(AdjList f1) (AdjList f2) -> AdjList (\context -> f1 context ++ f2 context))
                    lbl
                    (AdjList (pure . contribution))

collectAdjoint :: DMap (ADLabelT (PDAcc Int)) (AdjList lab Int args)
               -> ADLabelT Int item
               -> AContext Int aenv
               -> OpenAcc aenv lab (PDAcc Int) args item
collectAdjoint contribmap lbl (Context labelenv bindmap)
  | Just pvars <- alabValFinds labelenv (bindmap `dmapFind` fmapLabel P lbl)
  = case DMap.lookup (fmapLabel D lbl) contribmap of
        Just (AdjList listgen) -> arraysSum (labelType lbl) pvars (listgen (Context labelenv bindmap))
        Nothing -> arraysSum (labelType lbl) pvars []  -- if there are no contributions, well, the adjoint is an empty sum (i.e. zero)
collectAdjoint _ _ _ = error "Impossible GADTs"

arrayPlus :: OpenAcc aenv lab alab args (Array sh t)
          -> OpenAcc aenv lab alab args (Array sh t)
          -> OpenAcc aenv lab alab args (Array sh t)
arrayPlus a1 a2
  | TupRsingle arrty@(ArrayR _ ty) <- atypeOf a1
  , DeclareVars lhs1 _ vf1 <- declareVars ty
  , DeclareVars lhs2 w2 vf2 <- declareVars ty
  = ZipWith arrty
            (Right (Lam (A.LeftHandSidePair lhs1 lhs2) (Body
                      (expPlus ty (evars (vf1 w2)) (evars (vf2 A.weakenId))))))
            a1 a2
arrayPlus _ _ = error "unreachable"

arraySum :: ArrayR (Array sh t)
         -> Exp aenv lab alab () sh
         -> [OpenAcc aenv lab alab args (Array sh t)]
         -> OpenAcc aenv lab alab args (Array sh t)
arraySum (ArrayR sht ty) she [] = generateConstantArray ty (zeroForType ty) sht she
arraySum _ _ l = foldl1 arrayPlus l

-- TODO: use tupleZip
arraysSum :: ArraysR t
          -> A.ArrayVars aenv t  -- primal result
          -> [OpenAcc aenv lab alab args t]
          -> OpenAcc aenv lab alab args t
arraysSum TupRunit TupRunit _ = Anil
arraysSum (TupRsingle ty@(ArrayR _ _)) (TupRsingle pvar) l = arraySum ty (Shape (Left pvar)) l
arraysSum (TupRpair t1 t2) (TupRpair pvars1 pvars2) l =
    Apair (TupRpair t1 t2)
          (arraysSum t1 pvars1 (map smartFst l))
          (arraysSum t2 pvars2 (map smartSnd l))
arraysSum _ _ _ = error "arraysSum: Invalid GADTs"

generateConstantArray :: TypeR t -> Exp aenv lab alab () t
                      -> ShapeR sh -> Exp aenv lab alab () sh
                      -> OpenAcc aenv lab alab args (Array sh t)
generateConstantArray ty e sht she =
    Generate (ArrayR sht ty) she
             (Right (Lam (A.LeftHandSideWildcard (shapeType sht)) (Body e)))

expFstLam :: TypeR (t1, t2) -> Fun aenv lab alab ((t1, t2) -> t1)
expFstLam (TupRpair t1 t2)
  | LetBoundExpE lhs ex <- elhsCopy t1
  = Lam (A.LeftHandSidePair lhs (A.LeftHandSideWildcard t2)) (Body (evars ex))
expFstLam _ = error "expFstLam: Invalid GADTs"

expSndLam :: TypeR (t1, t2) -> Fun aenv lab alab ((t1, t2) -> t2)
expSndLam (TupRpair t1 t2)
  | LetBoundExpE lhs ex <- elhsCopy t2
  = Lam (A.LeftHandSidePair (A.LeftHandSideWildcard t1) lhs) (Body (evars ex))
expSndLam _ = error "expSndLam: Invalid GADTs"

plusLam :: TypeR t -> Fun aenv lab alab (t -> t -> t)
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

-- Errors if any parents are not Label nodes, or if called on a Let or Var node.
accLabelParents :: OpenAcc aenv lab alab args t -> [AnyLabelT alab]
accLabelParents = \case
    Aconst _ _ -> []
    Apair _ e1 e2 -> fromLabel e1 ++ fromLabel e2
    Anil -> []
    Acond _ _ e1 e2 -> fromLabel e1 ++ fromLabel e2
    Map _ lam e -> fromLabel e ++ lamLabels lam
    ZipWith _ lam e1 e2 -> fromLabel e1 ++ fromLabel e2 ++ lamLabels lam
    Generate _ e lam -> expLabels e ++ lamLabels lam
    Fold _ lam me0 e -> lamLabels lam ++ maybe [] expLabels me0 ++ fromLabel e
    Sum _ e -> fromLabel e
    Replicate _ _ she e -> expLabels she ++ fromLabel e
    Reshape _ she e -> expLabels she ++ fromLabel e
    Backpermute _ she f e -> expLabels she ++ funLabels f ++ fromLabel e
    Aget _ _ e -> fromLabel e
    Aarg _ _ -> []
    Alabel lab -> [AnyLabel lab]
    Alet _ _ _ -> unimplemented "Alet"
    Avar _ -> unimplemented "Avar"
    Reduce _ _ _ _ -> error "Unexpected Reduce in accLabelParents (should only be created in dual)"
  where
    unimplemented name =
        error ("accLabelParents: Unimplemented for " ++ name ++ ", semantics unclear")

    fromLabel (Alabel lab) = [AnyLabel lab]
    fromLabel _ = error "accLabelParents: Parent is not a label"

    expLabels :: OpenExp env aenv lab alab args t -> [AnyLabel ArraysR alab]
    expLabels e = [AnyLabel (tupleLabel lab) | AnyLabel lab <- expALabels e]

    funLabels :: OpenFun env aenv lab alab t -> [AnyLabel ArraysR alab]
    funLabels (Lam _ f) = funLabels f
    funLabels (Body e) = expLabels e

    lamLabels :: ExpLambda1 aenv lab alab sh t1 t2 -> [AnyLabel ArraysR alab]
    lamLabels (Left (SplitLambdaAD _ _ fvtup _)) = [AnyLabel (tupleLabel lab) | Some lab <- enumerateTupR fvtup]
    lamLabels (Right fun) = [AnyLabel (tupleLabel lab) | AnyLabel lab <- expFunALabels fun]

resolveAlabs :: (Ord alab, Show alab)
             => AContext alab aenv
             -> OpenExp env aenv' lab alab args t
             -> OpenExp env aenv lab alab' args t
resolveAlabs (Context labelenv bindmap) =
    inlineAvarLabels' $ \lab ->
        case bindmap `dmapFind` tupleLabel (fmapLabel P lab) of
            labs -> case alabValFinds labelenv labs of
                Just (TupRsingle var) -> var
                Just _ -> error $ "Array label in labelised expression refers to tuple?: " ++ show lab
                Nothing -> error $ "Array label in labelised expression not found in env: " ++ show lab

resolveAlabsFun :: (Ord alab, Show alab)
                => AContext alab aenv
                -> OpenFun env aenv' lab alab t
                -> OpenFun env aenv lab alab' t
resolveAlabsFun ctx (Lam lhs fun) = Lam lhs (resolveAlabsFun ctx fun)
resolveAlabsFun ctx (Body e) = Body (resolveAlabs ctx e)

dmapFind :: (HasCallStack, GCompare f) => DMap f g -> f a -> g a
dmapFind mp elt = case DMap.lookup elt mp of
                    Just res -> res
                    Nothing -> error "dmapFind: not found"

-- TODO: make smartFst and smartSnd non-quadratic (should be easy)
smartFst :: OpenAcc aenv lab alab args (t1, t2) -> OpenAcc aenv lab alab args t1
smartFst (Apair _ ex _) = ex
smartFst (Aget (TupRpair t1 _) tidx ex) = Aget t1 (insertFst tidx) ex
  where insertFst :: TupleIdx t (t1, t2) -> TupleIdx t t1
        insertFst TIHere = TILeft TIHere
        insertFst (TILeft ti) = TILeft (insertFst ti)
        insertFst (TIRight ti) = TIRight (insertFst ti)
smartFst ex
  | TupRpair t1 _ <- atypeOf ex
  = Aget t1 (TILeft TIHere) ex
smartFst _ = error "smartFst: impossible GADTs"

smartSnd :: OpenAcc aenv lab alab args (t1, t2) -> OpenAcc aenv lab alab args t2
smartSnd (Apair _ _ ex) = ex
smartSnd (Aget (TupRpair _ t2) tidx ex) = Aget t2 (insertSnd tidx) ex
  where insertSnd :: TupleIdx t (t1, t2) -> TupleIdx t t2
        insertSnd TIHere = TIRight TIHere
        insertSnd (TILeft ti) = TILeft (insertSnd ti)
        insertSnd (TIRight ti) = TIRight (insertSnd ti)
smartSnd ex
  | TupRpair _ t2 <- atypeOf ex
  = Aget t2 (TIRight TIHere) ex
smartSnd _ = error "smartSnd: impossible GADTs"
