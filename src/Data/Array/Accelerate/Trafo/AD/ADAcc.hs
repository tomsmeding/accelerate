{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS -Wno-unused-imports #-}  -- TODO: remove
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
import Data.Type.Equality
import Data.GADT.Compare (GCompare)

import Debug.Trace

import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Environment as A
import qualified Data.Array.Accelerate.AST.Idx as A
import qualified Data.Array.Accelerate.AST.LeftHandSide as A
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.Error (internalError, HasCallStack)
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (ShapeR(..), shapeType)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.AD.Acc
import Data.Array.Accelerate.Trafo.AD.Additive
import Data.Array.Accelerate.Trafo.AD.ADExp (splitLambdaAD)
import Data.Array.Accelerate.Trafo.AD.Algorithms
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.TupleZip
import Data.Array.Accelerate.Trafo.AD.Sink
import Data.Array.Accelerate.Trafo.Var (declareVars, DeclareVars(..))


type AContext = Context ArrayR PDAuxTagAcc


genId :: ArraysR t -> IdGen (ADLabelT Int t)
genId = genId'

genSingleId :: ArrayR t -> IdGen (ADLabel Int t)
genSingleId = genId'

genSingleIds :: ArraysR t -> IdGen (GenLHS ArrayR aenv t, TupR (ADLabel Int) t)
genSingleIds TupRunit = return (GenLHS (A.LeftHandSideWildcard TupRunit), TupRunit)
genSingleIds (TupRsingle ty) = (GenLHS (A.LeftHandSideSingle ty),) . TupRsingle <$> genSingleId ty
genSingleIds (TupRpair t1 t2) = do
    (GenLHS lhs1, ids1) <- genSingleIds t1
    (GenLHS lhs2, ids2) <- genSingleIds t2
    return (GenLHS (A.LeftHandSidePair lhs1 lhs2), TupRpair ids1 ids2)


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
                  -- return $ produceGradient argLabelMap context argsRHS  -- TODO
                  return Asnowman
      in
          trace ("Acc AD result: " ++ show transformedExp) $
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
        Sum ty e -> Sum ty (go argWeaken varWeaken e)
        Generate ty she f -> Generate ty (sinkExpAenv varWeaken she) (sinkFunAenv varWeaken <$> f)
        Aget ty tidx ex -> Aget ty tidx (go argWeaken varWeaken ex)
        Alet lhs rhs ex
          | GenLHS lhs' <- generaliseLHS lhs ->
              Alet lhs' (go argWeaken varWeaken rhs)
                  (go (A.weakenWithLHS lhs' A..> argWeaken) (A.sinkWithLHS lhs lhs' varWeaken) ex)
        Avar (A.Var ty idx) -> Avar (A.Var ty (varWeaken A.>:> idx))
        Aarg ty@(ArrayR _ _) idx -> Avar (A.Var ty (argWeaken A.>:> idx))
        Alabel _ -> error "realiseArgs: unexpected Label"

-- Map will NOT contain:
-- - Let or Var
-- - Label: the original expression should not have included Label
explode :: ALabVal Int aenv -> OpenAcc aenv unused1 unused2 args t -> IdGen (Exploded (PDExp Int) {- TODO is PD Int correct? -} Int args t)
explode labelenv e =
    trace ("acc explode: exploding " ++ showsAcc (const "L?") (const "AL?") 0 [] 9 e "") $
    explode' labelenv e

explode' :: ALabVal Int aenv -> OpenAcc aenv unused1 unused2 args t -> IdGen (Exploded (PDExp Int) Int args t)
explode' labelenv = \case
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
        let e' = doesNotContainArrayVars (generaliseLabA (generaliseLab e))  -- TODO: proper handling of array variables in non-lambda expressions
        (lab1, mp1, argmp1) <- explode' labelenv e1
        (lab2, mp2, argmp2) <- explode' labelenv e2
        lab <- genId ty
        let pruned = Acond ty e' (Alabel lab1) (Alabel lab2)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mp2, itemmp]
            argmp = DMap.unionsWithKey (error "explode: Overlapping arg's") [argmp1, argmp2]
        return (lab, mp, argmp)
    Map ty@(ArrayR sht _) (Right e) a -> do
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
        let me0' = doesNotContainArrayVars . generaliseLabA . generaliseLab <$> me0
        (lab1, mp1, argmp1) <- explode' labelenv a
        lab <- genId (TupRsingle ty)
        let pruned = Fold ty (Left e') me0' (Alabel lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    Fold _ (Left _) _ _ -> error "explode: Unexpected Fold SplitLambdaAD"
    Sum ty a -> do
        (lab1, mp1, argmp1) <- explode' labelenv a
        lab <- genId (TupRsingle ty)
        let pruned = Sum ty (Alabel lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    Generate _ _ _ -> error "explode: TODO Generate"
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

    -- TODO: make smartFst and smartSnd non-quadratic (should be easy)
    smartFst :: OpenAcc aenv lab alab args (t1, t2) -> OpenAcc aenv lab alab args t1
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
    smartSnd (Aget (TupRpair _ t2) tidx ex) = Aget t2 (insertSnd tidx) ex
      where insertSnd :: TupleIdx t (t1, t2) -> TupleIdx t t2
            insertSnd TIHere = TIRight TIHere
            insertSnd (TILeft ti) = TILeft (insertSnd ti)
            insertSnd (TIRight ti) = TIRight (insertSnd ti)
    smartSnd ex
      | TupRpair _ t2 <- atypeOf ex
      = Aget t2 (TIRight TIHere) ex
    smartSnd _ = error "smartSnd: impossible GADTs"

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
    primal exploded (\ctx -> dual exploded ctx cont)  -- TODO
    -- primal exploded cont

-- Resulting computation will only use P, never D
primal :: Exploded (PDExp Int) Int args res
       -> (forall aenv. AContext Int aenv -> IdGen (OpenAcc aenv (PDExp Int) (PDAcc Int) args t))
       -> IdGen (Acc (PDExp Int) (PDAcc Int) args t)
primal (endlab, nodemap, _) = primal' nodemap endlab (Context LEmpty mempty)

-- TODO: can't primal' just return the created bindmap entry, so that it
-- doesn't need to be looked up in the bindmap all the time?
primal' :: DMap (ADLabelT Int) (Acc (PDExp Int) Int args)
        -> ADLabelT Int t
        -> AContext Int aenv
        -> (forall aenv'. AContext Int aenv' -> IdGen (OpenAcc aenv' (PDExp Int) (PDAcc Int) args res))
        -> IdGen (OpenAcc aenv (PDExp Int) (PDAcc Int) args res)
primal' nodemap lbl (Context labelenv bindmap) cont
--   | trace ("primal': computing " ++ show lbl) False = undefined
  | fmapLabel P lbl `DMap.member` bindmap =
      cont (Context labelenv bindmap)
  | not (uniqueLabVal labelenv) =  -- TODO: remove this check
      error "Non-unique label valuation in primal'!"
  | otherwise =
      case nodemap `dmapFind` lbl of
          Aconst ty value -> do
              lblS <- genSingleId ty
              Alet (A.LeftHandSideSingle ty) (Aconst ty value)
                   <$> cont (Context (LPush labelenv lblS)
                                     (DMap.insert (fmapLabel P lbl) (TupRsingle lblS) bindmap))

          Apair _ (Alabel arglab1) (Alabel arglab2) ->
              primal' nodemap arglab1 (Context labelenv bindmap) $ \ctx1 ->
              primal' nodemap arglab2 ctx1 $ \(Context labelenv' bindmap') ->
                  let labs = TupRpair (bindmap' `dmapFind` fmapLabel P arglab1)
                                      (bindmap' `dmapFind` fmapLabel P arglab2)
                  in -- Note: We don't re-bind the constructed tuple into a new let
                     -- binding with fresh labels here; we just point the tuple label
                     -- for this Pair expression node to the pre-existing scalar labels.
                     cont (Context labelenv'
                                   (DMap.insert (fmapLabel P lbl) labs bindmap'))

          Anil ->
              -- No scalar labels are allocated for a Nil node, but we should still
              -- record that empty set of labels.
              cont (Context labelenv
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
              primal' nodemap thenlab (Context labelenv bindmap) $ \ctx1 ->
              primal' nodemap elselab ctx1 $ \(Context labelenv' bindmap') ->
                  let thenlabs = bindmap' `dmapFind` fmapLabel P thenlab
                      elselabs = bindmap' `dmapFind` fmapLabel P elselab
                  in case (alabValFinds labelenv' thenlabs
                          ,alabValFinds labelenv' elselabs) of
                      (Just thenvars, Just elsevars) -> do
                          (GenLHS lhs, labs) <- genSingleIds restype
                          Alet lhs (Acond restype (doesNotContainArrayVars (generaliseLabA condexpr))
                                                  (avars thenvars) (avars elsevars))
                               <$> cont (Context (lpushLabTup labelenv' lhs labs)
                                                 (DMap.insert (fmapLabel P lbl) labs bindmap'))
                      _ ->
                          error "primal: Cond arguments did not compute arguments"

          Map restype@(ArrayR resshape reselty) (Left (SplitLambdaAD lambdaPrimal _ lambdaLabs (lambdaTmpType, lambdaTmpLab))) (Alabel arglab) ->
              primal' nodemap arglab (Context labelenv bindmap) $ \(Context labelenv' bindmap') ->
                  let TupRsingle arglabS@(DLabel argtypeS _) = bindmap' `dmapFind` fmapLabel P arglab
                  in case (alabValFind labelenv' arglabS, alabValFinds labelenv' lambdaLabs) of
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
                               <$> cont (Context (LPush (LPush labelenv' lab) lambdaTmpLab)
                                                 (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap'))
                      _ ->
                          error "primal: Map arguments did not compute arguments"

          ZipWith restype (Left lambda) (Alabel arglab1) (Alabel arglab2) ->
              primal' nodemap arglab1 (Context labelenv bindmap) $ \ctx1 ->
              primal' nodemap arglab2 ctx1 $ \(Context labelenv' bindmap') ->
                  let TupRsingle arglab1S = bindmap' `dmapFind` fmapLabel P arglab1
                      TupRsingle arglab2S = bindmap' `dmapFind` fmapLabel P arglab2
                  in case (alabValFind labelenv' arglab1S, alabValFind labelenv' arglab2S) of
                      (Just argidx1, Just argidx2) -> do
                          lab <- genSingleId restype
                          Alet (A.LeftHandSideSingle restype)
                               (ZipWith restype (Left (fmapAlabSplitLambdaAD (fmapLabel P) lambda))
                                                (Avar (A.Var (labelType arglab1S) argidx1))
                                                (Avar (A.Var (labelType arglab2S) argidx2)))
                               <$> cont (Context (LPush labelenv' lab)
                                                 (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap'))
                      _ ->
                          error "primal: ZipWith arguments did not compute arguments"

          Fold restype (Left lambda) e0expr (Alabel arglab) ->
              primal' nodemap arglab (Context labelenv bindmap) $ \(Context labelenv' bindmap') ->
                  let TupRsingle arglabS@(DLabel argtype _) = bindmap' `dmapFind` fmapLabel P arglab
                  in case alabValFind labelenv' arglabS of
                      Just argidx -> do
                          lab <- genSingleId restype
                          Alet (A.LeftHandSideSingle restype)
                               (Fold restype (Left (fmapAlabSplitLambdaAD (fmapLabel P) lambda))
                                             (doesNotContainArrayVars . generaliseLabA <$> e0expr)
                                             (Avar (A.Var argtype argidx)))
                               <$> cont (Context (LPush labelenv' lab)
                                                 (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap'))
                      _ ->
                          error "primal: Fold arguments did not compute arguments"

          Sum restype (Alabel arglab) ->
              primal' nodemap arglab (Context labelenv bindmap) $ \(Context labelenv' bindmap') ->
                  let TupRsingle arglabS@(DLabel argtype _) = bindmap' `dmapFind` fmapLabel P arglab
                  in case alabValFind labelenv' arglabS of
                      Just argidx -> do
                          lab <- genSingleId restype
                          Alet (A.LeftHandSideSingle restype)
                               (Sum restype (Avar (A.Var argtype argidx)))
                               <$> cont (Context (LPush labelenv' lab)
                                                 (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap'))
                      _ ->
                          error "primal: Sum arguments did not compute arguments"

          Aget _ path (Alabel arglab) ->
              primal' nodemap arglab (Context labelenv bindmap) $ \(Context labelenv' bindmap') ->
                  let pickedlabs = pickDLabels path (bindmap' `dmapFind` fmapLabel P arglab)
                  in -- Note: We don't re-bind the picked tuple into a new let binding
                     -- with fresh labels here; we just point the tuple label for this
                     -- Get expression node to the pre-existing scalar labels.
                     cont (Context labelenv'
                                   (DMap.insert (fmapLabel P lbl) pickedlabs bindmap'))

          Aarg ty idx -> do
              labS <- genSingleId ty
              Alet (A.LeftHandSideSingle ty) (Aarg ty idx)
                   <$> cont (Context (LPush labelenv labS)
                                     (DMap.insert (fmapLabel P lbl) (TupRsingle labS) bindmap))

          Alabel arglab ->
              primal' nodemap arglab (Context labelenv bindmap) $ \(Context labelenv' bindmap') ->
                  let arglabs = bindmap' `dmapFind` fmapLabel P arglab
                  in -- Note: We don't re-bind the labeled tuple into a new let binding
                     -- with fresh labels here; we just point the tuple label for this
                     -- Label expression node to the pre-existing scalar labels.
                     cont (Context labelenv'
                                   (DMap.insert (fmapLabel P lbl) arglabs bindmap'))

          _ ->
              error "primal: Unexpected node shape in Exploded"
  where
    smartPair :: OpenAcc aenv lab alab args a -> OpenAcc aenv lab alab args b -> OpenAcc aenv lab alab args (a, b)
    smartPair a b = Apair (TupRpair (atypeOf a) (atypeOf b)) a b

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

-- List of adjoints, collected for a particular label.
-- The exact variable references in the adjoints are dependent on the Let stack, thus the
-- environment (and the bindmap) is needed.
newtype AdjList lab alab args t = AdjList (forall aenv. AContext alab aenv -> [OpenAcc aenv lab (PDAcc alab) args t])

type AnyLabelT = AnyLabel ArraysR

-- The Ord and Eq instances refer only to 'a'.
data OrdBox a b = OrdBox { _ordboxTag :: a, ordboxAuxiliary :: b }
instance Eq  a => Eq  (OrdBox a b) where OrdBox x _    ==     OrdBox y _ = x == y
instance Ord a => Ord (OrdBox a b) where OrdBox x _ `compare` OrdBox y _ = compare x y

dual :: Exploded (PDExp Int) Int args (Array () Float)
     -> AContext Int aenv
     -> (forall aenv'. AContext Int aenv' -> IdGen (OpenAcc aenv' (PDExp Int) (PDAcc Int) args t))
     -> IdGen (OpenAcc aenv (PDExp Int) (PDAcc Int) args t)
dual (endlab, nodemap, _) context cont =
    trace ("\nacc labelorder: " ++ show [labelLabel l | AnyLabel l <- labelorder]) $
    -- TODO: Can I use those scalarType shortcut methods to easily produce more type witnesses elsewhere?
    let contribmap = DMap.singleton (fmapLabel D endlab)
                                    (AdjList (const [let typ = ArrayR ShapeRz (TupRsingle scalarType)
                                                     in Aconst typ (fromList typ () [1.0])]))
    in dual' nodemap labelorder context contribmap cont
  where
    -- Every numeric label is unique; we don't need the type information for that.
    -- We play fast and loose with that here: we use an 'OrdBox' for 'floodfill'
    -- to use the 'Ord' instance on 'Int' while carrying along the full 'DLabel'
    -- objects, and we index the 'parentmap' on the integer value too.
    parentsOf :: AnyLabelT Int -> [AnyLabelT Int]
    parentsOf (AnyLabel lbl) = expLabelParents context (nodemap `dmapFind` lbl)

    alllabels :: [AnyLabelT Int]
    alllabels =
        map ordboxAuxiliary . Set.toList
            $ floodfill (OrdBox (labelLabel endlab) (AnyLabel endlab))
                        (\box -> [OrdBox (labelLabel l) (AnyLabel l)
                                 | AnyLabel l <- parentsOf (ordboxAuxiliary box)])
                        mempty

    parentmap :: Map Int [AnyLabelT Int]
    parentmap = Map.fromList [(labelLabel numlbl, parentsOf l)
                             | l@(AnyLabel numlbl) <- alllabels]

    labelorder :: [AnyLabelT Int]
    labelorder = topsort' (\(AnyLabel l) -> labelLabel l)
                          alllabels
                          (\(AnyLabel l) -> parentmap Map.! labelLabel l)

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
                                [Contribution thenlab (lbl :@ TLNil) TLNil $ \adjvars (pvars :@ TLNil) _ ->
                                    Acond restype (doesNotContainArrayVars (generaliseLabA condexp))
                                                  (avars adjvars) (arraysSum restype pvars [])
                                ,Contribution elselab (lbl :@ TLNil) TLNil $ \adjvars (pvars :@ TLNil) _ ->
                                    Acond restype (doesNotContainArrayVars (generaliseLabA condexp))
                                                  (arraysSum restype pvars []) (avars adjvars)]
                                contribmap
          (GenLHS lhs, labs) <- genSingleIds restype
          Alet lhs adjoint
               <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                     (DMap.insert (fmapLabel D lbl) labs bindmap))
                         contribmap' cont

      Map restype (Left (SplitLambdaAD _ lambdaDual lambdaLabs (_, lambdaTmpLab))) (Alabel arglab) -> do
          let TupRsingle argtypeS = labelType arglab
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil (lambdaLabs :@ TupRsingle lambdaTmpLab :@ TLNil) $
                                    \(TupRsingle adjvar) _ (fvvars :@ TupRsingle lambdaTmpVar :@ TLNil) ->
                                        ZipWith argtypeS (Right (fmapAlabFun (fmapLabel P) (lambdaDual fvvars)))
                                                (Avar adjvar) (Avar lambdaTmpVar)]
                                contribmap
          -- technically don't need the tuple machinery here, but for consistency
          (GenLHS lhs, labs) <- genSingleIds (TupRsingle restype)
          Alet lhs adjoint
               <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                     (DMap.insert (fmapLabel D lbl) labs bindmap))
                         contribmap' cont

      Sum restype@(ArrayR sht _) (Alabel arglab) -> do
          let TupRsingle argtypeS = labelType arglab
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) TLNil $
                                    \(TupRsingle adjvar) (TupRsingle pvar :@ TLNil) _ ->
                                        case elhsCopy (shapeType sht) of
                                            LetBoundExpE lhs shvars ->
                                                let lhs' = A.LeftHandSidePair lhs
                                                              (A.LeftHandSideWildcard (TupRsingle scalarType))
                                                in Generate argtypeS (Shape (Left pvar))
                                                            (Right (Lam lhs' (Body (Index (Left adjvar) (evars shvars)))))]
                                contribmap
          (GenLHS lhs, labs) <- genSingleIds (TupRsingle restype)
          Alet lhs adjoint
               <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                     (DMap.insert (fmapLabel D lbl) labs bindmap))
                         contribmap' cont

      -- Get restype path (Label arglab) -> do
      --     let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
      --         contribmap' = updateContribmap lbl
      --                           [Contribution arglab TLNil $ \adjvars _ ->
      --                               oneHotTup (labelType arglab) path (evars adjvars)]
      --                           contribmap
      --     (GenLHS lhs, labs) <- genScalarIds restype
      --     Let lhs adjoint
      --         <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
      --                                               (DMap.insert (fmapLabel D lbl) labs bindmap))
      --                   contribmap' cont

      -- Pair restype (Label arglab1) (Label arglab2) -> do
      --     let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
      --         contribmap' = updateContribmap lbl
      --                           [Contribution arglab1 TLNil $ \(TupRpair adjvars1 _) _ ->
      --                               evars adjvars1
      --                           ,Contribution arglab2 TLNil $ \(TupRpair _ adjvars2) _ ->
      --                               evars adjvars2]
      --                           contribmap
      --     (GenLHS lhs, labs) <- genScalarIds restype
      --     Let lhs adjoint
      --         <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
      --                                               (DMap.insert (fmapLabel D lbl) labs bindmap))
      --                   contribmap' cont

      -- Nil ->
      --     -- Nothing to compute here, but we still need to register this expression label
      --     -- in the bindmap.
      --     dual' nodemap restlabels (Context labelenv
      --                                       (DMap.insert (fmapLabel D lbl) TupRunit bindmap))
      --           contribmap cont

      Alabel arglab -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil TLNil $ \adjvars _ _ ->
                                    avars adjvars]
                                contribmap
          (GenLHS lhs, labs) <- genSingleIds (labelType arglab)
          Alet lhs adjoint
               <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                     (DMap.insert (fmapLabel D lbl) labs bindmap))
                         contribmap' cont

      expr -> trace ("\n!! " ++ show expr) undefined
  where
    smartPair :: OpenAcc aenv lab alab args a -> OpenAcc aenv lab alab args b -> OpenAcc aenv lab alab args (a, b)
    smartPair a b = Apair (TupRpair (atypeOf a) (atypeOf b)) a b

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
                (Just adjvars, parvars, scalvars) -> gen adjvars parvars scalvars
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
          (arraysSum t1 pvars1 (map (Aget t1 (TILeft TIHere)) l))
          (arraysSum t2 pvars2 (map (Aget t2 (TIRight TIHere)) l))
arraysSum _ _ _ = error "arraysSum: Invalid GADTs"

generateConstantArray :: TypeR t -> Exp aenv lab alab () t
                      -> ShapeR sh -> Exp aenv lab alab () sh
                      -> OpenAcc aenv lab alab args (Array sh t)
generateConstantArray ty e sht she =
    Generate (ArrayR sht ty) she
             (Right (Lam (A.LeftHandSideWildcard (shapeType sht)) (Body e)))

-- TODO: not yet converted to array language
-- oneHotTup :: TypeR t -> TupleIdx t t' -> OpenAcc aenv lab args t' -> OpenAcc aenv lab args t
-- oneHotTup _ TIHere ex = ex
-- oneHotTup ty@(TupRpair ty1 ty2) (TILeft ti) ex = Pair ty (oneHotTup ty1 ti ex) (zeroForType ty2)
-- oneHotTup ty@(TupRpair ty1 ty2) (TIRight ti) ex = Pair ty (zeroForType ty1) (oneHotTup ty2 ti ex)
-- oneHotTup _ _ _ = error "oneHotTup: impossible GADTs"

-- Errors if any parents are not Label nodes, or if called on a Let or Var node.
expLabelParents :: Ord alab => AContext alab aenv' -> OpenAcc aenv lab alab args t -> [AnyLabelT alab]
expLabelParents ctx = \case
    Aconst _ _ -> []
    Apair _ e1 e2 -> fromLabel e1 ++ fromLabel e2
    Anil -> []
    Acond _ _ e1 e2 -> fromLabel e1 ++ fromLabel e2
    Map _ lam e -> fromLabel e ++ lamLabels ctx lam
    Sum _ e -> fromLabel e
    Aget _ _ e -> fromLabel e
    Aarg _ _ -> []
    Alabel lab -> [AnyLabel lab]
    Alet _ _ _ -> unimplemented "Alet"
    Avar _ -> unimplemented "Avar"
  where
    unimplemented name =
        error ("expLabelParents: Unimplemented for " ++ name ++ ", semantics unclear")

    fromLabel (Alabel lab) = [AnyLabel lab]
    fromLabel _ = error "expLabelParents: Parent is not a label set"

    -- TODO: this is about the ugliest function around here (both due to the P assumption and the performance problem of using flipBindmap); fix this
    lamLabels :: Ord alab => AContext alab aenv' -> ExpLambda1 aenv lab alab sh t1 t2 -> [AnyLabel ArraysR alab]
    lamLabels _ (Left _) = []
    lamLabels (Context _ bindmap) (Right fun) =
        let lookupDict = flipBindmap bindmap
        in [case lookupDict Map.! AnyLabel lab of
                AnyLabel tlab -> AnyLabel (fmapLabel (\(P ptlab) -> ptlab) tlab)
           | AnyLabel lab <- expFunALabels fun]

    flipBindmap :: Ord alab
                => DMap (ADLabelT (PDAcc alab)) (TupR (ADLabel alab))
                -> Map (AnyLabel ArrayR alab) (AnyLabel ArraysR (PDAcc alab))
    flipBindmap bindmap =
        Map.fromList $ concat [map (,AnyLabel tlab) (allLabelsInTup labtup)
                              | tlab :=> labtup <- DMap.assocs bindmap]
      where
        allLabelsInTup :: TupR (ADLabel alab) t -> [AnyLabel ArrayR alab]
        allLabelsInTup TupRunit = []
        allLabelsInTup (TupRsingle lab) = [AnyLabel lab]
        allLabelsInTup (TupRpair t1 t2) = allLabelsInTup t1 ++ allLabelsInTup t2

dmapFind :: (HasCallStack, GCompare f) => DMap f g -> f a -> g a
dmapFind mp elt = case DMap.lookup elt mp of
                    Just res -> res
                    Nothing -> error "dmapFind: not found"
