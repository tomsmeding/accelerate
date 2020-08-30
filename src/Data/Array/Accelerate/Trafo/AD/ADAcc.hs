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
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.AD.Acc
import Data.Array.Accelerate.Trafo.AD.Algorithms
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.TupleZip
import Data.Array.Accelerate.Trafo.AD.Sink
import Data.Array.Accelerate.Trafo.Var (declareVars, DeclareVars(..))


genId :: ArraysR t -> IdGen (ADLabelT Int t)
genId = genId'

genSingleId :: ArrayR t -> IdGen (ADLabel Int t)
genSingleId = genId'

genSingleIds :: ArraysR t -> IdGen (GenLHS ArrayR env t, TupR (ADLabel Int) t)
genSingleIds TupRunit = return (GenLHS (A.LeftHandSideWildcard TupRunit), TupRunit)
genSingleIds (TupRsingle ty) = (GenLHS (A.LeftHandSideSingle ty),) . TupRsingle <$> genSingleId ty
genSingleIds (TupRpair t1 t2) = do
    (GenLHS lhs1, ids1) <- genSingleIds t1
    (GenLHS lhs2, ids2) <- genSingleIds t2
    return (GenLHS (A.LeftHandSidePair lhs1 lhs2), TupRpair ids1 ids2)


-- TODO: make this a data definition, not a tuple
type Exploded lab args res = (ADLabelT lab res, DMap (ADLabelT lab) (Acc lab args), DMap (A.Idx args) (ADLabelT lab))

showExploded :: (Ord lab, Show lab) => Exploded lab args t -> String
showExploded (endlab, nodemap, argmap) =
    "(" ++ showDLabel endlab ++ ", " ++ showNodemap nodemap ++ ", " ++ showArgmap argmap ++ ")"

showNodemap :: (Ord lab, Show lab) => DMap (ADLabelT lab) (Acc lab args) -> String
showNodemap nodemap =
    let tups = sortOn fst [(lab, (showDLabel dlab, show expr))
                          | dlab@(DLabel _ lab) :=> expr <- DMap.assocs nodemap]
        s = intercalate ", " ["(" ++ dlabshow ++ ") :=> " ++ exprshow
                             | (_, (dlabshow, exprshow)) <- tups]
    in "[" ++ s ++ "]"

showArgmap :: Show lab => DMap (A.Idx args) (ADLabelT lab) -> String
showArgmap argmap =
    let s = intercalate ", " ['A' : show (A.idxToInt argidx) ++ " :=> " ++ showDLabel dlab
                             | argidx :=> dlab <- DMap.assocs argmap]
    in "[" ++ s ++ "]"

data ExpandLHS s t env env1
    = forall env2. ExpandLHS (A.LeftHandSide s t env env2) (env1 A.:> env2)

-- Eliminates all Wildcard bindings.
expandLHS :: A.LeftHandSide s t env0 env1 -> ExpandLHS s t env0 env1
expandLHS lhs@(A.LeftHandSideSingle _) = ExpandLHS lhs A.weakenId
expandLHS (A.LeftHandSidePair lhs1 lhs2)
  | ExpandLHS lhs1' weaken1 <- expandLHS lhs1
  , GenLHS lhs2gen <- generaliseLHS lhs2
  , ExpandLHS lhs2' weaken2 <- expandLHS lhs2gen
  = ExpandLHS (A.LeftHandSidePair lhs1' lhs2')
              (weaken2 A..> A.sinkWithLHS lhs2 lhs2gen weaken1)
expandLHS lhs@(A.LeftHandSideWildcard TupRunit) = ExpandLHS lhs A.weakenId
expandLHS (A.LeftHandSideWildcard (TupRsingle sty)) =
    ExpandLHS (A.LeftHandSideSingle sty) (A.weakenSucc' A.weakenId)
expandLHS (A.LeftHandSideWildcard (TupRpair t1 t2))
  | ExpandLHS lhs1' weaken1 <- expandLHS (A.LeftHandSideWildcard t1)
  , ExpandLHS lhs2' weaken2 <- expandLHS (A.LeftHandSideWildcard t2)
  = ExpandLHS (A.LeftHandSidePair lhs1' lhs2') (weaken2 A..> weaken1)

-- Assumes the LeftHandSide's are equal in structure
sameLHSsameEnv :: A.LeftHandSide s t env env1 -> A.LeftHandSide s t env env2 -> env1 :~: env2
sameLHSsameEnv (A.LeftHandSideWildcard _) (A.LeftHandSideWildcard _) = Refl
sameLHSsameEnv (A.LeftHandSideSingle _) (A.LeftHandSideSingle _) = Refl
sameLHSsameEnv (A.LeftHandSidePair a b) (A.LeftHandSidePair c d)
  | Refl <- sameLHSsameEnv a c, Refl <- sameLHSsameEnv b d = Refl
sameLHSsameEnv _ _ = error "sameLHSsameEnv: Different LeftHandSide's"

-- Assumes the expression does not contain Arg
generaliseArgs :: OpenAcc env lab args t -> OpenAcc env lab args' t
generaliseArgs (Aconst ty x) = Aconst ty x
generaliseArgs (Apair ty e1 e2) = Apair ty (generaliseArgs e1) (generaliseArgs e2)
generaliseArgs Anil = Anil
generaliseArgs (Acond ty e1 e2 e3) = Acond ty e1 (generaliseArgs e2) (generaliseArgs e3)
generaliseArgs (Map ty f e) = Map ty f (generaliseArgs e)
generaliseArgs (ZipWith ty f e1 e2) = ZipWith ty f (generaliseArgs e1) (generaliseArgs e2)
generaliseArgs (Fold ty f me0 a) = Fold ty f me0 (generaliseArgs a)
generaliseArgs (Aget ty path ex) = Aget ty path (generaliseArgs ex)
generaliseArgs (Alet lhs rhs ex) = Alet lhs (generaliseArgs rhs) (generaliseArgs ex)
generaliseArgs (Avar v) = Avar v
generaliseArgs (Aarg _ _) = error "generaliseArgs: Arg found"
generaliseArgs (Alabel labs) = Alabel labs

-- Assumes the expression does not contain Label
generaliseLab :: OpenExp env lab args t -> OpenExp env lab' args t
generaliseLab (Const ty x) = Const ty x
generaliseLab (PrimApp ty op ex) = PrimApp ty op (generaliseLab ex)
generaliseLab (Pair ty e1 e2) = Pair ty (generaliseLab e1) (generaliseLab e2)
generaliseLab Nil = Nil
generaliseLab (Cond ty e1 e2 e3) = Cond ty (generaliseLab e1) (generaliseLab e2) (generaliseLab e3)
generaliseLab (Get ty path ex) = Get ty path (generaliseLab ex)
generaliseLab (Let lhs rhs ex) = Let lhs (generaliseLab rhs) (generaliseLab ex)
generaliseLab (Var v) = Var v
generaliseLab (Arg ty idx) = Arg ty idx
generaliseLab (Label _) = error "generaliseLab: Label found"

-- Assumes the expression does not contain Label
generaliseLabFun :: OpenFun env lab t -> OpenFun env lab' t
generaliseLabFun (Lam lhs fun) = Lam lhs (generaliseLabFun fun)
generaliseLabFun (Body ex) = Body (generaliseLab ex)

data ReverseADResA t = forall env. ReverseADResA (A.ALeftHandSide t () env) (OpenAcc env (PD Int) () t)

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
reverseADA :: A.ALeftHandSide t () env -> OpenAcc env unused () (Array () Float) -> ReverseADResA t
reverseADA paramlhs expr
  | ExpandLHS paramlhs' paramWeaken <- expandLHS paramlhs
  , DeclareVars paramlhs'2 _ varsgen <- declareVars (A.lhsToTupR paramlhs)
  , Refl <- sameLHSsameEnv paramlhs' paramlhs'2 =
      let argsRHS = varsToArgs (varsgen A.weakenId)
          closedExpr = Alet paramlhs' argsRHS (generaliseArgs (sinkAcc paramWeaken expr))
          transformedExp = evalIdGen $ do
              exploded@(_, _, argLabelMap) <- explode LEmpty closedExpr
              trace ("exploded: " ++ showExploded exploded) undefined
              {-primaldual exploded $ \context ->
                  -- 'argsRHS' is an expression of type 't', and is a simple tuple expression
                  -- containing only Arg (and Pair/Nil) nodes. Since 't' is also exactly the
                  -- type of the gradient that we must produce here, we can transform
                  -- 'argsRHS' to our wishes.
                  -- These Arg nodes we can look up in argLabelMap to produce a DLabel, which
                  -- can on their turn be looked up in 'labelenv' using 'labValFind'. The
                  -- lookup produces an Idx, which, put in a Var, should replace the Arg in
                  -- 'argsRHS'.
                  trace ("\ncontext in core: " ++ showContext context) $
                  return $ produceGradient argLabelMap context argsRHS-}
      in
          trace ("AD result: " ++ show transformedExp) $
          ReverseADResA paramlhs' (realiseArgs transformedExp paramlhs')
  where
    varsToArgs :: A.ArrayVars env t -> OpenAcc env' lab env t
    varsToArgs TupRunit = Anil
    varsToArgs (TupRsingle (A.Var ty idx)) = Aarg ty idx
    varsToArgs (TupRpair vars1 vars2) =
      let ex1 = varsToArgs vars1
          ex2 = varsToArgs vars2
      in Apair (TupRpair (atypeOf ex1) (atypeOf ex2)) ex1 ex2

    produceGradient :: DMap (Idx args) (ADLabelT Int)
                    -> Context Int env
                    -> OpenAcc () unused args t
                    -> OpenAcc env (PD Int) args' t
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
realiseArgs :: OpenAcc () lab args t -> A.ALeftHandSide t () args -> OpenAcc args lab () t
realiseArgs = \expr lhs -> go A.weakenId (A.weakenWithLHS lhs) expr
  where
    go :: args A.:> env' -> env A.:> env' -> OpenAcc env lab args t -> OpenAcc env' lab () t
    go argWeaken varWeaken expr = case expr of
        Aconst ty x -> Aconst ty x
        Apair ty e1 e2 -> Apair ty (go argWeaken varWeaken e1) (go argWeaken varWeaken e2)
        Anil -> Anil
        Acond ty e1 e2 e3 -> Acond ty e1 (go argWeaken varWeaken e2) (go argWeaken varWeaken e3)
        Map ty f e -> Map ty f (go argWeaken varWeaken e)
        ZipWith ty f e1 e2 -> ZipWith ty f (go argWeaken varWeaken e1) (go argWeaken varWeaken e2)
        Fold ty f me0 e -> Fold ty f me0 (go argWeaken varWeaken e)
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
explode :: ALabVal Int env -> OpenAcc env unused args t -> IdGen (Exploded Int args t)
explode labelenv e =
    trace ("explode: exploding " ++ showsAcc (const "L?") 0 [] 9 e "") $
    explode' labelenv e

explode' :: ALabVal Int env -> OpenAcc env unused args t -> IdGen (Exploded Int args t)
explode' env = \case
    Aconst ty x -> do
        lab <- genId (TupRsingle ty)
        return (lab, DMap.singleton lab (Aconst ty x), mempty)
    Apair ty e1 e2 -> do
        (lab1, mp1, argmp1) <- explode' env e1
        (lab2, mp2, argmp2) <- explode' env e2
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
        let e' = generaliseLab e  -- TODO: proper handling of lambdas
        (lab1, mp1, argmp1) <- explode' env e1
        (lab2, mp2, argmp2) <- explode' env e2
        lab <- genId ty
        let pruned = Acond ty e' (Alabel lab1) (Alabel lab2)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mp2, itemmp]
            argmp = DMap.unionsWithKey (error "explode: Overlapping arg's") [argmp1, argmp2]
        return (lab, mp, argmp)
    Map ty e a -> do
        let e' = generaliseLabFun e
        (lab1, mp1, argmp1) <- explode' env a
        lab <- genId (TupRsingle ty)
        let pruned = Map ty e' (Alabel lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    ZipWith ty e a1 a2 -> do
        let e' = generaliseLabFun e
        (lab1, mp1, argmp1) <- explode' env a1
        (lab2, mp2, argmp2) <- explode' env a2
        lab <- genId (TupRsingle ty)
        let pruned = ZipWith ty e' (Alabel lab1) (Alabel lab2)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mp2, itemmp]
            argmp = DMap.unionsWithKey (error "explode: Overlapping arg's") [argmp1, argmp2]
        return (lab, mp, argmp)
    Fold ty e me0 a -> do
        let e' = generaliseLabFun e
            me0' = generaliseLab <$> me0
        (lab1, mp1, argmp1) <- explode' env a
        lab <- genId (TupRsingle ty)
        let pruned = Fold ty e' me0' (Alabel lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (lab, mp, argmp1)
    Alet lhs rhs body -> do
        (lab1, mp1, argmp1) <- explode' env rhs
        (_, labs) <- genSingleIds (atypeOf rhs)
        let (env', mpLHS) = lpushLHS_Get lhs labs env (Alabel lab1)
        (lab2, mp2, argmp2) <- explode' env' body
        let mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mpLHS, mp2]
            argmp = DMap.unionWithKey (error "explode: Overlapping arg's") argmp1 argmp2
        return (lab2, mp, argmp)
    Avar (A.Var _ idx) -> do
        return (tupleLabel (prjL idx env), mempty, mempty)
    Aarg ty idx -> do
        lab <- genId (TupRsingle ty)
        return (lab, DMap.singleton lab (Aarg ty idx), DMap.singleton idx lab)
    Aget _ _ _ -> error "explode: Unexpected Aget"
    Alabel _ -> error "explode: Unexpected Alabel"
  where
    lpushLHS_Get :: A.ALeftHandSide t env env' -> TupR (ADLabel Int) t -> ALabVal Int env -> Acc Int args t -> (ALabVal Int env', DMap (ADLabelT Int) (Acc Int args))
    lpushLHS_Get lhs labs labelenv rhs = case (lhs, labs) of
        (A.LeftHandSidePair lhs1 lhs2, TupRpair labs1 labs2) ->
            let (labelenv1, mp1) = lpushLHS_Get lhs1 labs1 labelenv (smartFst rhs)
                (labelenv2, mp2) = lpushLHS_Get lhs2 labs2 labelenv1 (smartSnd rhs)
            in (labelenv2, DMap.unionWithKey (error "lpushLHS_Get: Overlapping id's") mp1 mp2)
        (A.LeftHandSideSingle _, TupRsingle lab) -> (LPush labelenv lab, DMap.singleton (tupleLabel lab) rhs)
        (A.LeftHandSideWildcard _, _) -> (labelenv, mempty)
        _ -> error "lpushLHS_Get: impossible GADTs"

    -- TODO: make smartFst and smartSnd non-quadratic (should be easy)
    smartFst :: OpenAcc env lab args (t1, t2) -> OpenAcc env lab args t1
    smartFst (Aget (TupRpair t1 _) tidx ex) = Aget t1 (insertFst tidx) ex
      where insertFst :: TupleIdx t (t1, t2) -> TupleIdx t t1
            insertFst TIHere = TILeft TIHere
            insertFst (TILeft ti) = TILeft (insertFst ti)
            insertFst (TIRight ti) = TIRight (insertFst ti)
    smartFst ex
      | TupRpair t1 _ <- atypeOf ex
      = Aget t1 (TILeft TIHere) ex
    smartFst _ = error "smartFst: impossible GADTs"

    smartSnd :: OpenAcc env lab args (t1, t2) -> OpenAcc env lab args t2
    smartSnd (Aget (TupRpair _ t2) tidx ex) = Aget t2 (insertSnd tidx) ex
      where insertSnd :: TupleIdx t (t1, t2) -> TupleIdx t t2
            insertSnd TIHere = TIRight TIHere
            insertSnd (TILeft ti) = TILeft (insertSnd ti)
            insertSnd (TIRight ti) = TIRight (insertSnd ti)
    smartSnd ex
      | TupRpair _ t2 <- atypeOf ex
      = Aget t2 (TIRight TIHere) ex
    smartSnd _ = error "smartSnd: impossible GADTs"

data PD a = P a | D a
  deriving (Show, Eq, Ord)

-- Expression node labels are of tuple type and have a PD tag.
-- Scalar value labels have no tag.
-- Since the Let bindings are on the scalar level (because Accelerate forces
--   tuple-destructuring), the labels in the environment are scalar labels.
--   These thus also have no tag.
data Context lab env = Context (ALabVal lab env) (DMap (ADLabelT (PD lab)) (TupR (ADLabel lab)))

showContext :: (Ord lab, Show lab) => Context lab env -> String
showContext (Context labelenv bindmap) = "Context " ++ showLabelenv labelenv ++ " " ++ showBindmap bindmap

showLabelenv :: Show lab => ALabVal lab env -> String
showLabelenv LEmpty = "[]"
showLabelenv (LPush env lab) = "[" ++ go env ++ showDLabel lab ++ "]"
  where
    go :: Show lab => ALabVal lab env -> String
    go LEmpty = ""
    go (LPush env' lab') = go env' ++ showDLabel lab' ++ ", "

showBindmap :: (Ord lab, Show lab) => DMap (ADLabelT (PD lab)) (TupR (ADLabel lab)) -> String
showBindmap bindmap =
    let tups = sortOn fst [(lab, (showDLabel dlab, showTupR showDLabel labs))
                          | dlab@(DLabel _ lab) :=> labs <- DMap.assocs bindmap]
        s = intercalate ", " ["(" ++ dlabshow ++ ") :=> " ++ labsshow
                             | (_, (dlabshow, labsshow)) <- tups]
    in "[" ++ s ++ "]"

{-
primaldual :: Exploded Int args Float
           -> (forall env. Context Int env -> IdGen (OpenExp env (PD Int) args t))
           -> IdGen (Exp (PD Int) args t)
primaldual exploded cont =
    primal exploded (\ctx -> dual exploded ctx cont)
-}

-- Resulting computation will only use P, never D
primal :: Exploded Int args res
       -> (forall env. Context Int env -> IdGen (OpenAcc env (PD Int) args t))
       -> IdGen (Acc (PD Int) args t)
primal (endlab, nodemap, _) = primal' nodemap endlab (Context LEmpty mempty)

-- TODO: can't primal' just return the created bindmap entry, so that it
-- doesn't need to be looked up in the bindmap all the time?
primal' :: DMap (ADLabelT Int) (Acc Int args)
        -> ADLabelT Int t
        -> Context Int env
        -> (forall env'. Context Int env' -> IdGen (OpenAcc env' (PD Int) args res))
        -> IdGen (OpenAcc env (PD Int) args res)
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
                          Alet lhs (Acond restype (generaliseLab condexpr)
                                                  (avars thenvars) (avars elsevars))
                               <$> cont (Context (lpushLabTup labelenv' lhs labs)
                                                 (DMap.insert (fmapLabel P lbl) labs bindmap'))
                      _ ->
                          error "primal: Cond arguments did not compute arguments"

          Map restype funcexpr (Alabel arglab) ->
              primal' nodemap arglab (Context labelenv bindmap) $ \(Context labelenv' bindmap') ->
                  let TupRsingle arglabS@(DLabel argtypeS _) = bindmap' `dmapFind` fmapLabel P arglab
                  in case alabValFind labelenv' arglabS of
                      Just argidx -> do
                          lab <- genSingleId restype
                          Alet (A.LeftHandSideSingle restype)
                               (Map restype (generaliseLabFun funcexpr)
                                            (Avar (A.Var argtypeS argidx)))
                               <$> cont (Context (LPush labelenv' lab)
                                                 (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap'))
                      _ ->
                          error "primal: Map arguments did not compute arguments"

          ZipWith restype funcexpr (Alabel arglab1) (Alabel arglab2) ->
              primal' nodemap arglab1 (Context labelenv bindmap) $ \ctx1 ->
              primal' nodemap arglab2 ctx1 $ \(Context labelenv' bindmap') ->
                  let TupRsingle arglab1S = bindmap' `dmapFind` fmapLabel P arglab1
                      TupRsingle arglab2S = bindmap' `dmapFind` fmapLabel P arglab2
                  in case (alabValFind labelenv' arglab1S, alabValFind labelenv' arglab2S) of
                      (Just argidx1, Just argidx2) -> do
                          lab <- genSingleId restype
                          Alet (A.LeftHandSideSingle restype)
                               (ZipWith restype (generaliseLabFun funcexpr)
                                                (Avar (A.Var (labelType arglab1S) argidx1))
                                                (Avar (A.Var (labelType arglab2S) argidx2)))
                               <$> cont (Context (LPush labelenv' lab)
                                                 (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap'))
                      _ ->
                          error "primal: ZipWith arguments did not compute arguments"

          Fold restype funcexpr e0expr (Alabel arglab) ->
              primal' nodemap arglab (Context labelenv bindmap) $ \(Context labelenv' bindmap') ->
                  let TupRsingle arglabS@(DLabel argtype _) = bindmap' `dmapFind` fmapLabel P arglab
                  in case alabValFind labelenv' arglabS of
                      Just argidx -> do
                          lab <- genSingleId restype
                          Alet (A.LeftHandSideSingle restype)
                               (Fold restype (generaliseLabFun funcexpr) (generaliseLab <$> e0expr)
                                             (Avar (A.Var argtype argidx)))
                               <$> cont (Context (LPush labelenv' lab)
                                                 (DMap.insert (fmapLabel P lbl) (TupRsingle lab) bindmap'))
                      _ ->
                          error "primal: Fold arguments did not compute arguments"

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

{-
-- List of adjoints, collected for a particular label.
-- The exact variable references in the adjoints are dependent on the Let stack, thus the
-- environment (and the bindmap) is needed.
newtype AdjList lab args t = AdjList (forall env. Context lab env -> [OpenExp env (PD lab) args t])

data AnyLabel s lab = forall t. AnyLabel (DLabel s lab t)
type AnyLabelT = AnyLabel TypeR

-- The Ord and Eq instances refer only to 'a'.
data OrdBox a b = OrdBox { _ordboxTag :: a, ordboxAuxiliary :: b }
instance Eq  a => Eq  (OrdBox a b) where OrdBox x _    ==     OrdBox y _ = x == y
instance Ord a => Ord (OrdBox a b) where OrdBox x _ `compare` OrdBox y _ = compare x y

dual :: Exploded Int args Float
     -> Context Int env
     -> (forall env'. Context Int env' -> IdGen (OpenExp env' (PD Int) args t))
     -> IdGen (OpenExp env (PD Int) args t)
dual (endlab, nodemap, _) context cont =
    trace ("\nlabelorder: " ++ show [labelLabel l | AnyLabel l <- labelorder]) $
    -- TODO: Is the type annotation on scalarType necessary?
    -- TODO: Can I use those shortcut methods to easily produce more type witnesses elsewhere?
    let contribmap = DMap.singleton (fmapLabel D endlab)
                                    (AdjList (const [Const (scalarType :: ScalarType Float) 1.0]))
    in dual' nodemap labelorder context contribmap cont
  where
    -- Every numeric label is unique; we don't need the type information for that.
    -- We play fast and loose with that here: we use an 'OrdBox' for 'floodfill'
    -- to use the 'Ord' instance on 'Int' while carrying along the full 'DLabel'
    -- objects, and we index the 'parentmap' on the integer value too.
    parentsOf :: AnyLabelT Int -> [AnyLabelT Int]
    parentsOf (AnyLabel lbl) = expLabelParents (nodemap `dmapFind` lbl)

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

dual' :: DMap (EDLabelT Int) (Exp Int args)
      -> [AnyLabelT Int]
      -> Context Int env
      -> DMap (EDLabelT (PD Int)) (AdjList Int args)
      -> (forall env'. Context Int env' -> IdGen (OpenExp env' (PD Int) args res))
      -> IdGen (OpenExp env (PD Int) args res)
dual' _ [] context _ cont = cont context
dual' nodemap (AnyLabel lbl : restlabels) (Context labelenv bindmap) contribmap cont =
    -- trace ("dual': computing " ++ show lbl) $
    case nodemap `dmapFind` lbl of
      -- We aren't interested in the adjoint of constant nodes -- seeing as
      -- they don't have any parents to contribute to.
      Const _ _ ->
          dual' nodemap restlabels (Context labelenv bindmap) contribmap cont

      -- Argument nodes don't have any nodes to contribute to either, but we do
      -- need to calculate and store their adjoint.
      Arg restypeS _ -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
          lblS <- genScalarId restypeS
          Let (A.LeftHandSideSingle restypeS) adjoint
              <$> dual' nodemap restlabels (Context (LPush labelenv lblS)
                                                    (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                        contribmap cont

      PrimApp _ (A.PrimAdd restypeN) (Label arglab) -> do
          let restypeS = SingleScalarType (NumSingleType restypeN)
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil $ \(TupRsingle adjvar) _ ->
                                    smartPair (Var adjvar) (Var adjvar)]
                                contribmap
          lblS <- genScalarId restypeS
          Let (A.LeftHandSideSingle restypeS) adjoint
              <$> dual' nodemap restlabels (Context (LPush labelenv lblS)
                                                    (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                        contribmap' cont

      PrimApp restype (A.PrimMul restypeN) (Label arglab) -> do
          let restypeS = SingleScalarType (NumSingleType restypeN)
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) $ \(TupRsingle adjvar) (TupRpair (TupRsingle argvar1) (TupRsingle argvar2) :@ TLNil) ->
                                    smartPair
                                         (PrimApp restype (A.PrimMul restypeN) (smartPair (Var adjvar) (Var argvar2)))
                                         (PrimApp restype (A.PrimMul restypeN) (smartPair (Var adjvar) (Var argvar1)))]
                                contribmap
          lblS <- genScalarId restypeS
          Let (A.LeftHandSideSingle restypeS) adjoint
              <$> dual' nodemap restlabels (Context (LPush labelenv lblS)
                                                    (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                        contribmap' cont

      PrimApp restype (A.PrimLog restypeF) (Label arglab) -> do
          let restypeS = SingleScalarType (NumSingleType (FloatingNumType restypeF))
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) $ \(TupRsingle adjvar) (TupRsingle argvar :@ TLNil) ->
                                    -- dE/dx = dE/d(log x) * d(log x)/dx = adjoint * 1/x = adjoint / x
                                    PrimApp restype (A.PrimFDiv restypeF)
                                        (smartPair (Var adjvar) (Var argvar))]
                                contribmap
          lblS <- genScalarId restypeS
          Let (A.LeftHandSideSingle restypeS) adjoint
              <$> dual' nodemap restlabels (Context (LPush labelenv lblS)
                                                    (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                        contribmap' cont

      -- Argument is an integral type, which takes no contributions
      PrimApp _ (A.PrimToFloating _ restypeF) _ -> do
          let restypeS = SingleScalarType (NumSingleType (FloatingNumType restypeF))
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
          lblS <- genScalarId restypeS
          Let (A.LeftHandSideSingle restypeS) adjoint
              <$> dual' nodemap restlabels (Context (LPush labelenv lblS)
                                                    (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                        contribmap cont

      -- Result is an integral type, which produces no contributions (because
      -- its adjoint is always zero). Therefore, we also have no contributions
      -- to our parents.
      -- Also, since contributions of integer-valued nodes are not used
      -- anywhere, we don't even have to generate this zero adjoint. TODO: is this true?
      PrimApp (TupRsingle (SingleScalarType (NumSingleType (IntegralNumType _)))) _ _ ->
          dual' nodemap restlabels (Context labelenv bindmap) contribmap cont

      Cond restype (Label condlab) (Label thenlab) (Label elselab) -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution thenlab (condlab :@ TLNil) $ \adjvars (TupRsingle condvar :@ TLNil) ->
                                    Cond restype (Var condvar) (evars adjvars) (zeroForType restype)
                                ,Contribution elselab (condlab :@ TLNil) $ \adjvars (TupRsingle condvar :@ TLNil) ->
                                    Cond restype (Var condvar) (zeroForType restype) (evars adjvars)]
                                contribmap
          (GenLHS lhs, labs) <- genScalarIds restype
          Let lhs adjoint
              <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                    (DMap.insert (fmapLabel D lbl) labs bindmap))
                        contribmap' cont

      Get restype path (Label arglab) -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil $ \adjvars _ ->
                                    oneHotTup (labelType arglab) path (evars adjvars)]
                                contribmap
          (GenLHS lhs, labs) <- genScalarIds restype
          Let lhs adjoint
              <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                    (DMap.insert (fmapLabel D lbl) labs bindmap))
                        contribmap' cont

      Pair restype (Label arglab1) (Label arglab2) -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab1 TLNil $ \(TupRpair adjvars1 _) _ ->
                                    evars adjvars1
                                ,Contribution arglab2 TLNil $ \(TupRpair _ adjvars2) _ ->
                                    evars adjvars2]
                                contribmap
          (GenLHS lhs, labs) <- genScalarIds restype
          Let lhs adjoint
              <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                    (DMap.insert (fmapLabel D lbl) labs bindmap))
                        contribmap' cont

      Nil ->
          -- Nothing to compute here, but we still need to register this expression label
          -- in the bindmap.
          dual' nodemap restlabels (Context labelenv
                                            (DMap.insert (fmapLabel D lbl) TupRunit bindmap))
                contribmap cont

      Label arglab -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil $ \adjvars _ ->
                                    evars adjvars]
                                contribmap
          (GenLHS lhs, labs) <- genScalarIds (labelType arglab)
          Let lhs adjoint
              <$> dual' nodemap restlabels (Context (lpushLabTup labelenv lhs labs)
                                                    (DMap.insert (fmapLabel D lbl) labs bindmap))
                        contribmap' cont

      expr -> trace ("\n!! " ++ show expr) undefined
  where
    smartPair :: OpenExp env lab args a -> OpenExp env lab args b -> OpenExp env lab args (a, b)
    smartPair a b = Pair (TupRpair (etypeOf a) (etypeOf b)) a b

-- TODO: make a new abstraction after the refactor, possibly inspired by this function, which was the abstraction pre-refactor
-- dualStoreAdjoint
--     :: DMap (DLabel Int) (Exp Int args)
--     -> [AnyLabel Int]
--     -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) args res)
--     -> DLabel Int t
--     -> LabVal (PD Int) env
--     -> DMap (DLabel (PD Int)) (AdjList (PD Int) args)
--     -> [Contribution t args]
--     -> OpenExp env (PD Int) args res
-- dualStoreAdjoint nodemap restlabels cont lbl labelenv contribmap contribs =
--     let adjoint = collectAdjoint contribmap lbl (TupRsingle (labelType lbl)) labelenv
--         contribmap' = updateContribmap lbl contribs contribmap
--     in Let (A.LeftHandSideSingle (labelType lbl)) adjoint
--            (dual' nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)
-}

-- Utility functions
-- -----------------

{-
infixr :@
data TypedList f tys where
    TLNil :: TypedList f '[]
    (:@) :: f t -> TypedList f tys -> TypedList f (t ': tys)

tlmap :: (forall t. f t -> g t) -> TypedList f tys -> TypedList g tys
tlmap _ TLNil = TLNil
tlmap f (x :@ xs) = f x :@ tlmap f xs

data Contribution node args =
    forall parents t.
        Contribution (EDLabelT Int t)  -- to which label are we contributing an adjoint
                     (TypedList (EDLabelT Int) parents)  -- labels you need the primary value of
                     (forall env. A.ExpVars env node                  -- current node's adjoint
                               -> TypedList (A.ExpVars env) parents   -- requested primal values
                               -> OpenExp env (PD Int) args t)        -- contribution

-- Note: Before this code was extracted into a separate function, its
-- functionality was inlined in the branches of dual'. Because of that, the
-- branches needed explicit type signatures (and thus be separate functions),
-- since the definition of the contribution function had too intricate type
-- variables for GHC to figure out.
-- Now that this is a separate function, though, the type signature here (and
-- the typing of Contribution) removes the need of the branches of dual' to
-- have a separate type signature, significantly simplifying the structure of
-- the code.
updateContribmap :: EDLabelT Int node
                 -> [Contribution node args]
                 -> DMap (EDLabelT (PD Int)) (AdjList Int args)
                 -> DMap (EDLabelT (PD Int)) (AdjList Int args)
updateContribmap lbl =
    flip . foldr $ \(Contribution lab parentlabs gen) ->
        addContribution (fmapLabel D lab) $ \(Context labelenv bindmap) ->
            let currentlabs = bindmap `dmapFind` fmapLabel D lbl
            in case (elabValFinds labelenv currentlabs, findAll (Context labelenv bindmap) parentlabs) of
                (Just adjvars, parvars) -> gen adjvars parvars
                _ -> error $ "updateContribmap: node D " ++ show lbl ++ " was not computed"
  where
    findAll :: Context Int env -> TypedList (EDLabelT Int) parents -> TypedList (A.ExpVars env) parents
    findAll (Context labelenv bindmap) =
        tlmap $ \lab ->
            let labs = bindmap `dmapFind` fmapLabel P lab
            in fromMaybe (err lab) (elabValFinds labelenv labs)
      where err lab = error $ "updateContribmap: arg P " ++ show lab ++ " was not computed"

addContribution :: Ord lab
                => EDLabelT (PD lab) t
                -> (forall env. Context lab env -> OpenExp env (PD lab) args t)
                -> DMap (EDLabelT (PD lab)) (AdjList lab args)
                -> DMap (EDLabelT (PD lab)) (AdjList lab args)
-- TODO: function body not yet updated, only type
addContribution lbl contribution =
    DMap.insertWith (\(AdjList f1) (AdjList f2) -> AdjList (\context -> f1 context ++ f2 context))
                    lbl
                    (AdjList (pure . contribution))

collectAdjoint :: DMap (EDLabelT (PD Int)) (AdjList Int args)
               -> EDLabelT Int item
               -> Context Int env
               -> OpenExp env (PD Int) args item
collectAdjoint contribmap lbl (Context labelenv bindmap) =
    case DMap.lookup (fmapLabel D lbl) contribmap of
        Just (AdjList listgen) -> expSum (labelType lbl) (listgen (Context labelenv bindmap))
        Nothing -> expSum (labelType lbl) []  -- if there are no contributions, well, the adjoint is an empty sum (i.e. zero)

class IsAdditive s where
    zeroForType' :: (forall a. Num a => a) -> s t -> OpenExp env lab args t
    expPlus :: s t -> OpenExp env lab args t -> OpenExp env lab args t -> OpenExp env lab args t

    zeroForType :: s t -> OpenExp env lab args t
    zeroForType = zeroForType' 0

    expSum :: s t -> [OpenExp env lab args t] -> OpenExp env lab args t
    expSum ty [] = zeroForType ty
    expSum ty es = foldl1 (expPlus ty) es

-- class IsMaybeAdditive s where
--     maybeZeroForType' :: (forall a. Num a => a) -> s t -> Maybe (OpenExp env lab args t)
--     maybeExpPlus :: s t -> OpenExp env lab args t -> OpenExp env lab args t -> Maybe (OpenExp env lab args t)

--     maybeZeroForType :: s t -> Maybe (OpenExp env lab args t)
--     maybeZeroForType = maybeZeroForType' 0

--     maybeExpSum :: s t -> [OpenExp env lab args t] -> Maybe (OpenExp env lab args t)
--     maybeExpSum ty [] = maybeZeroForType ty
--     maybeExpSum ty (expr:exprs) = go exprs expr
--       where go [] accum = Just accum
--             go (e:es) accum = maybeExpPlus ty accum e >>= go es

instance IsAdditive IntegralType where
    zeroForType' z ty = case ty of
        TypeInt -> Const (scalar TypeInt) z
        TypeInt8 -> Const (scalar TypeInt8) z
        TypeInt16 -> Const (scalar TypeInt16) z
        TypeInt32 -> Const (scalar TypeInt32) z
        TypeInt64 -> Const (scalar TypeInt64) z
        TypeWord -> Const (scalar TypeWord) z
        TypeWord8 -> Const (scalar TypeWord8) z
        TypeWord16 -> Const (scalar TypeWord16) z
        TypeWord32 -> Const (scalar TypeWord32) z
        TypeWord64 -> Const (scalar TypeWord64) z
      where scalar = SingleScalarType . NumSingleType . IntegralNumType

    expPlus ty e1 e2 =
      PrimApp (TupRsingle (scalar ty)) (A.PrimAdd (IntegralNumType ty))
              (Pair (TupRpair (TupRsingle (scalar ty)) (TupRsingle (scalar ty))) e1 e2)
      where scalar = SingleScalarType . NumSingleType . IntegralNumType

instance IsAdditive FloatingType where
    zeroForType' z ty = case ty of
        TypeHalf -> Const (flttype TypeHalf) z
        TypeFloat -> Const (flttype TypeFloat) z
        TypeDouble -> Const (flttype TypeDouble) z
      where flttype = SingleScalarType . NumSingleType . FloatingNumType

    expPlus ty e1 e2 =
      PrimApp (TupRsingle (scalar ty)) (A.PrimAdd (FloatingNumType ty))
              (Pair (TupRpair (TupRsingle (scalar ty)) (TupRsingle (scalar ty))) e1 e2)
      where scalar = SingleScalarType . NumSingleType . FloatingNumType

instance IsAdditive NumType where
    zeroForType' z (IntegralNumType t) = zeroForType' z t
    zeroForType' z (FloatingNumType t) = zeroForType' z t

    expPlus ty e1 e2 =
      PrimApp (TupRsingle (scalar ty)) (A.PrimAdd ty)
              (Pair (TupRpair (TupRsingle (scalar ty)) (TupRsingle (scalar ty))) e1 e2)
      where scalar = SingleScalarType . NumSingleType

instance IsAdditive SingleType where
    zeroForType' z (NumSingleType t) = zeroForType' z t

    expPlus (NumSingleType ty) e1 e2 = expPlus ty e1 e2

instance IsAdditive ScalarType where
    zeroForType' z (SingleScalarType t) = zeroForType' z t
    zeroForType' _ (VectorScalarType _) = internalError "AD: Can't handle vectors yet"

    expPlus (SingleScalarType ty) e1 e2 = expPlus ty e1 e2
    expPlus (VectorScalarType _) _ _ = internalError "AD: Can't handle vectors yet"

instance IsAdditive TypeR where
    zeroForType' _ TupRunit = Nil
    zeroForType' z (TupRsingle t) = zeroForType' z t
    zeroForType' z (TupRpair t1 t2) =
        Pair (TupRpair t1 t2) (zeroForType' z t1) (zeroForType' z t2)

    expPlus ty e1 e2 = tupleZip' ty expPlus e1 e2

oneHotTup :: TypeR t -> TupleIdx t t' -> OpenExp env lab args t' -> OpenExp env lab args t
oneHotTup _ TIHere ex = ex
oneHotTup ty@(TupRpair ty1 ty2) (TILeft ti) ex = Pair ty (oneHotTup ty1 ti ex) (zeroForType ty2)
oneHotTup ty@(TupRpair ty1 ty2) (TIRight ti) ex = Pair ty (zeroForType ty1) (oneHotTup ty2 ti ex)
oneHotTup _ _ _ = error "oneHotTup: impossible GADTs"

-- Errors if any parents are not Label nodes, or if called on a Let or Var node.
expLabelParents :: OpenExp env lab args t -> [AnyLabelT lab]
expLabelParents = \case
    Const _ _ -> []
    PrimApp _ _ e -> fromLabel e
    Pair _ e1 e2 -> fromLabel e1 ++ fromLabel e2
    Nil -> []
    Cond _ e1 e2 e3 -> fromLabel e1 ++ fromLabel e2 ++ fromLabel e3
    Get _ _ e -> fromLabel e
    Arg _ _ -> []
    Label lab -> [AnyLabel lab]
    Let _ _ _ -> unimplemented "Let"
    Var _ -> unimplemented "Var"
  where
    unimplemented name =
        error ("expLabelParents: Unimplemented for " ++ name ++ ", semantics unclear")

    fromLabel (Label lab) = [AnyLabel lab]
    fromLabel _ = error "expLabelParents: Parent is not a label set"
-}

dmapFind :: (HasCallStack, GCompare f) => DMap f g -> f a -> g a
dmapFind mp elt = case DMap.lookup elt mp of
                    Just res -> res
                    Nothing -> error "dmapFind: not found"
