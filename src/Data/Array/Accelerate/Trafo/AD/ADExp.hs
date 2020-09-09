{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Data.Array.Accelerate.Trafo.AD.ADExp (
  reverseAD, ReverseADResE(..),
  splitLambdaAD, labeliseFun
) where

import qualified Control.Monad.Writer as W
import Control.Monad.Writer (Writer)
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
import Data.Array.Accelerate.Error (HasCallStack, internalError)
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (shapeType)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.AD.Additive
import Data.Array.Accelerate.Trafo.AD.Algorithms
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.Sink
import Data.Array.Accelerate.Trafo.Var (declareVars, DeclareVars(..))


type EContext = Context ScalarType PDAuxTagExp


genId :: TypeR t -> IdGen (EDLabelT Int t)
genId = genId'

genSingleId :: ScalarType t -> IdGen (EDLabel Int t)
genSingleId = genId'

genSingleIds :: TypeR t -> IdGen (GenLHS ScalarType env t, TupR (EDLabel Int) t)
genSingleIds TupRunit = return (GenLHS (A.LeftHandSideWildcard TupRunit), TupRunit)
genSingleIds (TupRsingle ty) = (GenLHS (A.LeftHandSideSingle ty),) . TupRsingle <$> genSingleId ty
genSingleIds (TupRpair t1 t2) = do
    (GenLHS lhs1, ids1) <- genSingleIds t1
    (GenLHS lhs2, ids2) <- genSingleIds t2
    return (GenLHS (A.LeftHandSidePair lhs1 lhs2), TupRpair ids1 ids2)


-- TODO: make this a data definition, not a tuple
type Exploded aenv lab alab args res = (EDLabelT lab res, DMap (EDLabelT lab) (Exp aenv lab alab args), DMap (A.Idx args) (EDLabelT lab))

showExploded :: (Ord lab, Show lab, Show alab) => Exploded aenv lab alab args t -> String
showExploded (endlab, nodemap, argmap) =
    "(" ++ showDLabel endlab ++ ", " ++ showNodemap nodemap ++ ", " ++ showArgmap argmap ++ ")"

showNodemap :: (Ord lab, Show lab, Show alab) => DMap (EDLabelT lab) (Exp aenv lab alab args) -> String
showNodemap nodemap =
    let tups = sortOn fst [(lab, (showDLabel dlab, show expr))
                          | dlab@(DLabel _ lab) :=> expr <- DMap.assocs nodemap]
        s = intercalate ", " ["(" ++ dlabshow ++ ") :=> " ++ exprshow
                             | (_, (dlabshow, exprshow)) <- tups]
    in "[" ++ s ++ "]"

showArgmap :: Show lab => DMap (A.Idx args) (EDLabelT lab) -> String
showArgmap argmap =
    let s = intercalate ", " ['A' : show (A.idxToInt argidx) ++ " :=> " ++ showDLabel dlab
                             | argidx :=> dlab <- DMap.assocs argmap]
    in "[" ++ s ++ "]"

showList' :: (a -> String) -> [a] -> String
showList' f l = "[" ++ intercalate ", " (map f l) ++ "]"

-- Assumes the expression does not contain Arg
generaliseArgs :: OpenExp env aenv lab alab args t -> OpenExp env aenv lab alab args' t
generaliseArgs (Const ty x) = Const ty x
generaliseArgs (PrimApp ty op ex) = PrimApp ty op (generaliseArgs ex)
generaliseArgs (Pair ty e1 e2) = Pair ty (generaliseArgs e1) (generaliseArgs e2)
generaliseArgs Nil = Nil
generaliseArgs (Cond ty e1 e2 e3) = Cond ty (generaliseArgs e1) (generaliseArgs e2) (generaliseArgs e3)
generaliseArgs (Shape avar) = Shape avar
generaliseArgs (Get ty path ex) = Get ty path (generaliseArgs ex)
generaliseArgs (Let lhs rhs ex) = Let lhs (generaliseArgs rhs) (generaliseArgs ex)
generaliseArgs (Var v) = Var v
generaliseArgs (Arg _ _) = error "generaliseArgs: Arg found"
generaliseArgs (Label labs) = Label labs

data ReverseADResE aenv alab t = forall env. ReverseADResE (A.ELeftHandSide t () env) (OpenExp env aenv (PDExp Int) alab () t)

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
-- TODO: remove Show constraint from alab
reverseAD :: Show alab => A.ELeftHandSide t () env -> OpenExp env aenv unused alab () Float -> ReverseADResE aenv alab t
reverseAD paramlhs expr
  | ExpandLHS paramlhs' paramWeaken <- expandLHS paramlhs
  , DeclareVars paramlhs'2 _ varsgen <- declareVars (A.lhsToTupR paramlhs)
  , Refl <- sameLHSsameEnv paramlhs' paramlhs'2 =
      let argsRHS = varsToArgs (varsgen A.weakenId)
          closedExpr = Let paramlhs' argsRHS (generaliseArgs (sinkExp paramWeaken expr))
          transformedExp = evalIdGen $ do
              exploded@(_, _, argLabelMap) <- explode LEmpty closedExpr
              traceM ("exploded: " ++ showExploded exploded)
              primaldual exploded $ \context ->
                  -- 'argsRHS' is an expression of type 't', and is a simple tuple expression
                  -- containing only Arg (and Pair/Nil) nodes. Since 't' is also exactly the
                  -- type of the gradient that we must produce here, we can transform
                  -- 'argsRHS' to our wishes.
                  -- These Arg nodes we can look up in argLabelMap to produce a DLabel, which
                  -- can on their turn be looked up in 'labelenv' using 'labValFind'. The
                  -- lookup produces an Idx, which, put in a Var, should replace the Arg in
                  -- 'argsRHS'.
                  trace ("\ncontext in core: " ++ showContext context) $
                  return $ produceGradient argLabelMap context argsRHS
      in
          trace ("AD result: " ++ show transformedExp) $
          ReverseADResE paramlhs' (realiseArgs transformedExp paramlhs')

varsToArgs :: A.ExpVars env t -> OpenExp env' aenv lab alab env t
varsToArgs TupRunit = Nil
varsToArgs (TupRsingle (A.Var ty idx)) = Arg ty idx
varsToArgs (TupRpair vars1 vars2) =
  let ex1 = varsToArgs vars1
      ex2 = varsToArgs vars2
  in Pair (TupRpair (etypeOf ex1) (etypeOf ex2)) ex1 ex2

produceGradient :: DMap (Idx args) (EDLabelT Int)
                -> EContext Int env
                -> OpenExp () aenv unused unused2 args t
                -> OpenExp env aenv (PDExp Int) alab args' t
produceGradient argLabelMap context@(Context labelenv bindmap) argstup = case argstup of
    Nil -> Nil
    Pair ty e1 e2 -> Pair ty (produceGradient argLabelMap context e1)
                             (produceGradient argLabelMap context e2)
    Arg ty idx
      | Just lab <- DMap.lookup idx argLabelMap
      , Just labs <- DMap.lookup (fmapLabel D lab) bindmap
      , Just vars <- elabValFinds labelenv labs
          -> evars vars
      | otherwise
          -> error $ "produceGradient: Adjoint of Arg (" ++ show ty ++ ") " ++
                        'A' : show (A.idxToInt idx) ++ " not computed"
    _ -> error "produceGradient: what?"

splitLambdaAD :: forall f aenv t t' sh unused unused2.
                 Functor f
              => LabVal ArrayR Int aenv
              -> (forall ty. TypeR ty -> f (DLabel ArrayR Int (Array sh ty)))
              -> Fun aenv unused unused2 (t -> t')
              -> f (SplitLambdaAD t t' (PDExp Int) Int sh)
splitLambdaAD alabelenv tmplabGen (Lam paramlhs (Body expr))
  | TupRsingle (SingleScalarType (NumSingleType (FloatingNumType TypeFloat))) <- etypeOf expr  -- Float result type assertion
  , TupRsingle exprtypeS <- etypeOf expr
  , ExpandLHS paramlhs' paramWeaken <- expandLHS paramlhs
  , DeclareVars paramlhs'2 _ varsgen <- declareVars (A.lhsToTupR paramlhs)
  , Refl <- sameLHSsameEnv paramlhs' paramlhs'2
  , let argsRHS = varsToArgs (varsgen A.weakenId)
        closedExpr = Let paramlhs' argsRHS (generaliseArgs (sinkExp paramWeaken (generaliseLab expr)))
  , (labelisedExpr, fvlablist) <- W.runWriter (collectFreeAvars alabelenv closedExpr)
  , TuplifyAvars _ fvlabs fvlhs <- tuplifyAvars fvlablist
  = let transformedExp = evalIdGen $ do
            exploded@(reslab, _, argLabelMap) <- explode LEmpty labelisedExpr
            traceM ("exp exploded: " ++ showExploded exploded)
            PrimalResult context@(Context labelenv bindmap) builder <- primal exploded
            traceM ("\nexp context in core: " ++ showContext context)
            let reslabs = bindmap DMap.! fmapLabel P reslab
            case (elabValFinds labelenv reslabs, constructPrimalBundle context) of
                (Just resultvars, PrimalBundle tmpvars (PrimalInstantiator instantiator))
                  | LetBoundExpE tmpRestoreLHS tmpRestoreVars <- elhsCopy (A.varsType tmpvars) -> do
                      let e' = builder (evars (TupRpair resultvars tmpvars))
                      adjlab <- genSingleId scalarType
                      (_, tmpRestoreLabs) <- genSingleIds (A.varsType tmpRestoreVars)
                      dualBody <- instantiator
                                      (Context (lpushLabTup (LPush LEmpty adjlab) tmpRestoreLHS tmpRestoreLabs) mempty)
                                      (evars tmpRestoreVars)
                                      (\ctx -> do traceM $ "invoking exp dual with context: " ++ showContext ctx
                                                  let adjointProducer :: EContext Int env -> OpenExp env aenv (PDExp Int) alab args t'
                                                      adjointProducer (Context labelenv' _) =
                                                        case elabValFind labelenv' adjlab of
                                                            Just idx -> Var (A.Var exprtypeS idx)
                                                  DualResult ctx' _ builder' <- dual exploded adjointProducer ctx
                                                  return $ builder' $ produceGradient argLabelMap ctx' argsRHS)
                      -- The primal and dual lambda expression here are inlined because of the monomorphism restriction
                      return $ SplitLambdaAD (\fvavars ->
                                                  Lam paramlhs'
                                                    (Body (realiseArgs
                                                              (inlineAvarLabels fvlabs fvavars e')
                                                              paramlhs')))
                                             (\fvavars ->
                                                  Lam (A.LeftHandSidePair (A.LeftHandSideSingle scalarType) tmpRestoreLHS)
                                                      (Body (generaliseArgs  {- TODO: is this generalisation correct? -}
                                                                (inlineAvarLabels fvlabs fvavars dualBody))))
                                             fvlabs
                                             <$> fmap (A.varsType tmpvars,) (tmplabGen (A.varsType tmpvars))
                _ ->
                    error "Final primal value not computed"
    in -- trace ("AD result: " ++ show transformedExp) $
       -- ReverseADResE paramlhs' (realiseArgs transformedExp paramlhs')
       transformedExp
  | otherwise =
      internalError "Non-Float-producing lambdas under gradientA currently unsupported"
splitLambdaAD _ _ _ =
    internalError "splitLambdaAD passed function with more than 1 argument"

-- Asserts that there are no array labels yet in the expression, and reset the array environment
labeliseExp :: LabVal ArrayR alab aenv
            -> OpenExp env aenv lab alab' args t
            -> OpenExp env aenv' lab alab args t
labeliseExp labelenv ex = case ex of
    Const ty x -> Const ty x
    PrimApp ty op e -> PrimApp ty op (labeliseExp labelenv e)
    Pair ty e1 e2 -> Pair ty (labeliseExp labelenv e1) (labeliseExp labelenv e2)
    Nil -> Nil
    Cond ty e1 e2 e3 -> Cond ty (labeliseExp labelenv e1) (labeliseExp labelenv e2) (labeliseExp labelenv e3)
    Shape (Left (A.Var _ idx)) ->
        let lab = prjL idx labelenv
        in Shape (Right lab)
    Shape (Right _) -> error "Unexpected Shape(Label) in collectFreeAvars"
    Get ty ti e -> Get ty ti (labeliseExp labelenv e)
    Let lhs rhs e -> Let lhs (labeliseExp labelenv rhs) (labeliseExp labelenv e)
    Arg ty idx -> Arg ty idx
    Var var -> Var var
    Label lab -> Label lab

-- Asserts that there are no array labels yet in the expression, and reset the array environment
labeliseFun :: LabVal ArrayR alab aenv
            -> OpenFun env aenv lab alab' t
            -> OpenFun env aenv' lab alab t
labeliseFun labelenv (Lam lhs fun) = Lam lhs (labeliseFun labelenv fun)
labeliseFun labelenv (Body ex) = Body (labeliseExp labelenv ex)

collectFreeAvars :: LabVal ArrayR alab aenv
                 -> OpenExp env aenv lab unused args t
                 -> Writer [AnyLabel ArrayR alab] (OpenExp env aenv lab alab args t)
collectFreeAvars labelenv ex = case ex of
    Const ty x -> return (Const ty x)
    PrimApp ty op e -> PrimApp ty op <$> collectFreeAvars labelenv e
    Pair ty e1 e2 -> Pair ty <$> collectFreeAvars labelenv e1 <*> collectFreeAvars labelenv e2
    Nil -> return Nil
    Cond ty e1 e2 e3 -> Cond ty <$> collectFreeAvars labelenv e1 <*> collectFreeAvars labelenv e2 <*> collectFreeAvars labelenv e3
    Shape (Left (A.Var _ idx)) -> do
        let lab = prjL idx labelenv
        W.tell [AnyLabel lab]
        return (Shape (Right lab))
    Shape (Right _) -> error "Unexpected Shape(Label) in collectFreeAvars"
    Get ty ti e -> Get ty ti <$> collectFreeAvars labelenv e
    Let lhs rhs e -> Let lhs <$> collectFreeAvars labelenv rhs <*> collectFreeAvars labelenv e
    Arg ty idx -> return (Arg ty idx)
    Var var -> return (Var var)
    Label lab -> return (Label lab)

data TuplifyAvars lab aenv =
    forall aenv' t.
        TuplifyAvars -- Collects vars from array environment outside the lambda
                     (forall aenv''. aenv' A.:> aenv'' -> A.ArrayVars aenv'' t)
                     -- The tuple of labels bound
                     (TupR (DLabel ArrayR lab) t)
                     -- Bind the collected vars in the lambda argument
                     (A.LeftHandSide ArrayR t aenv aenv')
                     -- -- Lookup vars in passed tuple inside the lambda
                     -- (forall aenv''. aenv' A.:> aenv'' -> DMap (DLabel ArrayR lab) (A.ArrayVar aenv''))

tuplifyAvars :: Ord lab => [AnyLabel ArrayR lab] -> TuplifyAvars lab aenv
tuplifyAvars [] = TuplifyAvars (const TupRunit) TupRunit A.LeftHandSideUnit -- (const mempty)
tuplifyAvars (AnyLabel lab@(DLabel ty@(ArrayR _ _) _) : rest)
  | TuplifyAvars tupexprf labs lhs {-mpf-} <- tuplifyAvars rest
  = TuplifyAvars (\w -> TupRpair (tupexprf (A.weakenSucc w))
                                 (TupRsingle (A.Var ty (w A.>:> ZeroIdx))))
                 (TupRpair labs (TupRsingle lab))
                 (A.LeftHandSidePair lhs (A.LeftHandSideSingle ty))
                 -- (\w -> DMap.insert lab (A.Var ty (w A.>:> ZeroIdx))
                 --                    (mpf (A.weakenSucc w)))

data PrimalBundle env aenv lab alab =
    forall tmp.
        PrimalBundle -- Collects temporaries into a tuple
                     (A.ExpVars env tmp)
                     -- Consumes the tuple and reproduces the labels in a new let-environment
                     (PrimalInstantiator aenv lab alab tmp)

data PrimalInstantiator aenv lab alab tmp =
    PrimalInstantiator (forall env1 t args.
                        EContext lab env1
                     -> OpenExp env1 aenv (PDExp lab) alab args tmp
                     -> (forall env2. EContext lab env2 -> IdGen (OpenExp env2 aenv (PDExp lab) alab args t))
                     -> IdGen (OpenExp env1 aenv (PDExp lab) alab args t))

data PrimalBundle' env aenv lab alab =
    forall tmp.
        PrimalBundle' (A.ExpVars env tmp)
                      (TypeR tmp)
                      (forall env' args. OpenExp env' aenv (PDExp lab) alab args tmp
                                      -> IdGen ([DSum (EDLabel lab) (OpenExp env' aenv (PDExp lab) alab args)]  -- new scalar labels and their corresponding fragments of the temps tuple
                                               ,DMap (EDLabel lab) (EDLabel lab)))  -- old to new scalar label translation map

-- Does not use the contents of the given context; just adds to the bottom of it.
constructPrimalBundle :: EContext Int env -> PrimalBundle env aenv Int alab
constructPrimalBundle (Context toplabelenv topbindmap)
  | PrimalBundle' vars _ instantiator <- constructPrimalBundle' (enumerateLabelenv toplabelenv)
  = PrimalBundle vars $ PrimalInstantiator $ \(Context locallabelenv localbindmap) tupe cont -> do
      (fragments, oldnewmap) <- instantiator tupe
      let bindmap' = DMap.map (fmapTupR (oldnewmap DMap.!)) topbindmap
          localbindmap' = DMap.unionWithKey (error "constructPrimalBundle: Context at usage of primal bundle contains keys already defined in primal computation")
                                            localbindmap bindmap'
      traceM $ "constructPrimalBundle: oldnewmap: " ++ showList' (\(k :=> v) -> "(" ++ showDLabel k ++ ", " ++ showDLabel v ++ ")") (DMap.assocs oldnewmap) ++ "]"
      traceM $ "constructPrimalBundle: bindmap': " ++ showBindmap bindmap'
      traceM $ "constructPrimalBundle: fragments: " ++ showList' (\(k :=> _) -> "(" ++ showDLabel k ++ ", ...)") fragments
      bindAll (Context locallabelenv localbindmap') A.weakenId fragments cont
  where
    constructPrimalBundle' :: [DSum (EDLabel Int) (Idx env)] -> PrimalBundle' env aenv Int alab
    constructPrimalBundle' [] = PrimalBundle' TupRunit TupRunit (\_ -> return (mempty, mempty))
    constructPrimalBundle' ((lab@(DLabel ty _) :=> idx) : rest)
      | PrimalBundle' vars restty instantiator <- constructPrimalBundle' rest
      = PrimalBundle' (TupRpair vars (TupRsingle (A.Var ty idx)))
                      (TupRpair restty (TupRsingle ty))
                      (\tmpe -> do
                          (locmp, transmp) <- instantiator (Get restty (TILeft TIHere) tmpe)
                          lab' <- genSingleId ty
                          return ((lab' :=> Get (TupRsingle ty) (TIRight TIHere) tmpe) : locmp
                                 ,DMap.insert lab lab' transmp))

    bindAll :: EContext Int env'
            -> env A.:> env'
            -> [DSum (EDLabel Int) (OpenExp env aenv (PDExp Int) alab args)]
            -> (forall env2. EContext Int env2 -> IdGen (OpenExp env2 aenv (PDExp Int) alab args t))
            -> IdGen (OpenExp env' aenv (PDExp Int) alab args t)
    bindAll ctx _ [] cont = cont ctx
    bindAll (Context labelenv bindmap) w ((lab :=> ex) : rest) cont =
        trace ("bindAll: let-binding expression at label " ++ showDLabel lab) $
        Let (A.LeftHandSideSingle (labelType lab)) (sinkExp w ex)
            <$> bindAll (Context (LPush labelenv lab) bindmap) (A.weakenSucc' w) rest cont

enumerateLabelenv :: LabVal s lab env -> [DSum (DLabel s lab) (Idx env)]
enumerateLabelenv = go A.weakenId
  where
    go :: env A.:> env' -> LabVal s lab env -> [DSum (DLabel s lab) (Idx env')]
    go _ LEmpty = []
    go w (LPush labelenv lab) = (lab :=> w A.>:> ZeroIdx) : go (A.weakenSucc w) labelenv

inlineAvarLabels :: Ord alab
                 => TupR (DLabel ArrayR alab) fv
                 -> A.ArrayVars aenv' fv
                 -> OpenExp env aenv lab alab args t
                 -> OpenExp env aenv' lab alab' args t
inlineAvarLabels labs vars = go (buildVarLabMap labs vars)
  where
    buildVarLabMap :: Ord alab
                   => TupR (DLabel ArrayR alab) fv
                   -> A.ArrayVars aenv' fv
                   -> DMap (DLabel ArrayR alab) (A.ArrayVar aenv')
    buildVarLabMap TupRunit TupRunit = mempty
    buildVarLabMap (TupRsingle lab) (TupRsingle var) = DMap.singleton lab var
    buildVarLabMap (TupRpair l1 l2) (TupRpair v1 v2) =
        DMap.unionWithKey (error "Overlapping labels in buildVarLabMap") (buildVarLabMap l1 v1) (buildVarLabMap l2 v2)
    buildVarLabMap _ _ = error "Impossible GADTs"

    go :: Ord alab
       => DMap (DLabel ArrayR alab) (A.ArrayVar aenv')
       -> OpenExp env aenv lab alab args t
       -> OpenExp env aenv' lab alab' args t
    go mp = \case
        Const ty x -> Const ty x
        PrimApp ty op ex -> PrimApp ty op (go mp ex)
        Pair ty e1 e2 -> Pair ty (go mp e1) (go mp e2)
        Nil -> Nil
        Cond ty e1 e2 e3 -> Cond ty (go mp e1) (go mp e2) (go mp e3)
        Shape (Right lab)
          | Just var <- DMap.lookup lab mp -> Shape (Left var)
          | otherwise -> error "inlineAvarLabels: Not all labels instantiated"
        Shape (Left _) -> error "inlineAvarLabels: Array variable found in labelised expression"
        Get ty tidx ex -> Get ty tidx (go mp ex)
        Let lhs rhs ex -> Let lhs (go mp rhs) (go mp ex)
        Var v -> Var v
        Arg ty idx -> Arg ty idx
        Label l -> Label l

-- Produces an expression that can be put under a LHS that binds exactly the
-- 'args' of the original expression.
realiseArgs :: Exp aenv lab alab args res -> A.ELeftHandSide t () args -> OpenExp args aenv lab alab () res
realiseArgs = \expr lhs -> go A.weakenId (A.weakenWithLHS lhs) expr
  where
    go :: args A.:> env' -> env A.:> env' -> OpenExp env aenv lab alab args res -> OpenExp env' aenv lab alab () res
    go argWeaken varWeaken expr = case expr of
        Const ty x -> Const ty x
        PrimApp ty op ex -> PrimApp ty op (go argWeaken varWeaken ex)
        Pair ty e1 e2 -> Pair ty (go argWeaken varWeaken e1) (go argWeaken varWeaken e2)
        Nil -> Nil
        Cond ty e1 e2 e3 -> Cond ty (go argWeaken varWeaken e1) (go argWeaken varWeaken e2) (go argWeaken varWeaken e3)
        Shape avar -> Shape avar
        Get ty tidx ex -> Get ty tidx (go argWeaken varWeaken ex)
        Let lhs rhs ex
          | GenLHS lhs' <- generaliseLHS lhs ->
              Let lhs' (go argWeaken varWeaken rhs)
                  (go (A.weakenWithLHS lhs' A..> argWeaken) (A.sinkWithLHS lhs lhs' varWeaken) ex)
        Var (A.Var ty idx) -> Var (A.Var ty (varWeaken A.>:> idx))
        Arg ty idx -> Var (A.Var ty (argWeaken A.>:> idx))
        Label _ -> error "realiseArgs: unexpected Label"

-- Map will NOT contain:
-- - Let or Var
-- - Label: the original expression should not have included Label
explode :: ELabVal Int env -> OpenExp env aenv unused alab args t -> IdGen (Exploded aenv Int alab args t)
explode labelenv e =
    trace ("exp explode: exploding " ++ showsExp (const "L?") (const "AL?") 0 [] [] 9 e "") $
    explode' labelenv e

explode' :: ELabVal Int env -> OpenExp env aenv unused alab args t -> IdGen (Exploded aenv Int alab args t)
explode' env = \case
    Const ty x -> do
        lab <- genId (TupRsingle ty)
        return (lab, DMap.singleton lab (Const ty x), mempty)
    PrimApp ty f e -> do
        (lab1, mp1, argmp) <- explode' env e
        lab <- genId ty
        let pruned = PrimApp ty f (Label lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping arg's") mp1 itemmp
        return (lab, mp, argmp)
    Pair ty e1 e2 -> do
        (lab1, mp1, argmp1) <- explode' env e1
        (lab2, mp2, argmp2) <- explode' env e2
        lab <- genId ty
        let pruned = Pair ty (Label lab1) (Label lab2)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mp2, itemmp]
            argmp = DMap.unionWithKey (error "explode: Overlapping arg's") argmp1 argmp2
        return (lab, mp, argmp)
    Nil -> do
        lab <- genId TupRunit
        return (lab, DMap.singleton lab Nil, mempty)
    Cond ty e1 e2 e3 -> do
        (lab1, mp1, argmp1) <- explode' env e1
        (lab2, mp2, argmp2) <- explode' env e2
        (lab3, mp3, argmp3) <- explode' env e3
        lab <- genId ty
        let pruned = Cond ty (Label lab1) (Label lab2) (Label lab3)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mp2, mp3, itemmp]
            argmp = DMap.unionsWithKey (error "explode: Overlapping arg's") [argmp1, argmp2, argmp3]
        return (lab, mp, argmp)
    Shape (Left avar@(A.Var (ArrayR sht _) _)) -> do
        lab <- genId (shapeType sht)
        return (lab, DMap.singleton lab (Shape (Left avar)), mempty)
    Shape (Right alab@(DLabel (ArrayR sht _) _)) -> do
        lab <- genId (shapeType sht)
        return (lab, DMap.singleton lab (Shape (Right alab)), mempty)
    Let lhs rhs body -> do
        (lab1, mp1, argmp1) <- explode' env rhs
        (_, labs) <- genSingleIds (etypeOf rhs)
        let (env', mpLHS) = lpushLHS_Get lhs labs env (Label lab1)
        (lab2, mp2, argmp2) <- explode' env' body
        let mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mpLHS, mp2]
            argmp = DMap.unionWithKey (error "explode: Overlapping arg's") argmp1 argmp2
        return (lab2, mp, argmp)
    Var (A.Var _ idx) -> do
        return (tupleLabel (prjL idx env), mempty, mempty)
    Arg ty idx -> do
        lab <- genId (TupRsingle ty)
        return (lab, DMap.singleton lab (Arg ty idx), DMap.singleton idx lab)
    Get _ _ _ -> error "explode: Unexpected Get"
    Label _ -> error "explode: Unexpected Label"
  where
    lpushLHS_Get :: A.ELeftHandSide t env env' -> TupR (EDLabel Int) t -> ELabVal Int env -> Exp aenv Int alab args t -> (ELabVal Int env', DMap (EDLabelT Int) (Exp aenv Int alab args))
    lpushLHS_Get lhs labs labelenv rhs = case (lhs, labs) of
        (A.LeftHandSidePair lhs1 lhs2, TupRpair labs1 labs2) ->
            let (labelenv1, mp1) = lpushLHS_Get lhs1 labs1 labelenv (smartFst rhs)
                (labelenv2, mp2) = lpushLHS_Get lhs2 labs2 labelenv1 (smartSnd rhs)
            in (labelenv2, DMap.unionWithKey (error "lpushLHS_Get: Overlapping id's") mp1 mp2)
        (A.LeftHandSideSingle _, TupRsingle lab) -> (LPush labelenv lab, DMap.singleton (tupleLabel lab) rhs)
        (A.LeftHandSideWildcard _, _) -> (labelenv, mempty)
        _ -> error "lpushLHS_Get: impossible GADTs"

    -- TODO: make smartFst and smartSnd non-quadratic (should be easy)
    smartFst :: OpenExp env aenv lab alab args (t1, t2) -> OpenExp env aenv lab alab args t1
    smartFst (Get (TupRpair t1 _) tidx ex) = Get t1 (insertFst tidx) ex
      where insertFst :: TupleIdx t (t1, t2) -> TupleIdx t t1
            insertFst TIHere = TILeft TIHere
            insertFst (TILeft ti) = TILeft (insertFst ti)
            insertFst (TIRight ti) = TIRight (insertFst ti)
    smartFst ex
      | TupRpair t1 _ <- etypeOf ex
      = Get t1 (TILeft TIHere) ex
    smartFst _ = error "smartFst: impossible GADTs"

    smartSnd :: OpenExp env aenv lab alab args (t1, t2) -> OpenExp env aenv lab alab args t2
    smartSnd (Get (TupRpair _ t2) tidx ex) = Get t2 (insertSnd tidx) ex
      where insertSnd :: TupleIdx t (t1, t2) -> TupleIdx t t2
            insertSnd TIHere = TIRight TIHere
            insertSnd (TILeft ti) = TILeft (insertSnd ti)
            insertSnd (TIRight ti) = TIRight (insertSnd ti)
    smartSnd ex
      | TupRpair _ t2 <- etypeOf ex
      = Get t2 (TIRight TIHere) ex
    smartSnd _ = error "smartSnd: impossible GADTs"

showContext :: (Ord lab, Show lab) => EContext lab env -> String
showContext (Context labelenv bindmap) = "Context " ++ showLabelenv labelenv ++ " " ++ showBindmap bindmap

showLabelenv :: Show lab => ELabVal lab env -> String
showLabelenv LEmpty = "[]"
showLabelenv (LPush env lab) = "[" ++ go env ++ showDLabel lab ++ "]"
  where
    go :: Show lab => ELabVal lab env -> String
    go LEmpty = ""
    go (LPush env' lab') = go env' ++ showDLabel lab' ++ ", "

showBindmap :: (Ord lab, Show lab) => DMap (EDLabelT (PDExp lab)) (TupR (EDLabel lab)) -> String
showBindmap bindmap =
    let tups = sortOn fst [(lab, (showDLabel dlab, showTupR showDLabel labs))
                          | dlab@(DLabel _ lab) :=> labs <- DMap.assocs bindmap]
        s = intercalate ", " ["(" ++ dlabshow ++ ") :=> " ++ labsshow
                             | (_, (dlabshow, labsshow)) <- tups]
    in "[" ++ s ++ "]"

-- TODO: remove Show constraint from alab
primaldual :: Show alab
           => Exploded aenv Int alab args Float
           -> (forall env. EContext Int env -> IdGen (OpenExp env aenv (PDExp Int) alab args t))
           -> IdGen (Exp aenv (PDExp Int) alab args t)
primaldual exploded cont = do
    PrimalResult context1 builder1 <- primal exploded
    DualResult context2 _ builder2 <- dual exploded (const (Const scalarType 1.0)) context1
    builder1 . builder2 <$> cont context2

-- Before, the primal computation generator function was in CPS form, taking a
-- continuation instead of returning a datatype containing an existential.
-- (Note the duality between those two approaches.) Because I needed to
-- integrate 'primal' into code that was not written in CPS style, but still
-- needed to put nontrivial information in the core, I re-wrote primal (and
-- dual) to return existentials instead of take a continuation.
data PrimalResult env aenv alab args =
    forall env'.
        PrimalResult (EContext Int env')
                     (forall res. OpenExp env' aenv (PDExp Int) alab args res
                               -> OpenExp env aenv (PDExp Int) alab args res)

-- Resulting computation will only use P, never D
primal :: Exploded aenv Int alab args res
       -> IdGen (PrimalResult () aenv alab args)
primal (endlab, nodemap, _) = primal' nodemap endlab (Context LEmpty mempty)

primal' :: DMap (EDLabelT Int) (Exp aenv Int alab args)
        -> EDLabelT Int t
        -> EContext Int env
        -> IdGen (PrimalResult env aenv alab args)
primal' nodemap lbl (Context labelenv bindmap)
--   | trace ("primal': computing " ++ show lbl) False = undefined
  | fmapLabel P lbl `DMap.member` bindmap =
      return $ PrimalResult (Context labelenv bindmap) id
  | not (uniqueLabVal labelenv) =  -- TODO: remove this check
      error "Non-unique label valuation in primal'!"
  | otherwise =
      case nodemap `dmapFind` lbl of
          Const ty value -> do
              lblS <- genSingleId ty
              return $ PrimalResult (Context (LPush labelenv lblS) (DMap.insert (fmapLabel P lbl) (TupRsingle lblS) bindmap))
                                    (Let (A.LeftHandSideSingle ty) (Const ty value))

          Pair _ (Label arglab1) (Label arglab2) -> do
              PrimalResult ctx1 f1 <- primal' nodemap arglab1 (Context labelenv bindmap)
              PrimalResult (Context labelenv' bindmap') f2 <- primal' nodemap arglab2 ctx1
              -- Note: We don't re-bind the constructed tuple into a new let
              -- binding with fresh labels here; we just point the tuple label
              -- for this Pair expression node to the pre-existing scalar labels.
              let labs = TupRpair (bindmap' `dmapFind` fmapLabel P arglab1)
                                  (bindmap' `dmapFind` fmapLabel P arglab2)
              return $ PrimalResult (Context labelenv' (DMap.insert (fmapLabel P lbl) labs bindmap'))
                                    (f1 . f2)

          Nil ->
              -- No scalar labels are allocated for a Nil node, but we should still
              -- record that empty set of labels.
              return $ PrimalResult (Context labelenv (DMap.insert (fmapLabel P lbl) TupRunit bindmap)) id

          PrimApp restype oper (Label arglab) -> do
              PrimalResult (Context labelenv' bindmap') f1 <- primal' nodemap arglab (Context labelenv bindmap)
              let arglabs = bindmap' `dmapFind` fmapLabel P arglab
              case elabValFinds labelenv' arglabs of
                  Just vars -> do
                      (GenLHS lhs, labs) <- genSingleIds restype
                      return $ PrimalResult (Context (lpushLabTup labelenv' lhs labs) (DMap.insert (fmapLabel P lbl) labs bindmap'))
                                            (f1 . Let lhs (PrimApp restype oper (evars vars)))
                  Nothing ->
                      error "primal: App argument did not compute argument"

          -- TODO: inlining of the produced halves into the branches of the
          -- generated Cond operation, so that the halves are really only
          -- computed if needed.
          -- TODO: Also think about: what if the code contains:
          --   (cond c t e) + (cond (not c) e t)
          -- Because both t and e are shared, they cannot be inlined, and will
          -- thus always be computed, even if in the end only one is needed in
          -- all situations. But then, don't write code like that.
          Cond restype (Label condlab) (Label thenlab) (Label elselab) -> do
              PrimalResult ctx1 f1 <- primal' nodemap condlab (Context labelenv bindmap)
              PrimalResult ctx2 f2 <- primal' nodemap thenlab ctx1
              PrimalResult (Context labelenv' bindmap') f3 <- primal' nodemap elselab ctx2
              let condlabs = bindmap' `dmapFind` fmapLabel P condlab
                  thenlabs = bindmap' `dmapFind` fmapLabel P thenlab
                  elselabs = bindmap' `dmapFind` fmapLabel P elselab
              case (elabValFinds labelenv' condlabs
                   ,elabValFinds labelenv' thenlabs
                   ,elabValFinds labelenv' elselabs) of
                  (Just condvars, Just thenvars, Just elsevars) -> do
                      (GenLHS lhs, labs) <- genSingleIds restype
                      return $ PrimalResult (Context (lpushLabTup labelenv' lhs labs) (DMap.insert (fmapLabel P lbl) labs bindmap'))
                                            (f1 . f2 . f3 . Let lhs (Cond restype (evars condvars) (evars thenvars) (evars elsevars)))
                  _ ->
                      error "primal: Cond arguments did not compute arguments"

          Get _ path (Label arglab) -> do
              PrimalResult (Context labelenv' bindmap') f1 <- primal' nodemap arglab (Context labelenv bindmap)
              let pickedlabs = pickDLabels path (bindmap' `dmapFind` fmapLabel P arglab)
              -- Note: We don't re-bind the picked tuple into a new let binding
              -- with fresh labels here; we just point the tuple label for this
              -- Get expression node to the pre-existing scalar labels.
              return $ PrimalResult (Context labelenv' (DMap.insert (fmapLabel P lbl) pickedlabs bindmap')) f1

          Arg ty idx -> do
              labS <- genSingleId ty
              return $ PrimalResult (Context (LPush labelenv labS) (DMap.insert (fmapLabel P lbl) (TupRsingle labS) bindmap))
                                    (Let (A.LeftHandSideSingle ty) (Arg ty idx))

          Label arglab -> do
              PrimalResult (Context labelenv' bindmap') f1 <- primal' nodemap arglab (Context labelenv bindmap)
              let arglabs = bindmap' `dmapFind` fmapLabel P arglab
              -- Note: We don't re-bind the labeled tuple into a new let binding
              -- with fresh labels here; we just point the tuple label for this
              -- Label expression node to the pre-existing scalar labels.
              return $ PrimalResult (Context labelenv' (DMap.insert (fmapLabel P lbl) arglabs bindmap')) f1

          _ ->
              error "primal: Unexpected node shape in Exploded"

-- List of adjoints, collected for a particular label.
-- The exact variable references in the adjoints are dependent on the Let stack, thus the
-- environment (and the bindmap) is needed.
newtype AdjList aenv lab alab args t = AdjList (forall env. EContext lab env -> [OpenExp env aenv (PDExp lab) alab args t])

type AnyLabelT = AnyLabel TypeR

-- The Ord and Eq instances refer only to 'a'.
data OrdBox a b = OrdBox { _ordboxTag :: a, ordboxAuxiliary :: b }
instance Eq  a => Eq  (OrdBox a b) where OrdBox x _    ==     OrdBox y _ = x == y
instance Ord a => Ord (OrdBox a b) where OrdBox x _ `compare` OrdBox y _ = compare x y

data DualResult env aenv alab args =
    forall env'.
        DualResult (EContext Int env')
                   (DMap (EDLabelT (PDExp Int)) (AdjList aenv Int alab args))  -- contribmap
                   (forall res. OpenExp env' aenv (PDExp Int) alab args res
                             -> OpenExp env aenv (PDExp Int) alab args res)

dual :: Show alab
     => Exploded aenv Int alab args t
     -> (forall env'. EContext Int env' -> OpenExp env' aenv (PDExp Int) alab args t)
     -> EContext Int env
     -> IdGen (DualResult env aenv alab args)
dual (endlab, nodemap, _) endadjoint context =
    trace ("\nexp labelorder: " ++ show [labelLabel l | AnyLabel l <- labelorder]) $
    let contribmap = DMap.singleton (fmapLabel D endlab) (AdjList (pure . endadjoint))
    in dual's nodemap labelorder context contribmap
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

dual's :: Show alab
       => DMap (EDLabelT Int) (Exp aenv Int alab args)
       -> [AnyLabelT Int]
       -> EContext Int env
       -> DMap (EDLabelT (PDExp Int)) (AdjList aenv Int alab args)
       -> IdGen (DualResult env aenv alab args)
dual's _ [] context contribmap = return $ DualResult context contribmap id
dual's nodemap (AnyLabel lab : labs) context contribmap = do
    DualResult context1 contribmap1 f1 <- dual' nodemap lab context contribmap
    DualResult context2 contribmap2 f2 <- dual's nodemap labs context1 contribmap1
    return $ DualResult context2 contribmap2 (f1 . f2)

dual' :: Show alab
      => DMap (EDLabelT Int) (Exp aenv Int alab args)
      -> EDLabelT Int t
      -> EContext Int env
      -> DMap (EDLabelT (PDExp Int)) (AdjList aenv Int alab args)
      -> IdGen (DualResult env aenv alab args)
dual' nodemap lbl (Context labelenv bindmap) contribmap =
    -- trace ("dual': computing " ++ show lbl) $
    case nodemap `dmapFind` lbl of
      -- We aren't interested in the adjoint of constant nodes -- seeing as
      -- they don't have any parents to contribute to.
      Const _ _ ->
          return $ DualResult (Context labelenv bindmap) contribmap id

      -- Argument nodes don't have any nodes to contribute to either, but we do
      -- need to calculate and store their adjoint.
      Arg restypeS _ -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      PrimApp _ (A.PrimAdd restypeN) (Label arglab) -> do
          let restypeS = SingleScalarType (NumSingleType restypeN)
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil $ \(TupRsingle adjvar) _ ->
                                    smartPair (Var adjvar) (Var adjvar)]
                                contribmap
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap'
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      PrimApp restype (A.PrimMul restypeN) (Label arglab) -> do
          let restypeS = SingleScalarType (NumSingleType restypeN)
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) $ \(TupRsingle adjvar) (TupRpair (TupRsingle argvar1) (TupRsingle argvar2) :@ TLNil) ->
                                    smartPair
                                         (PrimApp restype (A.PrimMul restypeN) (smartPair (Var adjvar) (Var argvar2)))
                                         (PrimApp restype (A.PrimMul restypeN) (smartPair (Var adjvar) (Var argvar1)))]
                                contribmap
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap'
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      PrimApp restype (A.PrimLog restypeF) (Label arglab) -> do
          let restypeS = SingleScalarType (NumSingleType (FloatingNumType restypeF))
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) $ \(TupRsingle adjvar) (TupRsingle argvar :@ TLNil) ->
                                    -- dE/dx = dE/d(log x) * d(log x)/dx = adjoint * 1/x = adjoint / x
                                    PrimApp restype (A.PrimFDiv restypeF)
                                        (smartPair (Var adjvar) (Var argvar))]
                                contribmap
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap'
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      -- Argument is an integral type, which takes no contributions
      PrimApp _ (A.PrimToFloating _ restypeF) _ -> do
          let restypeS = SingleScalarType (NumSingleType (FloatingNumType restypeF))
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      -- Result is an integral type, which produces no contributions (because
      -- its adjoint is always zero). Therefore, we also have no contributions
      -- to our parents.
      -- Also, since contributions of integer-valued nodes are not used
      -- anywhere, we don't even have to generate this zero adjoint. TODO: is this true?
      PrimApp (TupRsingle (SingleScalarType (NumSingleType (IntegralNumType _)))) _ _ ->
          return $ DualResult (Context labelenv bindmap) contribmap id

      Cond restype (Label condlab) (Label thenlab) (Label elselab) -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution thenlab (condlab :@ TLNil) $ \adjvars (TupRsingle condvar :@ TLNil) ->
                                    Cond restype (Var condvar) (evars adjvars) (zeroForType restype)
                                ,Contribution elselab (condlab :@ TLNil) $ \adjvars (TupRsingle condvar :@ TLNil) ->
                                    Cond restype (Var condvar) (zeroForType restype) (evars adjvars)]
                                contribmap
          (GenLHS lhs, labs) <- genSingleIds restype
          return $ DualResult (Context (lpushLabTup labelenv lhs labs)
                                       (DMap.insert (fmapLabel D lbl) labs bindmap))
                              contribmap'
                              (Let lhs adjoint)

      Get restype path (Label arglab) -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil $ \adjvars _ ->
                                    oneHotTup (labelType arglab) path (evars adjvars)]
                                contribmap
          (GenLHS lhs, labs) <- genSingleIds restype
          return $ DualResult (Context (lpushLabTup labelenv lhs labs)
                                       (DMap.insert (fmapLabel D lbl) labs bindmap))
                              contribmap'
                              (Let lhs adjoint)

      Pair restype (Label arglab1) (Label arglab2) -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab1 TLNil $ \(TupRpair adjvars1 _) _ ->
                                    evars adjvars1
                                ,Contribution arglab2 TLNil $ \(TupRpair _ adjvars2) _ ->
                                    evars adjvars2]
                                contribmap
          (GenLHS lhs, labs) <- genSingleIds restype
          return $ DualResult (Context (lpushLabTup labelenv lhs labs)
                                       (DMap.insert (fmapLabel D lbl) labs bindmap))
                              contribmap'
                              (Let lhs adjoint)

      Nil ->
          -- Nothing to compute here, but we still need to register this expression label
          -- in the bindmap.
          return $ DualResult (Context labelenv (DMap.insert (fmapLabel D lbl) TupRunit bindmap))
                              contribmap id

      Label arglab -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil $ \adjvars _ ->
                                    evars adjvars]
                                contribmap
          (GenLHS lhs, labs) <- genSingleIds (labelType arglab)
          return $ DualResult (Context (lpushLabTup labelenv lhs labs)
                                       (DMap.insert (fmapLabel D lbl) labs bindmap))
                              contribmap'
                              (Let lhs adjoint)

      expr -> trace ("\n!! " ++ show expr) undefined
  where
    smartPair :: OpenExp env aenv lab alab args a -> OpenExp env aenv lab alab args b -> OpenExp env aenv lab alab args (a, b)
    smartPair a b = Pair (TupRpair (etypeOf a) (etypeOf b)) a b

-- TODO: make a new abstraction after the refactor, possibly inspired by this function, which was the abstraction pre-refactor
-- dualStoreAdjoint
--     :: DMap (DLabel Int) (Exp Int args)
--     -> [AnyLabel Int]
--     -> (forall env'. LabVal (PDExp Int) env' -> OpenExp env' aenv (PDExp Int) args res)
--     -> DLabel Int t
--     -> LabVal (PDExp Int) env
--     -> DMap (DLabel (PDExp Int)) (AdjList aenv (PDExp Int) args)
--     -> [Contribution t aenv args]
--     -> OpenExp env aenv (PDExp Int) args res
-- dualStoreAdjoint nodemap restlabels cont lbl labelenv contribmap contribs =
--     let adjoint = collectAdjoint contribmap lbl (TupRsingle (labelType lbl)) labelenv
--         contribmap' = updateContribmap lbl contribs contribmap
--     in Let (A.LeftHandSideSingle (labelType lbl)) adjoint
--            (dual' nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)

-- Utility functions
-- -----------------

infixr :@
data TypedList f tys where
    TLNil :: TypedList f '[]
    (:@) :: f t -> TypedList f tys -> TypedList f (t ': tys)

tlmap :: (forall t. f t -> g t) -> TypedList f tys -> TypedList g tys
tlmap _ TLNil = TLNil
tlmap f (x :@ xs) = f x :@ tlmap f xs

data Contribution node aenv alab args =
    forall parents t.
        Contribution (EDLabelT Int t)  -- to which label are we contributing an adjoint
                     (TypedList (EDLabelT Int) parents)  -- labels you need the primary value of
                     (forall env. A.ExpVars env node                  -- current node's adjoint
                               -> TypedList (A.ExpVars env) parents   -- requested primal values
                               -> OpenExp env aenv (PDExp Int) alab args t)   -- contribution

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
                 -> [Contribution node aenv alab args]
                 -> DMap (EDLabelT (PDExp Int)) (AdjList aenv Int alab args)
                 -> DMap (EDLabelT (PDExp Int)) (AdjList aenv Int alab args)
updateContribmap lbl =
    flip . foldr $ \(Contribution lab parentlabs gen) ->
        addContribution (fmapLabel D lab) $ \(Context labelenv bindmap) ->
            let currentlabs = bindmap `dmapFind` fmapLabel D lbl
            in case (elabValFinds labelenv currentlabs, findAll (Context labelenv bindmap) parentlabs) of
                (Just adjvars, parvars) -> gen adjvars parvars
                _ -> error $ "updateContribmap: node D " ++ show lbl ++ " was not computed"
  where
    findAll :: EContext Int env -> TypedList (EDLabelT Int) parents -> TypedList (A.ExpVars env) parents
    findAll (Context labelenv bindmap) =
        tlmap $ \lab ->
            let labs = bindmap `dmapFind` fmapLabel P lab
            in fromMaybe (error $ "updateContribmap: arg P " ++ show lab ++ " was not computed; labs: " ++ showTupR show labs ++ "; labelenv: " ++ showLabelenv labelenv ++ "; bindmap: " ++ showBindmap bindmap) (elabValFinds labelenv labs)

addContribution :: Ord lab
                => EDLabelT (PDExp lab) t
                -> (forall env. EContext lab env -> OpenExp env aenv (PDExp lab) alab args t)
                -> DMap (EDLabelT (PDExp lab)) (AdjList aenv lab alab args)
                -> DMap (EDLabelT (PDExp lab)) (AdjList aenv lab alab args)
addContribution lbl contribution =
    DMap.insertWith (\(AdjList f1) (AdjList f2) -> AdjList (\context -> f1 context ++ f2 context))
                    lbl
                    (AdjList (pure . contribution))

collectAdjoint :: DMap (EDLabelT (PDExp Int)) (AdjList aenv Int alab args)
               -> EDLabelT Int item
               -> EContext Int env
               -> OpenExp env aenv (PDExp Int) alab args item
collectAdjoint contribmap lbl (Context labelenv bindmap) =
    case DMap.lookup (fmapLabel D lbl) contribmap of
        Just (AdjList listgen) -> expSum (labelType lbl) (listgen (Context labelenv bindmap))
        Nothing -> expSum (labelType lbl) []  -- if there are no contributions, well, the adjoint is an empty sum (i.e. zero)

oneHotTup :: TypeR t -> TupleIdx t t' -> OpenExp env aenv lab alab args t' -> OpenExp env aenv lab alab args t
oneHotTup _ TIHere ex = ex
oneHotTup ty@(TupRpair ty1 ty2) (TILeft ti) ex = Pair ty (oneHotTup ty1 ti ex) (zeroForType ty2)
oneHotTup ty@(TupRpair ty1 ty2) (TIRight ti) ex = Pair ty (zeroForType ty1) (oneHotTup ty2 ti ex)
oneHotTup _ _ _ = error "oneHotTup: impossible GADTs"

-- Errors if any parents are not Label nodes, or if called on a Let or Var node.
expLabelParents :: OpenExp env aenv lab alab args t -> [AnyLabelT lab]
expLabelParents = \case
    Const _ _ -> []
    PrimApp _ _ e -> fromLabel e
    Pair _ e1 e2 -> fromLabel e1 ++ fromLabel e2
    Nil -> []
    Cond _ e1 e2 e3 -> fromLabel e1 ++ fromLabel e2 ++ fromLabel e3
    Shape _ -> []
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

dmapFind :: (HasCallStack, GCompare f) => DMap f g -> f a -> g a
dmapFind mp elt = case DMap.lookup elt mp of
                    Just res -> res
                    Nothing -> error "dmapFind: not found"
