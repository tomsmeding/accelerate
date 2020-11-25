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
  splitLambdaAD, labeliseFun,
  labeliseExp, inlineAvarLabels'
) where

import qualified Control.Monad.Writer as W
import Data.GADT.Compare (GCompare)
import Data.List (intercalate, sortOn)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Map (DMap)
import Data.Dependent.Sum
import Data.Type.Equality

import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Environment as A
import qualified Data.Array.Accelerate.AST.Idx as A
import qualified Data.Array.Accelerate.AST.LeftHandSide as A
import Data.Array.Accelerate.AST.LeftHandSide (Exists(..))
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.Error (HasCallStack, internalError)
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (shapeType)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.AD.Additive
import Data.Array.Accelerate.Trafo.AD.Algorithms
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Debug
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.Pretty
import Data.Array.Accelerate.Trafo.AD.Sink
import Data.Array.Accelerate.Trafo.Substitution (rebuildLHS, weakenVars)
import Data.Array.Accelerate.Trafo.Var (declareVars, DeclareVars(..))


genId :: TypeR t -> IdGen (EDLabelN Int t)
genId = genId'

genIdNodeSingle :: ScalarType t -> IdGen (EDLabelNS Int t)
genIdNodeSingle = genId'

genIds :: TypeR t -> IdGen (Exists (A.ELeftHandSide t env), TupR (EDLabelNS Int) t)
genIds TupRunit = return (Exists (A.LeftHandSideWildcard TupRunit), TupRunit)
genIds (TupRsingle ty) = (Exists (A.LeftHandSideSingle ty),) . TupRsingle <$> genIdNodeSingle ty
genIds (TupRpair t1 t2) = do
    (Exists lhs1, ids1) <- genIds t1
    (Exists lhs2, ids2) <- genIds t2
    return (Exists (A.LeftHandSidePair lhs1 lhs2), TupRpair ids1 ids2)

genSingleId :: ScalarType t -> IdGen (EDLabel Int t)
genSingleId = genId'

genSingleIds :: TypeR t -> IdGen (Exists (A.ELeftHandSide t env), TupR (EDLabel Int) t)
genSingleIds TupRunit = return (Exists (A.LeftHandSideWildcard TupRunit), TupRunit)
genSingleIds (TupRsingle ty) = (Exists (A.LeftHandSideSingle ty),) . TupRsingle <$> genSingleId ty
genSingleIds (TupRpair t1 t2) = do
    (Exists lhs1, ids1) <- genSingleIds t1
    (Exists lhs2, ids2) <- genSingleIds t2
    return (Exists (A.LeftHandSidePair lhs1 lhs2), TupRpair ids1 ids2)


-- TODO: make this a data definition, not a tuple
data Exploded aenv lab alab args tenv res =
    Exploded { exEndLabel :: EDLabelN lab res
             , exNodeMap :: DMap (EDLabelN lab) (Exp aenv lab alab args tenv)
             , exArgMap :: DMap (A.Idx args) (EDLabelN lab)
             , _exSubTree :: Set (EAnyLabelN lab) }

instance (Ord lab, Show lab, Show alab) => Show (Exploded aenv lab alab args tenv t) where
    show (Exploded endlab nodemap argmap subtree) =
        "Exploded (" ++ showDLabel endlab ++ ") (" ++ showNodemap nodemap ++ ") (" ++ showArgmap argmap ++ ") (" ++ show subtree ++ ")"

showNodemap :: (Ord lab, Show lab, Show alab) => DMap (EDLabelN lab) (Exp aenv lab alab args tenv) -> String
showNodemap nodemap =
    let tups = sortOn fst [(lab, (showDLabel dlab, show expr))
                          | dlab@(DLabel _ lab) :=> expr <- DMap.assocs nodemap]
        s = intercalate ", " ["(" ++ dlabshow ++ ") :=> " ++ exprshow
                             | (_, (dlabshow, exprshow)) <- tups]
    in "[" ++ s ++ "]"

showArgmap :: Show lab => DMap (A.Idx args) (EDLabelN lab) -> String
showArgmap argmap =
    let s = intercalate ", " ['A' : show (A.idxToInt argidx) ++ " :=> " ++ showDLabel dlab
                             | argidx :=> dlab <- DMap.assocs argmap]
    in "[" ++ s ++ "]"

-- Assumes the expression does not contain Arg
generaliseArgs :: OpenExp env aenv lab alab args tenv t -> OpenExp env aenv lab alab args' tenv t
generaliseArgs (Const ty x) = Const ty x
generaliseArgs (PrimApp ty op ex) = PrimApp ty op (generaliseArgs ex)
generaliseArgs (PrimConst c) = PrimConst c
generaliseArgs (Pair ty e1 e2) = Pair ty (generaliseArgs e1) (generaliseArgs e2)
generaliseArgs Nil = Nil
generaliseArgs (Cond ty e1 ns2 e2 ns3 e3) = Cond ty (generaliseArgs e1) ns2 (generaliseArgs e2) ns3 (generaliseArgs e3)
generaliseArgs (Shape ref) = Shape ref
generaliseArgs (Index ref idx) = Index ref (either (Left . generaliseArgs) Right idx)
generaliseArgs (ShapeSize sht e) = ShapeSize sht (generaliseArgs e)
generaliseArgs (Get ty path ex) = Get ty path (generaliseArgs ex)
generaliseArgs (Undef ty) = Undef ty
generaliseArgs (Let lhs rhs ex) = Let lhs (generaliseArgs rhs) (generaliseArgs ex)
generaliseArgs (Var v) = Var v
generaliseArgs (FreeVar v) = FreeVar v
generaliseArgs (Arg _ _) = error "generaliseArgs: Arg found"
generaliseArgs (Label labs) = Label labs

data ReverseADResE aenv alab tenv t = forall env. ReverseADResE (A.ELeftHandSide t () env) (OpenExp env aenv (PDExp Int) alab () tenv t)

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
reverseAD :: Show alab => A.ELeftHandSide t () env -> OpenExp env aenv unused alab () tenv Float -> ReverseADResE aenv alab tenv t
reverseAD paramlhs expr
  | ExpandLHS paramlhs' paramWeaken <- expandLHS paramlhs
  , DeclareVars paramlhs'2 _ varsgen <- declareVars (A.lhsToTupR paramlhs)
  , Refl <- sameLHSsameEnv paramlhs' paramlhs'2 =
      let argsVars = varsgen A.weakenId
          argsRHS = varsToArgs argsVars
          closedExpr = Let paramlhs' argsRHS (generaliseArgs (sinkExp paramWeaken expr))
          transformedExp = evalIdGen $ do
              exploded@Exploded { exArgMap = argLabelMap } <- explode LEmpty closedExpr
              traceM ("exploded: " ++ show exploded)
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
                  return $ produceGradient argLabelMap context argsVars
      in
          trace ("AD result: " ++ prettyPrint transformedExp) $
          ReverseADResE paramlhs' (realiseArgs transformedExp paramlhs')

varsToArgs :: A.ExpVars env t -> OpenExp env' aenv lab alab env tenv t
varsToArgs = untupleExps . fmapTupR (\(A.Var ty idx) -> Arg ty idx)

produceGradient :: DMap (Idx args) (EDLabelN Int)
                -> EContext Int env
                -> A.ExpVars args t
                -> OpenExp env aenv (PDExp Int) alab args' tenv t
produceGradient argLabelMap (Context labelenv bindmap) =
    untupleExps . fmapTupR (\(A.Var ty idx) ->
      case DMap.lookup idx argLabelMap of
        Just lab
          | Just labs <- DMap.lookup (fmapLabel D lab) bindmap
          , Just vars <- elabValFinds labelenv labs
          -> evars vars
        _
          -> error $ "produceGradient: Adjoint of Arg (" ++ show ty ++ ") " ++
                        'A' : show (A.idxToInt idx) ++ " not computed")

splitLambdaAD :: forall aenv t t' unused unused2 tenv.
                 LabVal NodeLabel ArrayR Int aenv
              -> Fun aenv unused unused2 tenv (t -> t')
              -> SomeSplitLambdaAD t t' (PDExp Int) Int tenv
splitLambdaAD alabelenv origfun@(Lam paramlhs (Body expr))
  | let exprtype = etypeOf expr
        argtype = A.lhsToTupR paramlhs
  , ExpandLHS paramlhs' paramWeaken <- expandLHS paramlhs
  , DeclareVars paramlhs'2 _ varsgen <- declareVars argtype
  , Refl <- sameLHSsameEnv paramlhs' paramlhs'2
  , let argsVars = varsgen A.weakenId
        argsRHS = varsToArgs argsVars
        closedExpr = Let paramlhs' argsRHS (sinkExp paramWeaken (generaliseArgs (generaliseLab expr)))
  , (fvlablist, labelisedExpr) <- labeliseExp alabelenv closedExpr
  , TuplifyVars _ fvlabs _ <- tuplifyVars fvlablist
  = -- trace ("AD result: " ++ show transformedExp) $
    evalIdGen $ do
        exploded@(Exploded reslab nodemap argLabelMap _) <- explode LEmpty labelisedExpr
        traceM ("exp exploded: " ++ show exploded)
        PrimalResult context@(Context labelenv bindmap) builder <- primal exploded
        traceM ("\nexp context in core: " ++ showContext context)
        let reslabs = bindmap DMap.! fmapLabel P reslab
        case elabValFinds labelenv reslabs of
            Just resultvars
              | EnvCapture tmpvars (EnvInstantiator instantiator) <- captureEnvironmentSlice (Context LEmpty mempty) context -> do
                  let primalBody = builder (evars (TupRpair resultvars tmpvars))

                  (Exists adjlhs, adjlabs) <- genSingleIds exprtype
                  -- TODO: is there a neater way to unwrap the existential?
                  LetBoundExpE tmpRestoreLHS tmpRestoreVars <- return (elhsCopy (A.varsType tmpvars))
                  (_, tmpRestoreLabs) <- genSingleIds (A.varsType tmpvars)
                  -- The type of the labelenv here is () |> adjoint... |> temporaries...,
                  -- where a |> b = (a, b), infixr |>. This nested tuple is the type of
                  -- the argument of the dual lambda.
                  let dualLabelenv = lpushLabTup (lpushLabTup LEmpty adjlhs adjlabs) tmpRestoreLHS tmpRestoreLabs
                      dualBindmap = instantiator (Context dualLabelenv mempty) tmpRestoreVars
                      dualInstCtx = Context dualLabelenv dualBindmap
                  traceM $ "invoking exp dual with context: " ++ showContext dualInstCtx
                  let adjointProducer :: EContext Int env -> OpenExp env aenv (PDExp Int) alab args tenv t'
                      adjointProducer (Context labelenv' _) =
                        case elabValFinds labelenv' adjlabs of
                            Just vars -> evars vars
                            Nothing -> error "splitLambdaAD: end-node adjoint label not put in labelenv?"
                  DualResult ctx' _ builder' <- dual exploded adjointProducer dualInstCtx
                  case collectIndexed ctx' nodemap of
                    CollectIndexed idxadjType idxInstantiators idxadjExpr -> do
                        let dualBody = builder' (smartPair (produceGradient argLabelMap ctx' argsVars) idxadjExpr)

                        -- The primal and dual lambda expression here are inlined because of the monomorphism restriction
                        return $ SomeSplitLambdaAD $
                            SplitLambdaAD (\fvavars ->
                                               Lam paramlhs'
                                                 (Body (realiseArgs
                                                           (inlineAvarLabels fvlabs fvavars primalBody)
                                                           paramlhs')))
                                          (\fvavars ->
                                               Lam (A.LeftHandSidePair adjlhs tmpRestoreLHS)
                                                   (Body (generaliseArgs
                                                             (inlineAvarLabels fvlabs fvavars dualBody))))
                                          fvlabs
                                          (A.varsType tmpvars)
                                          idxadjType
                                          idxInstantiators
            _ ->
                error "Final primal value not computed"
  | otherwise =
      internalError $ "Non-Float-producing lambdas under gradientA currently unsupported\nIn lambda: " ++
                          show (generaliseLabFunA (generaliseLabFun origfun) :: Fun aenv () () tenv (t -> t'))
splitLambdaAD _ _ =
    internalError "splitLambdaAD passed function with more than 1 argument"

-- Replaces all array variables by their labels in the array environment, and additionally returns the list of labels thus inserted.
-- The list of labels is deduplicated.
-- Asserts that there are no array labels yet in the expression, and resets the array environment.
labeliseFun :: Ord alab
            => LabVal NodeLabel ArrayR alab aenv
            -> OpenFun env aenv lab alab' tenv t
            -> ([AAnyLabelNS alab], OpenFun env aenv' lab alab tenv t)
labeliseFun labelenv (Lam lhs fun) = Lam lhs <$> labeliseFun labelenv fun
labeliseFun labelenv (Body ex) = Body <$> labeliseExp labelenv ex

-- Replaces all array variables by their labels in the array environment, and additionally returns the list of labels thus inserted.
-- The list of labels is deduplicated.
-- Asserts that there are no array labels yet in the expression, and resets the array environment.
labeliseExp :: Ord alab
            => LabVal NodeLabel ArrayR alab aenv
            -> OpenExp env aenv lab alab' args tenv t
            -> ([AAnyLabelNS alab], OpenExp env aenv' lab alab args tenv t)
labeliseExp labelenv = \ex -> let (labs, ex') = go ex
                              in (sortUniq labs, ex')
  where
    go ex = case ex of
      Const ty x -> return (Const ty x)
      PrimApp ty op e -> PrimApp ty op <$> labeliseExp labelenv e
      PrimConst c -> return (PrimConst c)
      Pair ty e1 e2 -> Pair ty <$> labeliseExp labelenv e1 <*> labeliseExp labelenv e2
      Nil -> return Nil
      Cond ty e1 ns2 e2 ns3 e3 -> Cond ty <$> labeliseExp labelenv e1 <*> return ns2 <*> labeliseExp labelenv e2 <*> return ns3 <*> labeliseExp labelenv e3
      Shape (Left (A.Var _ idx)) -> do
          let lab = prjL idx labelenv
          W.tell [AnyLabel lab]
          return (Shape (Right lab))
      Shape (Right _) -> error "Unexpected Shape(Label) in labeliseExp"
      Index (Left (A.Var _ idx)) idxe -> do
          let lab = prjL idx labelenv
          W.tell [AnyLabel lab]
          Index (Right lab) <$> either (fmap Left . labeliseExp labelenv) (return . Right) idxe
      Index (Right _) _ -> error "Unexpected Index(Label) in labeliseExp"
      ShapeSize sht e -> ShapeSize sht <$> labeliseExp labelenv e
      Get ty ti e -> Get ty ti <$> labeliseExp labelenv e
      Undef ty -> return (Undef ty)
      Let lhs rhs e -> Let lhs <$> labeliseExp labelenv rhs <*> labeliseExp labelenv e
      Arg ty idx -> return (Arg ty idx)
      Var var -> return (Var var)
      FreeVar var -> return (FreeVar var)
      Label lab -> return (Label lab)

-- TODO: the first and third field of this data type seem to be unused. Remove them if so.
data TuplifyVars lty s lab env =
    forall env' t.
        TuplifyVars -- Collects vars from array environment outside the lambda
                     (forall env''. env' A.:> env'' -> A.Vars s env'' t)
                     -- The tuple of labels bound
                     (TupR (DLabel lty s lab) t)
                     -- Bind the collected vars in the lambda argument
                     (A.LeftHandSide s t env env')
                     -- -- Lookup vars in passed tuple inside the lambda
                     -- (forall aenv''. aenv' A.:> aenv'' -> DMap (DLabel ArrayR lab) (A.ArrayVar aenv''))

tuplifyVars :: Ord lab => [AnyLabel lty s lab] -> TuplifyVars lty s lab env
tuplifyVars [] = TuplifyVars (const TupRunit) TupRunit A.LeftHandSideUnit -- (const mempty)
tuplifyVars (AnyLabel lab@(DLabel ty _) : rest)
  | TuplifyVars tupexprf labs lhs {-mpf-} <- tuplifyVars rest
  = TuplifyVars (\w -> TupRpair (tupexprf (A.weakenSucc w))
                                (TupRsingle (A.Var ty (w A.>:> ZeroIdx))))
                (TupRpair labs (TupRsingle lab))
                (A.LeftHandSidePair lhs (A.LeftHandSideSingle ty))
                -- (\w -> DMap.insert lab (A.Var ty (w A.>:> ZeroIdx))
                --                    (mpf (A.weakenSucc w)))

data CollectIndexed env aenv lab alab args tenv =
    forall idxadj.
        CollectIndexed (TypeR idxadj)
                       (DMap (ADLabelNS alab) (IndexInstantiators idxadj))
                       (OpenExp env aenv lab alab args tenv idxadj)

data ArrLabelExpExp env aenv lab alab args tenv =
    forall sh t.
        ArrLabelExpExp (ADLabelNS alab (Array sh t))
                       (OpenExp env aenv lab alab args tenv t)
                       (OpenExp env aenv lab alab args tenv sh)

collectIndexed :: forall env aenv lab alab args tenv. (Ord lab, Ord alab, Show lab)
               => EContext lab env
               -> DMap (EDLabelN lab) (Exp aenv lab alab args tenv)  -- nodemap
               -> CollectIndexed env aenv (PDExp lab) alab args tenv
collectIndexed (Context labelenv bindmap) nodemap =
    let lookupNode :: EDLabelN lab t -> (lab -> PDExp lab) -> OpenExp env aenv lab' alab args tenv t
        lookupNode elab labkind
          | Just vars <- elabValFinds labelenv (bindmap `dmapFind` fmapLabel labkind elab) = evars vars
          | otherwise = error ("Label " ++ show elab ++ " from nodemap not in labelenv in collectIndexed")
        labels = [ArrLabelExpExp alab (lookupNode nodelab D) (lookupNode idxlab P)
                 | nodelab :=> Index ref idxarg <- DMap.toList nodemap
                 , let alab = either (error "Non-labelised nodemap in collectIndexed") id ref
                       idxlab = case idxarg of
                                  -- Here we take the backup label, not the actual argument label, because only that
                                  -- one is known to be bound in the same conditional branch as the Index itself.
                                  -- See Index in Exp.hs.
                                  Right (_, l) -> l
                                  _ -> error "Index argument not Label in collectIndexed"]
    in tuplify labels
  where
    tuplify :: [ArrLabelExpExp env aenv lab' alab args tenv] -> CollectIndexed env aenv lab' alab args tenv
    tuplify [] = CollectIndexed TupRunit mempty Nil
    tuplify (ArrLabelExpExp lab@(DLabel (ArrayR sht ty) _) adjexp idxexp : rest)
      | CollectIndexed tupty mp expr <- tuplify rest
      = let itemtype = TupRpair ty (shapeType sht)
            restype = TupRpair tupty itemtype
        in CollectIndexed restype
                          (let weakenInst :: TypeR (e, sh)  -- dummy argument to be able to reference those type variables in the return type
                                          -> IndexInstantiators idxadj arr
                                          -> IndexInstantiators (idxadj, (e, sh)) arr
                               weakenInst _ (IndexInstantiators l) =
                                   IndexInstantiators (map (\(IndexInstantiator f) -> IndexInstantiator (f . smartFst)) l)
                           in DMap.insertWith (<>) lab (IndexInstantiators [IndexInstantiator smartSnd])
                                              (DMap.map (weakenInst itemtype) mp))
                          (Pair restype expr (Pair itemtype adjexp idxexp))

inlineAvarLabels :: Ord alab
                 => TupR (ADLabelNS alab) fv
                 -> A.ArrayVars aenv' fv
                 -> OpenExp env aenv lab alab args tenv t
                 -> OpenExp env aenv' lab alab' args tenv t
inlineAvarLabels labs vars =
    let mp = buildVarLabMap labs vars
    in inlineAvarLabels' (\lab -> case DMap.lookup lab mp of
                                    Just var -> var
                                    Nothing -> error "inlineAvarLabels: Not all labels instantiated")
  where
    buildVarLabMap :: Ord alab
                   => TupR (ADLabelNS alab) fv
                   -> A.ArrayVars aenv' fv
                   -> DMap (ADLabelNS alab) (A.ArrayVar aenv')
    buildVarLabMap TupRunit TupRunit = mempty
    buildVarLabMap (TupRsingle lab) (TupRsingle var) = DMap.singleton lab var
    buildVarLabMap (TupRpair l1 l2) (TupRpair v1 v2) =
        DMap.unionWithKey (error "Overlapping labels in buildVarLabMap") (buildVarLabMap l1 v1) (buildVarLabMap l2 v2)
    buildVarLabMap _ _ = error "Impossible GADTs"

inlineAvarLabels' :: (forall t'. ADLabelNS alab t' -> A.ArrayVar aenv' t')
                  -> OpenExp env aenv lab alab args tenv t
                  -> OpenExp env aenv' lab alab' args tenv t
inlineAvarLabels' f = \case
    Const ty x -> Const ty x
    PrimApp ty op ex -> PrimApp ty op (inlineAvarLabels' f ex)
    PrimConst c -> PrimConst c
    Pair ty e1 e2 -> Pair ty (inlineAvarLabels' f e1) (inlineAvarLabels' f e2)
    Nil -> Nil
    Cond ty e1 ns2 e2 ns3 e3 -> Cond ty (inlineAvarLabels' f e1) ns2 (inlineAvarLabels' f e2) ns3 (inlineAvarLabels' f e3)
    Shape (Right lab) -> Shape (Left (f lab))
    Shape (Left _) -> error "inlineAvarLabels': Array variable found in labelised expression (Shape)"
    ShapeSize sht e -> ShapeSize sht (inlineAvarLabels' f e)
    Index (Right lab) idxe -> Index (Left (f lab)) (either (Left . inlineAvarLabels' f) Right idxe)
    Index (Left _) _ -> error "inlineAvarLabels': Array variable found in labelised expression (Index)"
    Get ty tidx ex -> Get ty tidx (inlineAvarLabels' f ex)
    Undef ty -> Undef ty
    Let lhs rhs ex -> Let lhs (inlineAvarLabels' f rhs) (inlineAvarLabels' f ex)
    Var v -> Var v
    FreeVar v -> FreeVar v
    Arg ty idx -> Arg ty idx
    Label l -> Label l

-- Produces an expression that can be put under a LHS that binds exactly the
-- 'args' of the original expression.
realiseArgs :: Exp aenv lab alab args tenv res -> A.ELeftHandSide t () args -> OpenExp args aenv lab alab () tenv res
realiseArgs = \expr lhs -> go A.weakenId (A.weakenWithLHS lhs) expr
  where
    go :: args A.:> env' -> env A.:> env' -> OpenExp env aenv lab alab args tenv res -> OpenExp env' aenv lab alab () tenv res
    go argWeaken varWeaken expr = case expr of
        Const ty x -> Const ty x
        PrimApp ty op ex -> PrimApp ty op (go argWeaken varWeaken ex)
        PrimConst c -> PrimConst c
        Pair ty e1 e2 -> Pair ty (go argWeaken varWeaken e1) (go argWeaken varWeaken e2)
        Nil -> Nil
        Cond ty e1 ns2 e2 ns3 e3 -> Cond ty (go argWeaken varWeaken e1) ns2 (go argWeaken varWeaken e2) ns3 (go argWeaken varWeaken e3)
        Shape ref -> Shape ref
        Index ref idxe -> Index ref (either (Left . go argWeaken varWeaken) Right idxe)
        ShapeSize sht e -> ShapeSize sht (go argWeaken varWeaken e)
        Get ty tidx ex -> Get ty tidx (go argWeaken varWeaken ex)
        Undef ty -> Undef ty
        Let lhs rhs ex
          | A.Exists lhs' <- rebuildLHS lhs ->
              Let lhs' (go argWeaken varWeaken rhs)
                  (go (A.weakenWithLHS lhs' A..> argWeaken) (A.sinkWithLHS lhs lhs' varWeaken) ex)
        Var (A.Var ty idx) -> Var (A.Var ty (varWeaken A.>:> idx))
        FreeVar var -> FreeVar var
        Arg ty idx -> Var (A.Var ty (argWeaken A.>:> idx))
        Label _ -> error "realiseArgs: unexpected Label"

-- Map will NOT contain Let or Var. Note that it may contain Label due to Let-bindings.
explode :: Show alab => LabVal NodeLabel ScalarType Int env -> OpenExp env aenv unused alab args tenv t -> IdGen (Exploded aenv Int alab args tenv t)
explode labelenv e =
    trace ("exp explode: exploding " ++ showsExp (ShowEnv (const "L?") show 0 [] []) 9 e "") $
    explode' labelenv e

-- The labelenv in explode contains the node labels in scope. This means that
-- it contains tuple labels; however, a LabVal must contain scalar labels, thus
-- the label numbers are wrapped in scalar DLabel's instead of tuple labels.
-- This works out because any node that enters the environment does so via a
-- Let binding, which forcibly destructures any tuples to scalar-typed values.
-- After explode finishes, this LabVal is thrown away.
explode' :: LabVal NodeLabel ScalarType Int env -> OpenExp env aenv unused alab args tenv t -> IdGen (Exploded aenv Int alab args tenv t)
explode' env = \case
    Const ty x -> do
        lab <- genId (TupRsingle ty)
        return (Exploded lab (DMap.singleton lab (Const ty x)) mempty (Set.singleton (AnyLabel lab)))
    PrimApp ty f e -> do
        Exploded lab1 mp1 argmp subtree <- explode' env e
        lab <- genId ty
        let pruned = PrimApp ty f (Label lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping arg's") mp1 itemmp
        return (Exploded lab mp argmp (Set.insert (AnyLabel lab) subtree))
    PrimConst c -> do
        lab <- genId (TupRsingle (SingleScalarType (A.primConstType c)))
        return (Exploded lab (DMap.singleton lab (PrimConst c)) mempty (Set.singleton (AnyLabel lab)))
    Pair ty e1 e2 -> do
        Exploded lab1 mp1 argmp1 subtree1 <- explode' env e1
        Exploded lab2 mp2 argmp2 subtree2 <- explode' env e2
        lab <- genId ty
        let pruned = Pair ty (Label lab1) (Label lab2)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mp2, itemmp]
            argmp = DMap.unionWithKey (error "explode: Overlapping arg's") argmp1 argmp2
        return (Exploded lab mp argmp (Set.insert (AnyLabel lab) (subtree1 <> subtree2)))
    Nil -> do
        lab <- genId TupRunit
        return (Exploded lab (DMap.singleton lab Nil) mempty (Set.singleton (AnyLabel lab)))
    Cond ty e1 Nothing e2 Nothing e3 -> do
        Exploded lab1 mp1 argmp1 subtree1 <- explode' env e1
        Exploded lab2 mp2 argmp2 subtree2 <- explode' env e2
        Exploded lab3 mp3 argmp3 subtree3 <- explode' env e3
        lab <- genId ty
        -- Note: This is the place where we use those subtrees, namely to tell Cond what its branches are.
        let pruned = Cond ty (Label lab1) (Just subtree2) (Label lab2) (Just subtree3) (Label lab3)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mp2, mp3, itemmp]
            argmp = DMap.unionsWithKey (error "explode: Overlapping arg's") [argmp1, argmp2, argmp3]
        return (Exploded lab mp argmp (Set.insert (AnyLabel lab) (subtree1 <> subtree2 <> subtree3)))
    Cond _ _ _ _ _ _ -> error "explode: Unexpected Cond with embedded node sets"
    Shape (Left avar@(A.Var (ArrayR sht _) _)) -> do
        lab <- genId (shapeType sht)
        return (Exploded lab (DMap.singleton lab (Shape (Left avar))) mempty (Set.singleton (AnyLabel lab)))
    Shape (Right alab@(DLabel (ArrayR sht _) _)) -> do
        lab <- genId (shapeType sht)
        return (Exploded lab (DMap.singleton lab (Shape (Right alab))) mempty (Set.singleton (AnyLabel lab)))
    Index (Left avar@(A.Var (ArrayR _ ty) _)) (Left she) -> do
        Exploded lab1 mp1 argmp1 subtree1 <- explode' env she
        lab <- genId ty
        backuplab <- genId (etypeOf she)
        let pruned = Index (Left avar) (Right (lab1, backuplab))
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (Exploded lab mp argmp1 (Set.insert (AnyLabel lab) subtree1))
    Index (Right alab@(DLabel (ArrayR _ ty) _)) (Left she) -> do
        Exploded lab1 mp1 argmp1 subtree1 <- explode' env she
        lab <- genId ty
        backuplab <- genId (etypeOf she)
        let pruned = Index (Right alab) (Right (lab1, backuplab))
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (Exploded lab mp argmp1 (Set.insert (AnyLabel lab) subtree1))
    Index _ (Right _) -> error "explode: Unexpected exp-labelised Index"
    ShapeSize sht e -> do
        Exploded lab1 mp1 argmp1 subtree1 <- explode' env e
        lab <- genId (TupRsingle scalarType)
        let pruned = ShapeSize sht (Label lab1)
        let itemmp = DMap.singleton lab pruned
            mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 itemmp
        return (Exploded lab mp argmp1 (Set.insert (AnyLabel lab) subtree1))
    Undef ty -> do
        lab <- genId (TupRsingle ty)
        return (Exploded lab (DMap.singleton lab (Undef ty)) mempty (Set.singleton (AnyLabel lab)))
    Let lhs rhs body -> do
        Exploded lab1 mp1 argmp1 subtree1 <- explode' env rhs
        (_, labs) <- genIds (etypeOf rhs)
        let (env', mpLHS) = lpushLHS_Get lhs labs env (Label lab1)
        Exploded lab2 mp2 argmp2 subtree2 <- explode' env' body
        let mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mpLHS, mp2]
            argmp = DMap.unionWithKey (error "explode: Overlapping arg's") argmp1 argmp2
        return (Exploded lab2 mp argmp (subtree1 <> subtree2))
    Var (A.Var _ idx) -> do
        return (Exploded (tupleLabel (prjL idx env)) mempty mempty mempty)
    FreeVar var@(A.Var ty _) -> do
        lab <- genId (TupRsingle ty)
        return (Exploded lab (DMap.singleton lab (FreeVar var)) mempty (Set.singleton (AnyLabel lab)))
    Arg ty idx -> do
        lab <- genId (TupRsingle ty)
        return (Exploded lab (DMap.singleton lab (Arg ty idx)) (DMap.singleton idx lab) (Set.singleton (AnyLabel lab)))
    Get _ _ _ -> error "explode: Unexpected Get"
    Label _ -> error "explode: Unexpected Label"
  where
    lpushLHS_Get :: A.ELeftHandSide t env env' -> TupR (EDLabelNS Int) t -> LabVal NodeLabel ScalarType Int env -> Exp aenv Int alab args tenv t -> (LabVal NodeLabel ScalarType Int env', DMap (EDLabelN Int) (Exp aenv Int alab args tenv))
    lpushLHS_Get lhs labs labelenv rhs = case (lhs, labs) of
        (A.LeftHandSidePair lhs1 lhs2, TupRpair labs1 labs2) ->
            let (labelenv1, mp1) = lpushLHS_Get lhs1 labs1 labelenv (smartFst rhs)
                (labelenv2, mp2) = lpushLHS_Get lhs2 labs2 labelenv1 (smartSnd rhs)
            in (labelenv2, DMap.unionWithKey (error "lpushLHS_Get: Overlapping id's") mp1 mp2)
        (A.LeftHandSideSingle _, TupRsingle lab) -> (LPush labelenv lab, DMap.singleton (tupleLabel lab) rhs)
        (A.LeftHandSideWildcard _, _) -> (labelenv, mempty)
        _ -> error "lpushLHS_Get: impossible GADTs"

-- TODO: remove Show constraint from alab
primaldual :: Show alab
           => Exploded aenv Int alab args tenv Float
           -> (forall env. EContext Int env -> IdGen (OpenExp env aenv (PDExp Int) alab args tenv t))
           -> IdGen (Exp aenv (PDExp Int) alab args tenv t)
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
data PrimalResult env aenv alab args tenv =
    forall env'.
        PrimalResult (EContext Int env')
                     (forall res. OpenExp env' aenv (PDExp Int) alab args tenv res
                               -> OpenExp env aenv (PDExp Int) alab args tenv res)

-- Resulting computation will only use P, never D
primal :: Exploded aenv Int alab args tenv res
       -> IdGen (PrimalResult () aenv alab args tenv)
primal (Exploded { exEndLabel = endlab, exNodeMap = nodemap }) = primal' nodemap endlab (Context LEmpty mempty)

primalAll :: DMap (EDLabelN Int) (Exp aenv Int alab args tenv)
          -> [EAnyLabelN Int]
          -> EContext Int env
          -> IdGen (PrimalResult env aenv alab args tenv)
primalAll _ [] ctx = return (PrimalResult ctx id)
primalAll nodemap (AnyLabel lab : labs) ctx = do
    PrimalResult ctx1 builder1 <- primal' nodemap lab ctx
    PrimalResult ctx2 builder2 <- primalAll nodemap labs ctx1
    return (PrimalResult ctx2 (builder1 . builder2))

primal' :: DMap (EDLabelN Int) (Exp aenv Int alab args tenv)
        -> EDLabelN Int t
        -> EContext Int env
        -> IdGen (PrimalResult env aenv alab args tenv)
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

          PrimConst c -> do
              let TupRsingle ty = labelType lbl
              lblS <- genSingleId ty
              return $ PrimalResult (Context (LPush labelenv lblS) (DMap.insert (fmapLabel P lbl) (TupRsingle lblS) bindmap))
                                    (Let (A.LeftHandSideSingle ty) (PrimConst c))

          FreeVar var@(A.Var ty _) -> do
              lblS <- genSingleId ty
              return $ PrimalResult (Context (LPush labelenv lblS) (DMap.insert (fmapLabel P lbl) (TupRsingle lblS) bindmap))
                                    (Let (A.LeftHandSideSingle ty) (FreeVar var))

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
                      (Exists lhs, labs) <- genSingleIds restype
                      return $ PrimalResult (Context (lpushLabTup labelenv' lhs labs) (DMap.insert (fmapLabel P lbl) labs bindmap'))
                                            (f1 . Let lhs (PrimApp restype oper (evars vars)))
                  Nothing ->
                      error "primal: App argument did not compute argument"

          Cond restype (Label condlab) (Just thenset) (Label thenlab) (Just elseset) (Label elselab) -> do
              -- First ensure that all graph parts referenced by the conditional's branches have
              -- been computed already. This prevents including parts of the graph in the branches
              -- that were originally actually outside the Cond.
              let thenBound = graphSubsetBoundary nodemap thenset
                  elseBound = graphSubsetBoundary nodemap elseset
              PrimalResult ctxBound1 fBound1 <- primalAll nodemap (Set.toList thenBound) (Context labelenv bindmap)
              PrimalResult ctxBound2 fBound2 <- primalAll nodemap (Set.toList elseBound) ctxBound1

              PrimalResult ctxCond@(Context labelenv'Cond bindmap'Cond) fCond <- primal' nodemap condlab ctxBound2
              PrimalResult ctxThen@(Context labelenv'Then bindmap'Then) f2Then <- primal' nodemap thenlab ctxCond
              PrimalResult ctxElse@(Context labelenv'Else bindmap'Else) f2Else <- primal' nodemap elselab ctxCond
              let condlabs = bindmap'Cond `dmapFind` fmapLabel P condlab
                  thenlabs = bindmap'Then `dmapFind` fmapLabel P thenlab
                  elselabs = bindmap'Else `dmapFind` fmapLabel P elselab
              case (elabValFinds labelenv'Cond condlabs
                   ,elabValFinds labelenv'Then thenlabs
                   ,elabValFinds labelenv'Else elselabs) of
                (Just condvars, Just thenvars, Just elsevars)
                  | EnvCapture tmpvarsThen (EnvInstantiator instThen) <- captureEnvironmentSlice ctxCond ctxThen
                  , EnvCapture tmpvarsElse (EnvInstantiator instElse) <- captureEnvironmentSlice ctxCond ctxElse
                  , let tuptyThen = A.varsType tmpvarsThen
                        tuptyElse = A.varsType tmpvarsElse
                  , LetBoundExpE lhsResult _ <- elhsCopy restype
                  , LetBoundExpE lhsThen lhsVarsThen <- elhsCopy tuptyThen
                  , LetBoundExpE lhsElse lhsVarsElse <- elhsCopy tuptyElse
                  -> do
                    (_, labs) <- genSingleIds restype
                    (_, tmplabsThen) <- genSingleIds tuptyThen
                    (_, tmplabsElse) <- genSingleIds tuptyElse
                    let bodyThen = f2Then (smartPair (evars thenvars) (smartPair (evars tmpvarsThen) (undefsOfType tuptyElse)))
                        bodyElse = f2Else (smartPair (evars elsevars) (smartPair (undefsOfType tuptyThen) (evars tmpvarsElse)))
                        labelenv' = lpushLabTup (lpushLabTup (lpushLabTup labelenv'Cond lhsResult labs) lhsThen tmplabsThen) lhsElse tmplabsElse
                        bindmap'1 = instThen (Context labelenv' bindmap'Cond) (weakenVars (A.weakenWithLHS lhsElse) lhsVarsThen)
                        bindmap'2 = instElse (Context labelenv' bindmap'1) lhsVarsElse
                    return $ PrimalResult (Context labelenv' (DMap.insert (fmapLabel P lbl) labs bindmap'2))
                                          (fBound1 . fBound2 .
                                           fCond . Let (A.LeftHandSidePair lhsResult (A.LeftHandSidePair lhsThen lhsElse))
                                                       (Cond (TupRpair restype (TupRpair tuptyThen tuptyElse)) (evars condvars) Nothing bodyThen Nothing bodyElse))
                _ ->
                    error "primal: Cond arguments did not compute arguments"
            where
              -- TODO: This function is a huge hack since it generates -1 for all Int-valued entries, and 0 for all others.
              -- Why do we do that? We need all right arguments of an Index node to get -1 for the
              -- whole shape in order for the array-index-induced Permute's to not do anything with
              -- non-executed Index nodes. The easiest way to do that, which doesn't even involve
              -- looking at what node we're dealing with, is to set _all_ Int-typed temps to -1.
              -- Thus we do so.
              -- TODO: We'd like to generate Undef for the non-Int entries, but currently the dual phase always executes both branches, meaning that arithmetic would be performed with Undef values, which is (probably) unsafe.
              undefsOfType :: TypeR t -> OpenExp env aenv lab alab args tenv t
              undefsOfType TupRunit = Nil
              undefsOfType (TupRsingle (SingleScalarType (NumSingleType (IntegralNumType TypeInt)))) = Const scalarType (-1)
              undefsOfType (TupRsingle ty) = zeroForType ty
              undefsOfType (TupRpair t1 t2) = smartPair (undefsOfType t1) (undefsOfType t2)

          Shape ref -> do
              (Exists lhs, labs) <- genSingleIds (labelType lbl)
              return $ PrimalResult (Context (lpushLabTup labelenv lhs labs) (DMap.insert (fmapLabel P lbl) labs bindmap))
                                    (Let lhs (Shape ref))

          Index ref (Right (arglab, backuplab)) -> do
              PrimalResult (Context labelenv' bindmap') f1 <- primal' nodemap arglab (Context labelenv bindmap)
              let arglabs = bindmap' `dmapFind` fmapLabel P arglab
              -- We have to take the argument and first make a copy at
              -- 'backuplab', and then use that copy instead of the value from
              -- the argument. This is to ensure a copy is available directly
              -- adjacent to the Index node; see Index in Exp.hs.
              case (elabValFinds labelenv' arglabs, elhsCopy (labelType backuplab)) of
                  (Just vars, LetBoundExpE lhs2 vars2) -> do
                      (Exists lhs, labs) <- genSingleIds (labelType lbl)
                      (_, labs2) <- genSingleIds (labelType backuplab)
                      let labelenv'' = lpushLabTup (lpushLabTup labelenv' lhs2 labs2) lhs labs
                          bindmap'' = DMap.insert (fmapLabel P lbl) labs $
                                      DMap.insert (fmapLabel P backuplab) labs2 $
                                      bindmap'
                      return $ PrimalResult (Context labelenv'' (DMap.insert (fmapLabel P lbl) labs bindmap''))
                                            (f1 . Let lhs2 (evars vars) . Let lhs (Index ref (Left (evars vars2))))
                  _ -> error "primal: Index arguments did not compute arguments"

          ShapeSize sht (Label arglab) -> do
              PrimalResult (Context labelenv' bindmap') f1 <- primal' nodemap arglab (Context labelenv bindmap)
              let arglabs = bindmap' `dmapFind` fmapLabel P arglab
              case elabValFinds labelenv' arglabs of
                  Just vars -> do
                      (Exists lhs, labs) <- genSingleIds (TupRsingle scalarType)
                      return $ PrimalResult (Context (lpushLabTup labelenv' lhs labs) (DMap.insert (fmapLabel P lbl) labs bindmap'))
                                            (f1 . Let lhs (ShapeSize sht (evars vars)))
                  _ -> error "primal: ShapeSize arguments did not compute arguments"

          Get _ path (Label arglab) -> do
              PrimalResult (Context labelenv' bindmap') f1 <- primal' nodemap arglab (Context labelenv bindmap)
              let pickedlabs = pickTupR path (bindmap' `dmapFind` fmapLabel P arglab)
              -- Note: We don't re-bind the picked tuple into a new let binding
              -- with fresh labels here; we just point the tuple label for this
              -- Get expression node to the pre-existing scalar labels.
              return $ PrimalResult (Context labelenv' (DMap.insert (fmapLabel P lbl) pickedlabs bindmap')) f1

          Undef ty -> do
              labS <- genSingleId ty
              return $ PrimalResult (Context (LPush labelenv labS) (DMap.insert (fmapLabel P lbl) (TupRsingle labS) bindmap))
                                    (Let (A.LeftHandSideSingle ty) (Undef ty))

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
newtype AdjList aenv lab alab args tenv t = AdjList (forall env. EContext lab env -> [OpenExp env aenv (PDExp lab) alab args tenv t])

data DualResult env aenv alab args tenv =
    forall env'.
        DualResult (EContext Int env')
                   (DMap (EDLabelN (PDExp Int)) (AdjList aenv Int alab args tenv))  -- contribmap
                   (forall res. OpenExp env' aenv (PDExp Int) alab args tenv res
                             -> OpenExp env aenv (PDExp Int) alab args tenv res)

dual :: Show alab
     => Exploded aenv Int alab args tenv t
     -> (forall env'. EContext Int env' -> OpenExp env' aenv (PDExp Int) alab args tenv t)
     -> EContext Int env
     -> IdGen (DualResult env aenv alab args tenv)
dual (Exploded { exEndLabel = endlab, exNodeMap = nodemap, exArgMap = argmap }) endadjoint context =
    trace ("\nexp labelorder: " ++ show [labelLabel l | AnyLabel l <- labelorder]) $
    let contribmap = DMap.singleton (fmapLabel D endlab) (AdjList (pure . endadjoint))
    in dual's nodemap labelorder context contribmap
  where
    argLabels :: Set (EAnyLabelN Int)
    argLabels = Set.fromList [AnyLabel lab | _ :=> lab <- DMap.toList argmap]

    parentsOf :: EAnyLabelN Int -> [EAnyLabelN Int]
    parentsOf (AnyLabel lbl) = expLabelParents (nodemap `dmapFind` lbl)

    -- Add the labels corresponding to argument nodes if they're not already
    -- found by the floodfill. If an argument is unused, we still want to visit
    -- it (if only to store 0 for the adjoint because there are no
    -- contributions).
    alllabels :: [EAnyLabelN Int]
    alllabels = Set.toList $ floodfill (AnyLabel endlab) parentsOf mempty <> argLabels

    parentmap :: Map Int [EAnyLabelN Int]
    parentmap = Map.fromList [(labelLabel numlbl, parentsOf l)
                             | l@(AnyLabel numlbl) <- alllabels]

    labelorder :: [EAnyLabelN Int]
    labelorder = topsort' (\(AnyLabel l) -> labelLabel l)
                          alllabels
                          (\(AnyLabel l) -> parentmap Map.! labelLabel l)

dual's :: Show alab
       => DMap (EDLabelN Int) (Exp aenv Int alab args tenv)
       -> [EAnyLabelN Int]
       -> EContext Int env
       -> DMap (EDLabelN (PDExp Int)) (AdjList aenv Int alab args tenv)
       -> IdGen (DualResult env aenv alab args tenv)
dual's _ [] context contribmap = return $ DualResult context contribmap id
dual's nodemap (AnyLabel lab : labs) context contribmap = do
    DualResult context1 contribmap1 f1 <- dual' nodemap lab context contribmap
    DualResult context2 contribmap2 f2 <- dual's nodemap labs context1 contribmap1
    return $ DualResult context2 contribmap2 (f1 . f2)

dual' :: Show alab
      => DMap (EDLabelN Int) (Exp aenv Int alab args tenv)
      -> EDLabelN Int t
      -> EContext Int env
      -> DMap (EDLabelN (PDExp Int)) (AdjList aenv Int alab args tenv)
      -> IdGen (DualResult env aenv alab args tenv)
dual' nodemap lbl (Context labelenv bindmap) contribmap =
    -- trace ("dual': computing " ++ show lbl) $
    case nodemap `dmapFind` lbl of
      -- We aren't interested in the adjoint of constant nodes -- seeing as
      -- they don't have any parents to contribute to, and their own adjoints
      -- aren't used anywhere.
      Const _ _ -> return $ DualResult (Context labelenv bindmap) contribmap id
      PrimConst _ -> return $ DualResult (Context labelenv bindmap) contribmap id
      Undef _ -> return $ DualResult (Context labelenv bindmap) contribmap id

      -- We also aren't interested in the adjoint of free variables.
      FreeVar _ ->
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

      PrimApp _ (A.PrimSub restypeN) (Label arglab) -> do
          let restypeS = SingleScalarType (NumSingleType restypeN)
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil $ \(TupRsingle adjvar) _ ->
                                    smartPair (Var adjvar) (smartNeg restypeN (Var adjvar))]
                                contribmap
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap'
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      PrimApp _ (A.PrimMul restypeN) (Label arglab) -> do
          let restypeS = SingleScalarType (NumSingleType restypeN)
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) $ \(TupRsingle adjvar) (TupRpair (TupRsingle argvar1) (TupRsingle argvar2) :@ TLNil) ->
                                    smartPair
                                         (smartMul restypeN (Var adjvar) (Var argvar2))
                                         (smartMul restypeN (Var adjvar) (Var argvar1))]
                                contribmap
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap'
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      PrimApp _ (A.PrimFDiv restypeF) (Label arglab) -> do
          let restypeN = FloatingNumType restypeF
              restypeS = SingleScalarType (NumSingleType restypeN)
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) $ \(TupRsingle adjvar) (TupRpair (TupRsingle argvar1) (TupRsingle argvar2) :@ TLNil) ->
                                    smartPair
                                         (smartMul restypeN (Var adjvar) (smartRecip restypeF (Var argvar2)))
                                         (smartMul restypeN (Var adjvar)
                                              (smartFDiv restypeF (smartNeg restypeN (Var argvar1))
                                                                  (smartMul restypeN (Var argvar2) (Var argvar2))))]
                                contribmap
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap'
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      PrimApp _ (A.PrimMax restypeSg) (Label arglab) -> do
          let restypeS = SingleScalarType restypeSg
              restypeT = TupRsingle restypeS
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) $ \(TupRsingle adjvar) (TupRpair (TupRsingle argvar1) (TupRsingle argvar2) :@ TLNil) ->
                                    Cond (TupRpair restypeT restypeT)
                                         (smartGt restypeSg (Var argvar1) (Var argvar2))
                                         Nothing
                                         (smartPair (Var adjvar) (zeroForType restypeSg))
                                         Nothing
                                         (smartPair (zeroForType restypeSg) (Var adjvar))]
                                contribmap
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap'
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      PrimApp _ (A.PrimNeg restypeN) (Label arglab) -> do
          let restypeS = SingleScalarType (NumSingleType restypeN)
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                -- Note: derivative of -x is -1, so we just return -adjoint
                                [Contribution arglab TLNil $ \(TupRsingle adjvar) _ ->
                                    smartNeg restypeN (Var adjvar)]
                                contribmap
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap'
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      PrimApp _ (A.PrimLog restypeF) (Label arglab) -> do
          let restypeS = SingleScalarType (NumSingleType (FloatingNumType restypeF))
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) $ \(TupRsingle adjvar) (TupRsingle argvar :@ TLNil) ->
                                    -- dE/dx = dE/d(log x) * d(log x)/dx = adjoint * 1/x = adjoint / x
                                    smartFDiv restypeF (Var adjvar) (Var argvar)]
                                contribmap
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap'
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      PrimApp _ (A.PrimSqrt restypeF) (Label arglab) -> do
          let restypeN = FloatingNumType restypeF
              restypeS = SingleScalarType (NumSingleType restypeN)
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (lbl :@ TLNil) $ \(TupRsingle adjvar) (TupRsingle primvar :@ TLNil) ->
                                    -- dE/dx = dE/d(sqrt x) * d(sqrt x)/dx = adjoint * 1/(2 * sqrt x) = adjoint / (2 * sqrt x)
                                    -- where 'sqrt x' is just the primal value
                                    smartFDiv restypeF (Var adjvar) (smartMul restypeN (zeroForType' 2 restypeS) (Var primvar))]
                                contribmap
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap'
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      PrimApp _ (A.PrimExpFloating restypeF) (Label arglab) -> do
          let restypeS = SingleScalarType (NumSingleType (FloatingNumType restypeF))
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                -- Note: derivative of e^x is e^x, so we just copy the primal value over
                                [Contribution arglab (lbl :@ TLNil) $ \(TupRsingle adjvar) (TupRsingle primvar :@ TLNil) ->
                                    smartMul (FloatingNumType restypeF) (Var adjvar) (Var primvar)]
                                contribmap
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap'
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      PrimApp _ (A.PrimTanh restypeF) (Label arglab) -> do
          let restypeS = SingleScalarType (NumSingleType (FloatingNumType restypeF))
              restypeN = FloatingNumType restypeF
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                -- Note: derivative of tanh(x) is 1 - tanh(x)^2, so use the primal value
                                [Contribution arglab (lbl :@ TLNil) $ \(TupRsingle adjvar) (TupRsingle primvar :@ TLNil) ->
                                    smartMul restypeN (Var adjvar)
                                                      (smartSub restypeN (zeroForType' 1 restypeF)
                                                                         (smartMul restypeN (Var primvar) (Var primvar)))]
                                contribmap
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap'
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      PrimApp restype (A.PrimSin restypeF) (Label arglab) -> do
          let restypeS = SingleScalarType (NumSingleType (FloatingNumType restypeF))
              restypeN = FloatingNumType restypeF
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) $ \(TupRsingle adjvar) (TupRsingle primvar :@ TLNil) ->
                                    smartMul restypeN (Var adjvar)
                                                      (PrimApp restype (A.PrimCos restypeF) (Var primvar))]
                                contribmap
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap'
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      PrimApp restype (A.PrimCos restypeF) (Label arglab) -> do
          let restypeS = SingleScalarType (NumSingleType (FloatingNumType restypeF))
              restypeN = FloatingNumType restypeF
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) $ \(TupRsingle adjvar) (TupRsingle primvar :@ TLNil) ->
                                    smartMul restypeN (Var adjvar)
                                                      (PrimApp restype (A.PrimNeg restypeN)
                                                          (PrimApp restype (A.PrimSin restypeF) (Var primvar)))]
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

      -- Argument is an integral type, which takes no contributions
      PrimApp _ (A.PrimFromIntegral _ restypeN) _ -> do
          let restypeS = SingleScalarType (NumSingleType restypeN)
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

      -- No adjoint because the result is an integral type, thus also no
      -- contributions to make
      Shape _ ->
          return $ DualResult (Context labelenv bindmap) contribmap id

      -- No adjoint because the result is an integral type, thus also no
      -- contributions to make
      ShapeSize _ _ ->
          return $ DualResult (Context labelenv bindmap) contribmap id

      -- Argument (the index) is an integral type, which takes no
      -- contributions. Note that more needs to be done in splitLambdaAD with
      -- lambdas that contain Index nodes, but here all is still simple.
      Index _ _ -> do
          let TupRsingle restypeS = labelType lbl
              adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
          lblS <- genSingleId restypeS
          return $ DualResult (Context (LPush labelenv lblS)
                                       (DMap.insert (fmapLabel D lbl) (TupRsingle lblS) bindmap))
                              contribmap
                              (Let (A.LeftHandSideSingle restypeS) adjoint)

      Cond restype (Label condlab) _ (Label thenlab) _ (Label elselab) -> do
          let adjoint = collectAdjoint contribmap lbl (Context labelenv bindmap)
              contribmap' = updateContribmap lbl
                                [Contribution thenlab (condlab :@ TLNil) $ \adjvars (TupRsingle condvar :@ TLNil) ->
                                    Cond restype (Var condvar) Nothing (evars adjvars) Nothing (zeroForType restype)
                                ,Contribution elselab (condlab :@ TLNil) $ \adjvars (TupRsingle condvar :@ TLNil) ->
                                    Cond restype (Var condvar) Nothing (zeroForType restype) Nothing (evars adjvars)]
                                contribmap
          (Exists lhs, labs) <- genSingleIds restype
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
          (Exists lhs, labs) <- genSingleIds restype
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
          (Exists lhs, labs) <- genSingleIds restype
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
          (Exists lhs, labs) <- genSingleIds (labelType arglab)
          return $ DualResult (Context (lpushLabTup labelenv lhs labs)
                                       (DMap.insert (fmapLabel D lbl) labs bindmap))
                              contribmap'
                              (Let lhs adjoint)

      expr -> error ("\n!! " ++ show expr)

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

data Contribution node aenv alab args tenv =
    forall parents t.
        Contribution (EDLabelN Int t)  -- to which label are we contributing an adjoint
                     (TypedList (EDLabelN Int) parents)  -- labels you need the primary value of
                     (forall env. A.ExpVars env node                  -- current node's adjoint
                               -> TypedList (A.ExpVars env) parents   -- requested primal values
                               -> OpenExp env aenv (PDExp Int) alab args tenv t)   -- contribution

-- Note: Before this code was extracted into a separate function, its
-- functionality was inlined in the branches of dual'. Because of that, the
-- branches needed explicit type signatures (and thus be separate functions),
-- since the definition of the contribution function had too intricate type
-- variables for GHC to figure out.
-- Now that this is a separate function, though, the type signature here (and
-- the typing of Contribution) removes the need of the branches of dual' to
-- have a separate type signature, significantly simplifying the structure of
-- the code.
updateContribmap :: EDLabelN Int node
                 -> [Contribution node aenv alab args tenv]
                 -> DMap (EDLabelN (PDExp Int)) (AdjList aenv Int alab args tenv)
                 -> DMap (EDLabelN (PDExp Int)) (AdjList aenv Int alab args tenv)
updateContribmap lbl =
    flip . foldr $ \(Contribution lab parentlabs gen) ->
        addContribution (fmapLabel D lab) $ \(Context labelenv bindmap) ->
            let currentlabs = bindmap `dmapFind` fmapLabel D lbl
            in case (elabValFinds labelenv currentlabs, findAll (Context labelenv bindmap) parentlabs) of
                (Just adjvars, parvars) -> gen adjvars parvars
                _ -> error $ "updateContribmap: node D " ++ show lbl ++ " was not computed"
  where
    findAll :: EContext Int env -> TypedList (EDLabelN Int) parents -> TypedList (A.ExpVars env) parents
    findAll (Context labelenv bindmap) =
        tlmap $ \lab ->
            let labs = bindmap `dmapFind` fmapLabel P lab
            in fromMaybe (error $ "updateContribmap: arg P " ++ show lab ++ " was not computed; labs: " ++ showTupR show labs ++ "; labelenv: " ++ showLabelenv labelenv ++ "; bindmap: " ++ showBindmap bindmap) (elabValFinds labelenv labs)

addContribution :: Ord lab
                => EDLabelN (PDExp lab) t
                -> (forall env. EContext lab env -> OpenExp env aenv (PDExp lab) alab args tenv t)
                -> DMap (EDLabelN (PDExp lab)) (AdjList aenv lab alab args tenv)
                -> DMap (EDLabelN (PDExp lab)) (AdjList aenv lab alab args tenv)
addContribution lbl contribution =
    DMap.insertWith (\(AdjList f1) (AdjList f2) -> AdjList (\context -> f1 context ++ f2 context))
                    lbl
                    (AdjList (pure . contribution))

collectAdjoint :: DMap (EDLabelN (PDExp Int)) (AdjList aenv Int alab args tenv)
               -> EDLabelN Int item
               -> EContext Int env
               -> OpenExp env aenv (PDExp Int) alab args tenv item
collectAdjoint contribmap lbl (Context labelenv bindmap) =
    case DMap.lookup (fmapLabel D lbl) contribmap of
        Just (AdjList listgen) -> expSum (labelType lbl) (listgen (Context labelenv bindmap))
        Nothing -> expSum (labelType lbl) []  -- if there are no contributions, well, the adjoint is an empty sum (i.e. zero)

oneHotTup :: TypeR t -> TupleIdx t t' -> OpenExp env aenv lab alab args tenv t' -> OpenExp env aenv lab alab args tenv t
oneHotTup _ TIHere ex = ex
oneHotTup ty@(TupRpair ty1 ty2) (TILeft ti) ex = Pair ty (oneHotTup ty1 ti ex) (zeroForType ty2)
oneHotTup ty@(TupRpair ty1 ty2) (TIRight ti) ex = Pair ty (zeroForType ty1) (oneHotTup ty2 ti ex)
oneHotTup _ _ _ = error "oneHotTup: impossible GADTs"

-- Errors if any parents are not Label nodes, or if called on a Let or Var node.
expLabelParents :: OpenExp env aenv lab alab args tenv t -> [EAnyLabelN lab]
expLabelParents = \case
    Const _ _ -> []
    PrimApp _ _ e -> fromLabel e
    PrimConst _ -> []
    Pair _ e1 e2 -> fromLabel e1 ++ fromLabel e2
    Nil -> []
    Cond _ e1 _ e2 _ e3 -> fromLabel e1 ++ fromLabel e2 ++ fromLabel e3
    Shape _ -> []
    Index _ (Left e) -> fromLabel e
    Index _ (Right (lab, _)) -> [AnyLabel lab]
    ShapeSize _ e -> fromLabel e
    Get _ _ e -> fromLabel e
    Undef _ -> []
    FreeVar _ -> []
    Arg _ _ -> []
    Label lab -> [AnyLabel lab]
    Let _ _ _ -> unimplemented "Let"
    Var _ -> unimplemented "Var"
  where
    unimplemented name =
        error ("expLabelParents: Unimplemented for " ++ name ++ ", semantics unclear")

    fromLabel (Label lab) = [AnyLabel lab]
    fromLabel _ = error "expLabelParents: Parent is not a label"

graphSubsetBoundary :: Ord lab
                    => DMap (EDLabelN lab) (OpenExp env aenv lab alab args tenv)
                    -> Set (EAnyLabelN lab)
                    -> Set (EAnyLabelN lab)
graphSubsetBoundary nodemap interior =
    let expanded = Set.fromList (concat [expLabelParents (nodemap `dmapFind` lab)
                                        | AnyLabel lab <- Set.toList interior])
    in expanded Set.\\ interior

dmapFind :: (HasCallStack, GCompare f) => DMap f g -> f a -> g a
dmapFind mp elt = case DMap.lookup elt mp of
                    Just res -> res
                    Nothing -> error "dmapFind: not found"
