{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Data.Array.Accelerate.Trafo.AD.ADDep (
  reverseAD, ReverseADRes(..)
) where

import Control.Monad.State.Strict
import Data.List (intercalate, sortOn)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Map (DMap)
import Data.Dependent.Sum
import Data.Type.Equality

import Debug.Trace

import qualified Data.Array.Accelerate.AST as A
import qualified Data.Array.Accelerate.AST.Environment as A
import qualified Data.Array.Accelerate.AST.Idx as A
import qualified Data.Array.Accelerate.AST.LeftHandSide as A
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.AD.Algorithms
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.TupleZip
import Data.Array.Accelerate.Trafo.AD.Sink
import Data.Array.Accelerate.Trafo.Var (declareVars, DeclareVars(..))


newtype IdGen a = IdGen (State Int a)
  deriving (Functor, Applicative, Monad, MonadState Int)

evalIdGen :: IdGen a -> a
evalIdGen (IdGen s) = evalState s 1

genScalarId :: ScalarType t -> IdGen (DLabel Int t)
genScalarId ty = state (\s -> (DLabel ty s, succ s))

genId :: TypeR t -> IdGen (DLabels Int t)
genId TupRunit = return DLNil
genId (TupRsingle ty) = DLScalar <$> genScalarId ty
genId (TupRpair t1 t2) = DLPair <$> genId t1 <*> genId t2


type Exploded lab args res = (DLabels lab res, DMap (DLabel lab) (Exp lab args), DMap (A.Idx args) (DLabel lab))

showExploded :: (Ord lab, Show lab) => Exploded lab args t -> String
showExploded (endlab, nodemap, argmap) =
  "(" ++ showDLabels show endlab ++ ", " ++ showNodemap nodemap ++ ", " ++ showArgmap argmap ++ ")"

showNodemap :: (Ord lab, Show lab) => DMap (DLabel lab) (Exp lab args) -> String
showNodemap nodemap =
    let tups = sortOn fst [(lab, (showDLabel dlab, show expr)) | dlab@(DLabel _ lab) :=> expr <- DMap.assocs nodemap]
        s = intercalate ", " ["(" ++ dlabshow ++ ") :=> " ++ exprshow
                             | (_, (dlabshow, exprshow)) <- tups]
    in "[" ++ s ++ "]"

showArgmap :: Show lab => DMap (A.Idx args) (DLabel lab) -> String
showArgmap argmap =
    let s = intercalate ", " ['A' : show (A.idxToInt argidx) ++ " :=> " ++ showDLabel dlab
                             | argidx :=> dlab <- DMap.assocs argmap]
    in "[" ++ s ++ "]"

showDLabel :: Show lab => DLabel lab t -> String
showDLabel (DLabel ty lab) = "L" ++ show lab ++ " :: " ++ show ty

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
generaliseArgs :: OpenExp env lab args t -> OpenExp env lab args' t
generaliseArgs (Const ty x) = Const ty x
generaliseArgs (PrimApp ty op ex) = PrimApp ty op (generaliseArgs ex)
generaliseArgs (Pair ty e1 e2) = Pair ty (generaliseArgs e1) (generaliseArgs e2)
generaliseArgs Nil = Nil
generaliseArgs (Get ty path ex) = Get ty path (generaliseArgs ex)
generaliseArgs (Let lhs rhs ex) = Let lhs (generaliseArgs rhs) (generaliseArgs ex)
generaliseArgs (Var v) = Var v
generaliseArgs (Arg _ _) = error "generaliseArgs: Arg found"
generaliseArgs (Label labs) = Label labs

data ReverseADRes t = forall env. ReverseADRes (A.ELeftHandSide t () env) (OpenExp env (PD Int) () t)

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
reverseAD :: A.ELeftHandSide t () env -> OpenExp env unused () Float -> ReverseADRes t
reverseAD paramlhs expr
  | ExpandLHS paramlhs' paramWeaken <- expandLHS paramlhs
  , DeclareVars paramlhs'2 _ varsgen <- declareVars (A.lhsToTupR paramlhs)
  , Refl <- sameLHSsameEnv paramlhs' paramlhs'2 =
      let argsRHS = varsToArgs (varsgen A.weakenId)
          closedExpr = Let paramlhs' argsRHS (generaliseArgs (sinkExp paramWeaken expr))
          exploded@(_, _, argLabelMap) = explode LEmpty closedExpr
          transformedExp =
              primaldual exploded $ \labelenv ->
                  -- 'argsRHS' is an expression of type 't', and is a simple tuple expression
                  -- containing only Arg (and Pair/Nil) nodes. Since 't' is also exactly the
                  -- type of the gradient that we must produce here, we can transform
                  -- 'argsRHS' to our wishes.
                  -- These Arg nodes we can look up in argLabelMap to produce a DLabel, which
                  -- can on their turn be looked up in 'labelenv' using 'labValFind'. The
                  -- lookup produces an Idx, which, put in a Var, should replace the Arg in
                  -- 'argsRHS'.
                  trace ("\nlabval in core: " ++ show (labValToList labelenv)) $
                  produceGradient argLabelMap labelenv argsRHS
      in
          trace ("exploded: " ++ showExploded exploded) $
          trace ("AD result: " ++ show transformedExp) $
          ReverseADRes paramlhs' (realiseArgs transformedExp paramlhs')
  where
    varsToArgs :: A.ExpVars env t -> OpenExp env' lab env t
    varsToArgs TupRunit = Nil
    varsToArgs (TupRsingle (A.Var ty idx)) = Arg ty idx
    varsToArgs (TupRpair vars1 vars2) =
      let ex1 = varsToArgs vars1
          ex2 = varsToArgs vars2
      in Pair (TupRpair (typeOf ex1) (typeOf ex2)) ex1 ex2

    produceGradient :: DMap (Idx args) (DLabel Int)
                    -> LabVal (PD Int) env
                    -> OpenExp () unused args t
                    -> OpenExp env (PD Int) args' t
    produceGradient argLabelMap labelenv argstup = case argstup of
        Nil -> Nil
        Pair ty e1 e2 -> Pair ty (produceGradient argLabelMap labelenv e1)
                                 (produceGradient argLabelMap labelenv e2)
        Arg ty idx
          | Just lab <- DMap.lookup idx argLabelMap
          , Just idx' <- labValFind labelenv (fmapLabel D lab)
              -> Var (A.Var ty idx')
          | otherwise
              -> error $ "produceGradient: Adjoint of Arg (" ++ show ty ++ ") " ++
                            'A' : show (A.idxToInt idx) ++ " not computed"
        _ -> error "produceGradient: what?"

realiseArgs :: OpenExp () lab args t -> A.ELeftHandSide t () args -> OpenExp args lab () t
realiseArgs = \expr lhs -> go A.weakenId (A.weakenWithLHS lhs) expr
  where
    go :: args A.:> env' -> env A.:> env' -> OpenExp env lab args t -> OpenExp env' lab () t
    go argWeaken varWeaken expr = case expr of
        Const ty x -> Const ty x
        PrimApp ty op ex -> PrimApp ty op (go argWeaken varWeaken ex)
        Pair ty e1 e2 -> Pair ty (go argWeaken varWeaken e1) (go argWeaken varWeaken e2)
        Nil -> Nil
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
-- - Pair or Nil: eliminated by pairing of variable labels
explode :: LabVal Int env -> OpenExp env unused args t -> Exploded Int args t
explode labelenv e =
    trace ("explode: exploding " ++ showsExpr (const "L?") 0 [] 9 e "") $
    evalIdGen (explode' labelenv e)

explode' :: LabVal Int env -> OpenExp env unused args t -> IdGen (Exploded Int args t)
explode' env = \case
    Const ty x -> do
        lab <- genScalarId ty
        return (DLScalar lab, DMap.singleton lab (Const ty x), mempty)
    PrimApp ty f e -> do
        (labs1, mp, argmp) <- explode' env e
        labs <- genId ty
        let pruned = PrimApp ty f (Label labs1)
        let mp' = tupleGetMap ty labs pruned
            mp'' = DMap.unionWithKey (error "explode: Overlapping id's") mp mp'
        return (labs, mp'', argmp)
    Pair _ e1 e2 -> do
        (labs1, mp1, argmp1) <- explode' env e1
        (labs2, mp2, argmp2) <- explode' env e2
        let mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 mp2
            argmp = DMap.unionWithKey (error "explode: Overlapping arg's") argmp1 argmp2
        return (DLPair labs1 labs2, mp, argmp)
    Nil -> return (DLNil, mempty, mempty)
    Let lhs rhs body -> do
        (lab1, mp1, argmp1) <- explode' env rhs
        labs <- genId (typeOf rhs)
        let (env', mpLHS) = lpushLHS lhs labs env (Label lab1)
        (lab2, mp2, argmp2) <- explode' env' body
        let mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mpLHS, mp2]
            argmp = DMap.unionWithKey (error "explode: Overlapping arg's") argmp1 argmp2
        return (lab2, mp, argmp)
    Var (A.Var _ idx) -> do
        let lab = prjL idx env
        return (DLScalar lab, mempty, mempty)
    Arg ty idx -> do
        lab <- genScalarId ty
        return (DLScalar lab, DMap.singleton lab (Arg ty idx), DMap.singleton idx lab)
    Get _ _ _ -> error "explode: Unexpected Get"
    Label _ -> error "explode: Unexpected Label"
  where
    tupleGetMap :: Ord lab => TypeR t -> DLabels lab t -> Exp lab args t -> DMap (DLabel lab) (Exp lab args)
    tupleGetMap TupRunit _ _ = DMap.empty
    tupleGetMap (TupRsingle _) (DLScalar lab) ex = DMap.singleton lab ex
    tupleGetMap (TupRpair t1 t2) (DLPair labs1 labs2) ex =
        let mp1 = tupleGetMap t1 labs1 (smartFst ex)
            mp2 = tupleGetMap t2 labs2 (smartSnd ex)
        in DMap.unionWithKey (error "tupleGetMap: Overlapping id's") mp1 mp2
    tupleGetMap _ _ _ = error "tupleGetMap: impossible GADTs"

    lpushLHS :: A.ELeftHandSide t env env' -> DLabels Int t -> LabVal Int env -> Exp Int args t -> (LabVal Int env', DMap (DLabel Int) (Exp Int args))
    lpushLHS lhs labs labelenv rhs = case (lhs, labs) of
        (A.LeftHandSidePair lhs1 lhs2, DLPair labs1 labs2) ->
            let (labelenv1, mp1) = lpushLHS lhs1 labs1 labelenv (smartFst rhs)
                (labelenv2, mp2) = lpushLHS lhs2 labs2 labelenv1 (smartSnd rhs)
            in (labelenv2, DMap.unionWithKey (error "lpushLHS: Overlapping id's") mp1 mp2)
        (A.LeftHandSideSingle _, DLScalar lab) -> (LPush labelenv lab, DMap.singleton lab rhs)
        (A.LeftHandSideWildcard _, _) -> (labelenv, mempty)
        (_, _) -> error "lpushLHS: impossible GADTs"

    smartFst :: OpenExp env lab args (t1, t2) -> OpenExp env lab args t1
    smartFst (Get (TupRpair t1 _) tidx ex) = Get t1 (insertFst tidx) ex
      where insertFst :: TupleIdx (t1, t2) t -> TupleIdx t1 t
            insertFst TIHere = TILeft TIHere
            insertFst (TILeft ti) = TILeft (insertFst ti)
            insertFst (TIRight ti) = TIRight (insertFst ti)
    smartFst ex
      | TupRpair t1 _ <- typeOf ex
      = Get t1 (TILeft TIHere) ex
    smartFst _ = error "smartFst: impossible GADTs"

    smartSnd :: OpenExp env lab args (t1, t2) -> OpenExp env lab args t2
    smartSnd (Get (TupRpair _ t2) tidx ex) = Get t2 (insertSnd tidx) ex
      where insertSnd :: TupleIdx (t1, t2) t -> TupleIdx t2 t
            insertSnd TIHere = TIRight TIHere
            insertSnd (TILeft ti) = TILeft (insertSnd ti)
            insertSnd (TIRight ti) = TIRight (insertSnd ti)
    smartSnd ex
      | TupRpair _ t2 <- typeOf ex
      = Get t2 (TIRight TIHere) ex
    smartSnd _ = error "smartSnd: impossible GADTs"

data PD a = P a | D a
  deriving (Show, Eq, Ord)

primaldual :: Exploded Int args Float
           -> (forall env. LabVal (PD Int) env -> OpenExp env (PD Int) args t)
           -> Exp (PD Int) args t
primaldual exploded cont =
    primal exploded (\labelenv -> dual exploded labelenv cont)

-- Resulting computation will only use P, never D
primal :: Ord lab
       => Exploded lab args res
       -> (forall env. LabVal (PD lab) env -> OpenExp env (PD lab) args t)
       -> Exp (PD lab) args t
primal (endlab, nodemap, _) = primal'Tuple nodemap endlab LEmpty

primal'Tuple :: Ord lab
             => DMap (DLabel lab) (Exp lab args)
             -> DLabels lab t
             -> LabVal (PD lab) env
             -> (forall env'. LabVal (PD lab) env' -> OpenExp env' (PD lab) args res)
             -> OpenExp env (PD lab) args res
primal'Tuple nodemap labs labelenv cont = case labs of
    DLNil -> cont labelenv
    DLScalar lab -> primal' nodemap lab labelenv cont
    DLPair labs1 labs2 ->
        primal'Tuple nodemap labs1 labelenv $ \labelenv1 ->
            primal'Tuple nodemap labs2 labelenv1 cont

primal' :: Ord lab
        => DMap (DLabel lab) (Exp lab args)
        -> DLabel lab t
        -> LabVal (PD lab) env
        -> (forall env'. LabVal (PD lab) env' -> OpenExp env' (PD lab) args res)
        -> OpenExp env (PD lab) args res
primal' nodemap lbl labelenv cont
  -- | trace ("primal': computing " ++ show lbl) False = undefined
  | labValContains labelenv (P (labelLabel lbl)) =
      cont labelenv
  | not (uniqueLabVal labelenv) =
      error "Non-unique label valuation in primal'!"
  | otherwise =
      case nodemap DMap.! lbl of
          Const ty value ->
              let subexp = cont (LPush labelenv (fmapLabel P lbl))
              in Let (A.LeftHandSideSingle ty) (Const ty value) subexp

          PrimApp restype oper (Label arglabs)
            -- We can do this because 'labelType lbl' is a ScalarType, and that's
            -- the same type as this expression node.
            | TupRsingle restypeS <- restype ->
                primal'Tuple nodemap arglabs labelenv $ \labelenv' ->
                    case labValFinds labelenv' (fmapLabels P arglabs) of
                        Just vars ->
                            let subexp = cont (LPush labelenv' (fmapLabel P lbl))
                            in Let (A.LeftHandSideSingle restypeS) (PrimApp restype oper (evars vars)) subexp
                        Nothing ->
                            error "primal: App argument did not compute argument"

          Get restype path (Label arglabs)
            -- We can do this because 'labelType lbl' is a ScalarType, and that's
            -- the same type as this expression node.
            | TupRsingle restypeS <- restype
            , DLScalar lab <- pickDLabels path arglabs ->
                primal' nodemap lab labelenv $ \labelenv' ->
                    case labValFind labelenv' (fmapLabel P lab) of
                        Just idx ->
                            Let (A.LeftHandSideSingle restypeS) (Var (A.Var restypeS idx))
                                (cont (LPush labelenv' (fmapLabel P lbl)))
                        Nothing ->
                            error "primal: Get argument did not compute argument"

          Arg ty idx ->
              let subexp = cont (LPush labelenv (fmapLabel P lbl))
              in Let (A.LeftHandSideSingle ty) (Arg ty idx) subexp

          Label (DLScalar arglabel) ->
              -- We can do this because 'labelType lbl' is a ScalarType, and that's
              -- the same type as this expression node.
              primal' nodemap arglabel labelenv $ \labelenv' ->
                  case labValFind labelenv' (fmapLabel P arglabel) of
                      Just idx ->
                          Let (A.LeftHandSideSingle (labelType arglabel))
                              (Var (A.Var (labelType arglabel) idx))
                              (cont (LPush labelenv' (fmapLabel P lbl)))
                      Nothing ->
                          error "primal: Label remap in nodemap was not previously computed"

          _ ->
              error "primal: Unexpected node shape in Exploded"

-- List of adjoints, collected for a particular label.
-- The exact variable references in the adjoints are dependent on the Let stack, thus the environment is needed.
newtype AdjList lab args t = AdjList (forall env. LabVal lab env -> [OpenExp env lab args t])

data AnyLabel lab = forall t. AnyLabel (DLabel lab t)

instance Show lab => Show (AnyLabel lab) where
    showsPrec d (AnyLabel lab) = showParen (d > 9) (showString "AnyLabel " . showsPrec 9 lab)

-- The Ord and Eq instances refer only to 'a'.
data OrdBox a b = OrdBox { _ordboxTag :: a, ordboxAuxiliary :: b }
instance Eq  a => Eq  (OrdBox a b) where OrdBox x _    ==     OrdBox y _ = x == y
instance Ord a => Ord (OrdBox a b) where OrdBox x _ `compare` OrdBox y _ = compare x y

dual :: Exploded Int args Float
     -> LabVal (PD Int) env
     -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) args t)
     -> OpenExp env (PD Int) args t
dual (DLScalar endlab, nodemap, _) labelenv cont =
    trace ("\nlabelorder: " ++ show [labelLabel l | AnyLabel l <- labelorder]) $
    let contribmap = DMap.singleton (fmapLabel D endlab) (AdjList (const [Const (labelType endlab) 1.0]))
    in dual' nodemap labelorder labelenv contribmap cont
  where
    -- Every numeric label is unique; we don't need the type information for that.
    -- We play fast and loose with that here: we use an 'OrdBox' for 'floodfill'
    -- to use the 'Ord' instance on 'Int' while carrying along the full 'DLabel'
    -- objects, and we index the 'parentmap' on the integer value too.
    parentsOf :: AnyLabel Int -> [AnyLabel Int]
    parentsOf (AnyLabel lbl) = expLabelParents (nodemap DMap.! lbl)

    alllabels :: [AnyLabel Int]
    alllabels =
        map ordboxAuxiliary . Set.toList
            $ floodfill (OrdBox (labelLabel endlab) (AnyLabel endlab))
                        (\box -> [OrdBox (labelLabel l) (AnyLabel l)
                                 | AnyLabel l <- parentsOf (ordboxAuxiliary box)])
                        mempty

    parentmap :: Map Int [AnyLabel Int]
    parentmap = Map.fromList [(labelLabel numlbl, parentsOf l)
                             | l@(AnyLabel numlbl) <- alllabels]

    labelorder :: [AnyLabel Int]
    labelorder = topsort' (\(AnyLabel l) -> labelLabel l)
                          alllabels
                          (\(AnyLabel l) -> parentmap Map.! labelLabel l)

dual' :: forall res env args.
         DMap (DLabel Int) (Exp Int args)
      -> [AnyLabel Int]
      -> LabVal (PD Int) env
      -> DMap (DLabel (PD Int)) (AdjList (PD Int) args)
      -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) args res)
      -> OpenExp env (PD Int) args res
dual' _ [] labelenv _ cont = cont labelenv
dual' nodemap (AnyLabel lbl : restlabels) labelenv contribmap cont =
    -- trace ("dual': computing " ++ show lbl) $
    case nodemap DMap.! lbl of
      -- We aren't interested in the adjoint of constant nodes -- seeing as
      -- they don't have any parents to contribute to.
      Const _ _ ->
          dual' nodemap restlabels labelenv contribmap cont

      -- Argument nodes don't have any nodes to contribute to either, but we do
      -- need to calculate and store their adjoint.
      Arg ty _ ->
          let adjoint = collectAdjoint contribmap lbl (TupRsingle ty) labelenv
          in Let (A.LeftHandSideSingle ty) adjoint
                 (dual' nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap cont)

      PrimApp _ (A.PrimAdd argtype) (Label (DLPair (DLScalar arglab1) (DLScalar arglab2))) ->
          let argtypeS = SingleScalarType (NumSingleType argtype)
              adjoint = collectAdjointNum contribmap lbl argtype labelenv
              contribmap' = updateContribmap lbl
                                [Contribution arglab1 TLNil (\adjidx _ -> Var (A.Var argtypeS adjidx))
                                ,Contribution arglab2 TLNil (\adjidx _ -> Var (A.Var argtypeS adjidx))]
                                contribmap
          in Let (A.LeftHandSideSingle argtypeS) adjoint
                 (dual' nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)

      PrimApp _ (A.PrimMul argtype) (Label (DLPair (DLScalar arglab1) (DLScalar arglab2))) ->
          let argtypeS = SingleScalarType (NumSingleType argtype)
              argtypeT = TupRsingle argtypeS
              adjoint = collectAdjointNum contribmap lbl argtype labelenv
              contribmap' = updateContribmap lbl
                                [Contribution arglab1 (arglab2 :@ TLNil) (\adjidx (arg2idx :@ _) ->
                                    PrimApp argtypeT (A.PrimMul argtype)
                                        (Pair (TupRpair argtypeT argtypeT) (Var (A.Var argtypeS adjidx))
                                                                           (Var (A.Var argtypeS arg2idx))))
                                ,Contribution arglab2 (arglab1 :@ TLNil) (\adjidx (arg1idx :@ _) ->
                                    PrimApp argtypeT (A.PrimMul argtype)
                                        (Pair (TupRpair argtypeT argtypeT) (Var (A.Var argtypeS adjidx))
                                                                           (Var (A.Var argtypeS arg1idx))))]
                                contribmap
          in Let (A.LeftHandSideSingle argtypeS) adjoint
                 (dual' nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)

      PrimApp _ (A.PrimLog argtype) (Label (DLScalar arglab)) ->
          let argtypeS = SingleScalarType (NumSingleType (FloatingNumType argtype))
              argtypeT = TupRsingle argtypeS
              adjoint = collectAdjointNum contribmap lbl (FloatingNumType argtype) labelenv
              contribmap' = updateContribmap lbl
                                [Contribution arglab (arglab :@ TLNil) (\adjidx (argidx :@ _) ->
                                    -- dE/dx = dE/d(log x) * d(log x)/dx = adjoint * 1/x = adjoint / x
                                    PrimApp argtypeT (A.PrimFDiv argtype)
                                        (Pair (TupRpair argtypeT argtypeT) (Var (A.Var argtypeS adjidx))
                                                                           (Var (A.Var argtypeS argidx))))]
                                contribmap
          in Let (A.LeftHandSideSingle argtypeS) adjoint
                 (dual' nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)

      -- Note that the types enforce that the result of this Get operation is a
      -- scalar. This typechecks because we arranged it like this in 'explode'.
      Get restype@(TupRsingle restypeS) path (Label arglabs) ->
          let adjoint = collectAdjoint contribmap lbl restype labelenv

              targetLabel = case pickDLabels path arglabs of
                              DLScalar lab -> lab
                              _ -> error "Invalid types in Get (pickDLabels)"

              contribmap' = updateContribmap lbl
                                [Contribution targetLabel TLNil (\adjidx _ -> Var (A.Var restypeS adjidx))]
                                contribmap
          in Let (A.LeftHandSideSingle restypeS) adjoint
                 (dual' nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)

      Label (DLScalar arglab) ->
          let adjoint = collectAdjoint contribmap lbl (TupRsingle (labelType arglab)) labelenv
              contribmap' = updateContribmap lbl
                                [Contribution arglab TLNil (\adjidx _ -> Var (A.Var (labelType arglab) adjidx))]
                                contribmap
          in Let (A.LeftHandSideSingle (labelType arglab)) adjoint
                 (dual' nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)

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
    forall parents t.
        Contribution (DLabel Int t)  -- adjoint of which label to contribute to
                     (TypedList (DLabel Int) parents)  -- labels you need the primary value of
                     (forall env. Idx env node -> TypedList (Idx env) parents -> OpenExp env (PD Int) args t)

-- Note: Before this code was extracted into a separate function, its
-- functionality was inlined in the branches of dual'. Because of that, the
-- branches needed explicit type signatures (and thus be separate functions),
-- since the definition of the contribution function had too intricate type
-- variables for GHC to figure out.
-- Now that this is a separate function, though, the type signature here (and
-- the typing of Contribution) removes the need of the branches of dual' to
-- have a separate type signature, significantly simplifying the structure of
-- the code.
updateContribmap :: DLabel Int node
                 -> [Contribution node args]
                 -> DMap (DLabel (PD Int)) (AdjList (PD Int) args)
                 -> DMap (DLabel (PD Int)) (AdjList (PD Int) args)
updateContribmap lbl =
    flip . foldr $ \(Contribution lab parentlabs gen) ->
        addContribution (fmapLabel D lab) $ \labelenv ->
            case (labValFind labelenv (fmapLabel D lbl), findAll labelenv parentlabs) of
                (Just idx, indices) -> gen idx indices
                _ -> error $ "updateContribmap: node D " ++ show lbl ++ " was not computed"
  where
    findAll :: LabVal (PD Int) env -> TypedList (DLabel Int) parents -> TypedList (Idx env) parents
    findAll labelenv = tlmap $ \lab -> fromMaybe (err lab) (labValFind labelenv (fmapLabel P lab))
      where err lab = error $ "updateContribmap: arg P " ++ show lab ++ " was not computed"

addContribution :: Ord lab
                => DLabel lab t
                -> (forall env. LabVal lab env -> OpenExp env lab args t)
                -> DMap (DLabel lab) (AdjList lab args)
                -> DMap (DLabel lab) (AdjList lab args)
addContribution lbl contribution =
    DMap.insertWith (\(AdjList f1) (AdjList f2) -> AdjList (\labelenv -> f1 labelenv ++ f2 labelenv))
                    lbl
                    (AdjList (pure . contribution))

collectAdjoint :: DMap (DLabel (PD Int)) (AdjList (PD Int) args)
               -> DLabel Int item
               -> TypeR item
               -> LabVal (PD Int) env
               -> OpenExp env (PD Int) args item
collectAdjoint contribmap lbl ty labelenv =
    case contribmap DMap.! fmapLabel D lbl of
      AdjList listgen -> fromJust $ maybeExpSum ty (listgen labelenv)

collectAdjointNum :: DMap (DLabel (PD Int)) (AdjList (PD Int) args)
                  -> DLabel Int item
                  -> NumType item
                  -> LabVal (PD Int) env
                  -> OpenExp env (PD Int) args item
collectAdjointNum contribmap lbl ty labelenv =
    case contribmap DMap.! fmapLabel D lbl of
      AdjList listgen -> expSum ty (listgen labelenv)

class IsAdditive s where
    zeroForType' :: (forall a. Num a => a) -> s t -> OpenExp env lab args t
    expPlus :: s t -> OpenExp env lab args t -> OpenExp env lab args t -> OpenExp env lab args t

    zeroForType :: s t -> OpenExp env lab args t
    zeroForType = zeroForType' 0

    expSum :: s t -> [OpenExp env lab args t] -> OpenExp env lab args t
    expSum ty [] = zeroForType ty
    expSum ty es = foldl1 (expPlus ty) es

class IsMaybeAdditive s where
    maybeZeroForType' :: (forall a. Num a => a) -> s t -> Maybe (OpenExp env lab args t)
    maybeExpPlus :: s t -> OpenExp env lab args t -> OpenExp env lab args t -> Maybe (OpenExp env lab args t)

    maybeZeroForType :: s t -> Maybe (OpenExp env lab args t)
    maybeZeroForType = maybeZeroForType' 0

    maybeExpSum :: s t -> [OpenExp env lab args t] -> Maybe (OpenExp env lab args t)
    maybeExpSum ty [] = maybeZeroForType ty
    maybeExpSum ty (expr:exprs) = go exprs expr
      where go [] accum = Just accum
            go (e:es) accum = maybeExpPlus ty accum e >>= go es

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

instance IsMaybeAdditive SingleType where
    maybeZeroForType' z (NumSingleType t) = Just (zeroForType' z t)

    maybeExpPlus (NumSingleType ty) e1 e2 = Just (expPlus ty e1 e2)

instance IsMaybeAdditive ScalarType where
    maybeZeroForType' z (SingleScalarType t) = maybeZeroForType' z t
    maybeZeroForType' _ (VectorScalarType _) = Nothing

    maybeExpPlus (SingleScalarType ty) e1 e2 = maybeExpPlus ty e1 e2
    maybeExpPlus (VectorScalarType _) _ _ = Nothing

instance IsMaybeAdditive TypeR where
    maybeZeroForType' _ TupRunit = Just Nil
    maybeZeroForType' z (TupRsingle t) = maybeZeroForType' z t
    maybeZeroForType' z (TupRpair t1 t2) =
        Pair (TupRpair t1 t2) <$> maybeZeroForType' z t1 <*> maybeZeroForType' z t2

    maybeExpPlus ty e1 e2 = tupleZip ty maybeExpPlus e1 e2

-- Errors if any parents are not Label nodes, or if called on a Let or Var node.
expLabelParents :: OpenExp env lab args t -> [AnyLabel lab]
expLabelParents = \case
    Const _ _ -> []
    PrimApp _ _ e -> fromLabel e
    Pair _ e1 e2 -> fromLabel e1 ++ fromLabel e2
    Nil -> []
    Get _ path (Label labs) -> collect (pickDLabels path labs)
    Get _ _ e -> fromLabel e
    Arg _ _ -> []
    Label lab -> collect lab
    Let _ _ _ -> unimplemented "Let"
    Var _ -> unimplemented "Var"
  where
    unimplemented name =
        error ("expLabelParents: Unimplemented for " ++ name ++ ", semantics unclear")

    fromLabel (Label labs) = collect labs
    fromLabel _ = error "expLabelParents: Parent is not a label set"

    collect :: DLabels lab t -> [AnyLabel lab]
    collect DLNil = []
    collect (DLScalar lab) = [AnyLabel lab]
    collect (DLPair labs1 labs2) = collect labs1 ++ collect labs2
