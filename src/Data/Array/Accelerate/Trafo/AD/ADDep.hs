{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Array.Accelerate.Trafo.AD.ADDep (
  reverseAD
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

import Debug.Trace

import qualified Data.Array.Accelerate.AST as A
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.AD.Algorithms
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.TupleZip


newtype IdGen a = IdGen (State Int a)
  deriving (Functor, Applicative, Monad, MonadState Int)

evalIdGen :: IdGen a -> a
evalIdGen (IdGen s) = evalState s 1

genScalarId :: ScalarType t -> IdGen (DLabel Int t)
genScalarId ty = state (\s -> (DLabel ty s, succ s))

genId :: TupleType t -> IdGen (DLabels Int t)
genId TupRunit = return DLNil
genId (TupRsingle ty) = DLScalar <$> genScalarId ty
genId (TupRpair t1 t2) = DLPair <$> genId t1 <*> genId t2


type Exploded lab res = (DLabels lab res, DMap (DLabel lab) (Exp lab))

showExploded :: (Ord lab, Show lab) => Exploded lab t -> String
showExploded (endlab, nodemap) = "(" ++ showDLabels show endlab ++ ", " ++ showNodemap nodemap ++ ")"

showNodemap :: (Ord lab, Show lab) => DMap (DLabel lab) (Exp lab) -> String
showNodemap nodemap =
    let tups = sortOn fst [(lab, (showDLabel dlab, show expr)) | dlab@(DLabel _ lab) :=> expr <- DMap.assocs nodemap]
        s = intercalate ", " ["(" ++ dlabshow ++ ") :=> " ++ exprshow
                             | (_, (dlabshow, exprshow)) <- tups]
    in "[" ++ s ++ "]"

showDLabel :: Show lab => DLabel lab t -> String
showDLabel (DLabel ty lab) = "L" ++ show lab ++ " :: " ++ show ty

explodedAddNode :: Ord lab => DLabel lab t -> Exp lab t -> Exploded lab res -> Exploded lab res
explodedAddNode lab expr (endlab, nodemap)
  | lab `DMap.notMember` nodemap = (endlab, DMap.insert lab expr nodemap)
  | otherwise = error "explodedAddNode: Label already exists in nodemap"

-- TODO: This now takes a constant scalar value as the function argument, but
-- this should be an ELeftHandSide, since that is also what we have in the
-- context of a gradientE expression. Then the type of the 'expr' argument
-- changes too.
-- The label environment passed to 'explode' here should derive from that LHS.
-- Maybe the value stored in the nodemap for the labels bound to the LHS should
-- be of a new expression node type, say Arg, that models arguments with
-- respect to which we are differentiating. If they then get type-level index
-- into the top-level LHS here, say an Idx (that should work), then if the rest
-- of the computation just considers them constants, we should be able to fill
-- them in here at the end. To do this filling in, we'll have to recurse over
-- the entire produced expression, incrementing indices along the way, and
-- replace each Arg with a Var reference to the let-bound variable at the top
-- level (which is inserted there as we go; we must do this as we go since
-- otherwise the types won't match up).
reverseAD :: ScalarType t -> t -> OpenExp ((), t) unused Float -> Exp (PD Int) t
reverseAD paramtype param expr =
    let arglabel = DLabel paramtype (-1)
        exploded = explode (LPush LEmpty arglabel) expr
        exploded' = explodedAddNode arglabel (Const paramtype param) exploded
    in trace ("exploded: " ++ showExploded exploded') $
       primaldual exploded' $ \labelenv ->
           trace ("\nlabval in core: " ++ show (labValToList labelenv)) $
           case labValFind labelenv (fmapLabel D arglabel) of
             Just idx -> Var (A.Var paramtype idx)
             Nothing -> error "reverseAD: dual did not compute adjoint of parameter"

-- Map will NOT contain:
-- - Let or Var
-- - Label: the original expression should not have included Label
-- - Pair or Nil: eliminated by pairing of variable labels
explode :: LabVal Int env -> OpenExp env unused t -> Exploded Int t
explode labelenv e = evalIdGen (explode' labelenv e)

explode' :: LabVal Int env -> OpenExp env unused t -> IdGen (Exploded Int t)
explode' env = \case
    Const ty x -> do
        lab <- genScalarId ty
        return (DLScalar lab, DMap.singleton lab (Const ty x))
    PrimApp ty f e -> do
        (labs1, mp) <- explode' env e
        labs <- genId ty
        let pruned = PrimApp ty f (Label labs1)
        let mp' = tupleGetMap ty labs pruned
            mp'' = DMap.unionWithKey (error "explode: Overlapping id's") mp mp'
        return (labs, mp'')
    Pair _ e1 e2 -> do
        (labs1, mp1) <- explode' env e1
        (labs2, mp2) <- explode' env e2
        let mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 mp2
        return (DLPair labs1 labs2, mp)
    Nil -> return (DLNil, DMap.empty)
    Let lhs rhs body -> do
        (lab1, mp1) <- explode' env rhs
        labs <- genId (typeOf rhs)
        let (env', mpLHS) = lpushLHS lhs labs env (Label lab1)
        (lab2, mp2) <- explode' env' body
        let mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mpLHS, mp2]
        return (lab2, mp)
    Var (A.Var _ idx) -> do
        let lab = prjL idx env
        return (DLScalar lab, mempty)
    Get _ _ _ -> error "explode: Unexpected Get"
    Label _ -> error "explode: Unexpected Label"
  where
    tupleGetMap :: Ord lab => TupleType t -> DLabels lab t -> Exp lab t -> DMap (DLabel lab) (Exp lab)
    tupleGetMap TupRunit _ _ = DMap.empty
    tupleGetMap (TupRsingle _) (DLScalar lab) ex = DMap.singleton lab ex
    tupleGetMap (TupRpair t1 t2) (DLPair labs1 labs2) ex =
        let mp1 = tupleGetMap t1 labs1 (smartFst ex)
            mp2 = tupleGetMap t2 labs2 (smartSnd ex)
        in DMap.unionWithKey (error "tupleGetMap: Overlapping id's") mp1 mp2
    tupleGetMap _ _ _ = error "tupleGetMap: impossible GADTs"

    lpushLHS :: A.ELeftHandSide t env env' -> DLabels Int t -> LabVal Int env -> Exp Int t -> (LabVal Int env', DMap (DLabel Int) (Exp Int))
    lpushLHS lhs labs labelenv rhs = case (lhs, labs) of
        (A.LeftHandSidePair lhs1 lhs2, DLPair labs1 labs2) ->
            let (labelenv1, mp1) = lpushLHS lhs1 labs1 labelenv (smartFst rhs)
                (labelenv2, mp2) = lpushLHS lhs2 labs2 labelenv1 (smartSnd rhs)
            in (labelenv2, DMap.unionWithKey (error "lpushLHS: Overlapping id's") mp1 mp2)
        (A.LeftHandSideSingle _, DLScalar lab) -> (LPush labelenv lab, DMap.singleton lab rhs)
        (A.LeftHandSideWildcard _, _) -> (labelenv, mempty)
        (_, _) -> error "lpushLHS: impossible GADTs"

    smartFst :: OpenExp env lab (t1, t2) -> OpenExp env lab t1
    smartFst (Get (TupRpair t1 _) tidx ex) = Get t1 (insertFst tidx) ex
      where insertFst :: TupleIdx (t1, t2) t -> TupleIdx t1 t
            insertFst TIHere = TILeft TIHere
            insertFst (TILeft ti) = TILeft (insertFst ti)
            insertFst (TIRight ti) = TIRight (insertFst ti)
    smartFst ex
      | TupRpair t1 _ <- typeOf ex
      = Get t1 (TILeft TIHere) ex
    smartFst _ = error "smartFst: impossible GADTs"

    smartSnd :: OpenExp env lab (t1, t2) -> OpenExp env lab t2
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

primaldual :: Exploded Int Float
           -> (forall env. LabVal (PD Int) env -> OpenExp env (PD Int) t)
           -> Exp (PD Int) t
primaldual exploded cont =
    primal exploded (\labelenv -> dual exploded labelenv cont)

-- Resulting computation will only use P, never D
primal :: Ord lab
       => Exploded lab res
       -> (forall env. LabVal (PD lab) env -> OpenExp env (PD lab) t)
       -> Exp (PD lab) t
primal (endlab, nodemap) = primal'Tuple nodemap endlab LEmpty

primal'Tuple :: Ord lab
             => DMap (DLabel lab) (Exp lab)
             -> DLabels lab t
             -> LabVal (PD lab) env
             -> (forall env'. LabVal (PD lab) env' -> OpenExp env' (PD lab) res)
             -> OpenExp env (PD lab) res
primal'Tuple nodemap labs labelenv cont = case labs of
    DLNil -> cont labelenv
    DLScalar lab -> primal' nodemap lab labelenv cont
    DLPair labs1 labs2 ->
        primal'Tuple nodemap labs1 labelenv $ \labelenv1 ->
            primal'Tuple nodemap labs2 labelenv1 cont

primal' :: Ord lab
        => DMap (DLabel lab) (Exp lab)
        -> DLabel lab t
        -> LabVal (PD lab) env
        -> (forall env'. LabVal (PD lab) env' -> OpenExp env' (PD lab) res)
        -> OpenExp env (PD lab) res
primal' nodemap lbl labelenv cont
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

          _ ->
              error "primal: Unexpected node shape in Exploded"

-- List of adjoints, collected for a particular label.
-- The exact variable references in the adjoints are dependent on the Let stack, thus the environment is needed.
newtype AdjList lab t = AdjList (forall env. LabVal lab env -> [OpenExp env lab t])

data AnyLabel lab = forall t. AnyLabel (DLabel lab t)

instance Show lab => Show (AnyLabel lab) where
    showsPrec d (AnyLabel lab) = showParen (d > 9) (showString "AnyLabel " . showsPrec 9 lab)

-- The Ord and Eq instances refer only to 'a'.
data OrdBox a b = OrdBox { _ordboxTag :: a, ordboxAuxiliary :: b }
instance Eq  a => Eq  (OrdBox a b) where OrdBox x _    ==     OrdBox y _ = x == y
instance Ord a => Ord (OrdBox a b) where OrdBox x _ `compare` OrdBox y _ = compare x y

dual :: Exploded Int Float
     -> LabVal (PD Int) env
     -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) t)
     -> OpenExp env (PD Int) t
dual (DLScalar endlab, nodemap) labelenv cont =
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

-- Note [dualGate split]
dual' :: forall res env.
         DMap (DLabel Int) (Exp Int)
      -> [AnyLabel Int]
      -> LabVal (PD Int) env
      -> DMap (DLabel (PD Int)) (AdjList (PD Int))
      -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) res)
      -> OpenExp env (PD Int) res
dual' _ [] labelenv _ cont = cont labelenv
dual' nodemap (AnyLabel lbl : restlabels) labelenv contribmap cont =
    case nodemap DMap.! lbl of
      -- Note that we normally aren't interested in the adjoint of a constant
      -- node -- seeing as it doesn't have any parents to contribute to.
      -- However, the AD parameter is injected as a constant node too, and we
      -- do need the parameter's adjoint, obviously.
      Const ty _ ->
          let adjoint = case contribmap DMap.! fmapLabel D lbl of
                          AdjList listgen -> fromJust $ maybeExpSum ty (listgen labelenv)
          in Let (A.LeftHandSideSingle ty) adjoint
                 (dual' nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap cont)

      -- Note [dual' split]
      -- The bodies of these case arms are written as separate functions, and
      -- not merged into dual' here, so that the type of the label 'lbl' (which
      -- is 'DLabel Int a' for some 'a') can be mentioned explicitly in a type
      -- signature somewhere. This is necessary, because the 'contribution'
      -- variable in those helper functions _must_ have a type signature for
      -- GHC to understand it, and that type signature would mention 'a', which
      -- would not be mentioned anywhere yet if the function body was just
      -- spliced in here.
      PrimApp _ (A.PrimAdd argtype) (Label arglabs) ->
          dual'Add nodemap lbl argtype arglabs restlabels labelenv contribmap cont

      PrimApp _ (A.PrimMul argtype) (Label arglabs) ->
          dual'Mul nodemap lbl argtype arglabs restlabels labelenv contribmap cont

      PrimApp _ (A.PrimLog argtype) (Label arglabs) ->
          dual'Log nodemap lbl argtype arglabs restlabels labelenv contribmap cont

      -- Note that the types enforce that the result of this Get operation is a
      -- scalar. This typechecks because we arranged it like this in 'explode'.
      Get restype path (Label arglabs) ->
          dual'Get nodemap lbl restype arglabs path restlabels labelenv contribmap cont

      expr -> trace ("\n!! " ++ show expr) undefined

-- TODO: More DRY code!
dual'Add :: forall res env a.
            DMap (DLabel Int) (Exp Int)
         -> DLabel Int a
         -> NumType a
         -> DLabels Int (a, a)
         -> [AnyLabel Int]
         -> LabVal (PD Int) env
         -> DMap (DLabel (PD Int)) (AdjList (PD Int))
         -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) res)
         -> OpenExp env (PD Int) res
dual'Add nodemap lbl argtype (DLPair (DLScalar arglab1) (DLScalar arglab2)) restlabels labelenv contribmap cont =
    let argtypeS = SingleScalarType (NumSingleType argtype)
        adjoint = case contribmap DMap.! fmapLabel D lbl of
                    AdjList listgen -> expSum argtype (listgen labelenv)
        -- Type signature here is necessary, and its mentioning of 'a' enforces
        -- that dual'Add has a type signature, which enforces this separation
        -- thing. See Note [dual' split].
        contribution :: LabVal (PD Int) env' -> OpenExp env' (PD Int) a
        contribution labelenv' =
            case labValFind labelenv' (fmapLabel D lbl) of
              Just adjidx ->
                  Var (A.Var argtypeS adjidx)
              _ -> error "dual' App Add: node D was not computed"
        contribmap' = addContribution (fmapLabel D arglab1) contribution $
                      addContribution (fmapLabel D arglab2) contribution $
                      contribmap
    in Let (A.LeftHandSideSingle argtypeS) adjoint
           (dual' nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)
dual'Add _ _ _ _ _ _ _ _ = error "Invalid types in PrimAdd"

dual'Mul :: forall res env a.
            DMap (DLabel Int) (Exp Int)
         -> DLabel Int a
         -> NumType a
         -> DLabels Int (a, a)
         -> [AnyLabel Int]
         -> LabVal (PD Int) env
         -> DMap (DLabel (PD Int)) (AdjList (PD Int))
         -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) res)
         -> OpenExp env (PD Int) res
dual'Mul nodemap lbl argtype (DLPair (DLScalar arglab1) (DLScalar arglab2)) restlabels labelenv contribmap cont =
    let argtypeS = SingleScalarType (NumSingleType argtype)
        argtypeT = TupRsingle argtypeS
        adjoint = case contribmap DMap.! fmapLabel D lbl of
                    AdjList listgen -> expSum argtype (listgen labelenv)
        contribution1 :: LabVal (PD Int) env' -> OpenExp env' (PD Int) a
        contribution1 labelenv' =
            case (labValFind labelenv' (fmapLabel P arglab2), labValFind labelenv' (fmapLabel D lbl)) of
              (Just arg2idx, Just adjidx) ->
                  PrimApp argtypeT (A.PrimMul argtype)
                      (Pair (TupRpair argtypeT argtypeT) (Var (A.Var argtypeS adjidx))
                                                         (Var (A.Var argtypeS arg2idx)))
              _ -> error "dual' App Mul: arg P and/or node D was not computed"
        contribution2 :: LabVal (PD Int) env' -> OpenExp env' (PD Int) a
        contribution2 labelenv' =
            case (labValFind labelenv' (fmapLabel P arglab1), labValFind labelenv' (fmapLabel D lbl)) of
              (Just arg1idx, Just adjidx) ->
                  PrimApp argtypeT (A.PrimMul argtype)
                      (Pair (TupRpair argtypeT argtypeT) (Var (A.Var argtypeS adjidx))
                                                         (Var (A.Var argtypeS arg1idx)))
              _ -> error "dual' App Mul: arg P and/or node D was not computed"
        contribmap' = addContribution (fmapLabel D arglab1) contribution1 $
                      addContribution (fmapLabel D arglab2) contribution2 $
                      contribmap
    in Let (A.LeftHandSideSingle argtypeS) adjoint
           (dual' nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)
dual'Mul _ _ _ _ _ _ _ _ = error "Invalid types in PrimMul"

dual'Log :: forall res env a.
            DMap (DLabel Int) (Exp Int)
         -> DLabel Int a
         -> FloatingType a
         -> DLabels Int a
         -> [AnyLabel Int]
         -> LabVal (PD Int) env
         -> DMap (DLabel (PD Int)) (AdjList (PD Int))
         -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) res)
         -> OpenExp env (PD Int) res
dual'Log nodemap lbl argtype (DLScalar arglab) restlabels labelenv contribmap cont =
    let argtypeS = SingleScalarType (NumSingleType (FloatingNumType argtype))
        argtypeT = TupRsingle argtypeS
        adjoint = case contribmap DMap.! fmapLabel D lbl of
                    AdjList listgen -> expSum argtype (listgen labelenv)
        contribution :: LabVal (PD Int) env' -> OpenExp env' (PD Int) a
        contribution labelenv' =
            case (labValFind labelenv' (fmapLabel P arglab), labValFind labelenv' (fmapLabel D lbl)) of
              (Just argidx, Just adjidx) ->
                  -- dE/dx = dE/d(log x) * d(log x)/dx = adjoint * 1/x = adjoint / x
                  PrimApp argtypeT (A.PrimFDiv argtype)
                      (Pair (TupRpair argtypeT argtypeT) (Var (A.Var argtypeS adjidx))
                                                         (Var (A.Var argtypeS argidx)))
              _ -> error "dual' App Log: arg P and/or node D were not computed"
        contribmap' = addContribution (fmapLabel D arglab) contribution contribmap
    in Let (A.LeftHandSideSingle argtypeS) adjoint
           (dual' nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)
dual'Log _ _ _ _ _ _ _ _ = error "Invalid types in PrimLog"

-- Note that the types enforce that the result of this Get operation is a scalar.
dual'Get :: forall res env tup item.
            DMap (DLabel Int) (Exp Int)
         -> DLabel Int item
         -> TupleType item
         -> DLabels Int tup
         -> TupleIdx item tup
         -> [AnyLabel Int]
         -> LabVal (PD Int) env
         -> DMap (DLabel (PD Int)) (AdjList (PD Int))
         -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) res)
         -> OpenExp env (PD Int) res
dual'Get nodemap lbl (TupRsingle restypeS) arglabs path restlabels labelenv contribmap cont =
    let adjoint = case contribmap DMap.! fmapLabel D lbl of
                    AdjList listgen -> fromJust $ maybeExpSum restypeS (listgen labelenv)

        targetLabel = case pickDLabels path arglabs of
                        DLScalar lab -> lab
                        _ -> error "Invalid types in Get (pickDLabels)"

        contribution :: LabVal (PD Int) env' -> OpenExp env' (PD Int) item
        contribution labelenv' =
            case labValFind labelenv' (fmapLabel D targetLabel) of
              Just adjidx -> Var (A.Var restypeS adjidx)
              _ -> error "dual' App Get: node D was not computed"

        contribmap' = addContribution (fmapLabel D targetLabel) contribution contribmap
    in Let (A.LeftHandSideSingle restypeS) adjoint
           (dual' nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)
dual'Get _ _ _ _ _ _ _ _ _ = error "Invalid types in Get"

-- Utility functions
-- -----------------

addContribution :: Ord lab
                => DLabel lab t
                -> (forall env. LabVal lab env -> OpenExp env lab t)
                -> DMap (DLabel lab) (AdjList lab)
                -> DMap (DLabel lab) (AdjList lab)
addContribution lbl contribution =
    DMap.insertWith (\(AdjList f1) (AdjList f2) -> AdjList (\labelenv -> f1 labelenv ++ f2 labelenv))
                    lbl
                    (AdjList (pure . contribution))

class IsAdditive s where
    zeroForType' :: (forall a. Num a => a) -> s t -> OpenExp env lab t
    expPlus :: s t -> OpenExp env lab t -> OpenExp env lab t -> OpenExp env lab t

    zeroForType :: s t -> OpenExp env lab t
    zeroForType = zeroForType' 0

    expSum :: s t -> [OpenExp env lab t] -> OpenExp env lab t
    expSum ty [] = zeroForType ty
    expSum ty es = foldl1 (expPlus ty) es

class IsMaybeAdditive s where
    maybeZeroForType' :: (forall a. Num a => a) -> s t -> Maybe (OpenExp env lab t)
    maybeExpPlus :: s t -> OpenExp env lab t -> OpenExp env lab t -> Maybe (OpenExp env lab t)

    maybeZeroForType :: s t -> Maybe (OpenExp env lab t)
    maybeZeroForType = maybeZeroForType' 0

    maybeExpSum :: s t -> [OpenExp env lab t] -> Maybe (OpenExp env lab t)
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
    maybeZeroForType' _ (NonNumSingleType _) = Nothing

    maybeExpPlus (NumSingleType ty) e1 e2 = Just (expPlus ty e1 e2)
    maybeExpPlus (NonNumSingleType _) _ _ = Nothing

instance IsMaybeAdditive ScalarType where
    maybeZeroForType' z (SingleScalarType t) = maybeZeroForType' z t
    maybeZeroForType' _ (VectorScalarType _) = Nothing

    maybeExpPlus (SingleScalarType ty) e1 e2 = maybeExpPlus ty e1 e2
    maybeExpPlus (VectorScalarType _) _ _ = Nothing

instance IsMaybeAdditive TupleType where
    maybeZeroForType' _ TupRunit = Just Nil
    maybeZeroForType' z (TupRsingle t) = maybeZeroForType' z t
    maybeZeroForType' z (TupRpair t1 t2) =
        Pair (TupRpair t1 t2) <$> maybeZeroForType' z t1 <*> maybeZeroForType' z t2

    maybeExpPlus ty e1 e2 = tupleZip ty maybeExpPlus e1 e2

-- Errors if any parents are not Label nodes, or if called on a Let or Var node.
expLabelParents :: OpenExp env lab t -> [AnyLabel lab]
expLabelParents = \case
    Const _ _ -> []
    PrimApp _ _ e -> fromLabel e
    Pair _ e1 e2 -> fromLabel e1 ++ fromLabel e2
    Nil -> []
    Get _ path (Label labs) -> collect (pickDLabels path labs)
    Get _ _ e -> fromLabel e
    Let _ _ _ -> unimplemented "Let"
    Var _ -> unimplemented "Var"
    Label _ -> unimplemented "Label"
  where
    unimplemented name =
        error ("expLabelParents: Unimplemented for " ++ name ++ ", semantics unclear")

    fromLabel (Label labs) = collect labs
    fromLabel _ = error ("expLabelParents: Parent is not a label set")

    collect :: DLabels lab t -> [AnyLabel lab]
    collect DLNil = []
    collect (DLScalar lab) = [AnyLabel lab]
    collect (DLPair labs1 labs2) = collect labs1 ++ collect labs2
