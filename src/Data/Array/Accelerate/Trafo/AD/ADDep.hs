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
module Data.Array.Accelerate.Trafo.AD.ADDep
  -- ( reverseAD )
where

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
import Data.Array.Accelerate.Trafo.Substitution (weakenE)
import Data.Array.Accelerate.Trafo.AD.Algorithms
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.Array.Accelerate.Trafo.AD.TupleZip
import Data.Array.Accelerate.Trafo.AD.Sink


newtype IdGen a = IdGen (State Int a)
  deriving (Functor, Applicative, Monad, MonadState Int)

evalIdGen :: IdGen a -> a
evalIdGen (IdGen s) = evalState s 1

genId :: TupleType t -> IdGen (DLabel Int t)
genId ty = state (\s -> (DLabel ty s, succ s))


type Exploded lab res = (DLabel lab res, DMap (DLabel lab) (Exp lab))

showExploded :: (Ord lab, Show lab) => Exploded lab t -> String
showExploded (endlab, nodemap) = "(" ++ show endlab ++ ", " ++ showNodemap nodemap ++ ")"

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

-- reverseAD :: TupleType t -> t -> OpenExp ((), t) unused Float -> Exp (PD Int) t
-- reverseAD paramtype param expr =
--     let arglabel = DLabel paramtype (-1)
--         exploded = explode (LPush LEmpty arglabel) expr
--         exploded' = explodedAddNode arglabel (Const paramtype param) exploded
--     in trace ("exploded: " ++ showExploded exploded') $
--        primaldual exploded' $ \labelenv ->
--            trace ("\nlabval in core: " ++ show (labValToList labelenv)) $
--            case labValFind labelenv (fmapLabel D arglabel) of
--              Just idx -> Var paramtype idx
--              Nothing -> error "reverseAD: dual did not compute adjoint of parameter"

-- Map will contain neither Let nor Var; also it will not contain Label, since
-- the original expression should not have included Label.
explode :: LabVal Int env -> OpenExp env unused t -> Exploded Int t
explode labelenv e = evalIdGen (explode' labelenv e)

explode' :: LabVal Int env -> OpenExp env unused t -> IdGen (Exploded Int t)
explode' env = \case
    Const ty x -> do
        lab <- genId (TupRsingle ty)
        return (lab, DMap.singleton lab (Const ty x))
    PrimApp ty f e -> do
        (lab1, mp) <- explode' env e
        lab <- genId ty
        let pruned = PrimApp ty f (Label lab1)
        return (lab, DMap.insert lab pruned mp)
    Pair ty e1 e2 -> do
        (lab1, mp1) <- explode' env e1
        (lab2, mp2) <- explode' env e2
        let mp = DMap.unionWithKey (error "explode: Overlapping id's") mp1 mp2
        lab <- genId ty
        let pruned = Pair ty (Label lab1) (Label lab2)
        return (lab, DMap.insert lab pruned mp)
    Nil -> do
        lab <- genId TupRunit
        return (lab, DMap.singleton lab Nil)
    Let lhs rhs body -> do
        (lab1, mp1) <- explode' env rhs
        (env', mpLHS) <- lpushLHS lhs env (Label lab1)
        (lab2, mp2) <- explode' env' body
        let mp = DMap.unionsWithKey (error "explode: Overlapping id's") [mp1, mpLHS, mp2]
        return (lab2, mp)
    Var (A.Var _ idx) -> do
        let lab = prjL idx env
        return (lab, mempty)
    Get _ _ -> error "explode: Unexpected Get"
    Label _ -> error "explode: Unexpected Label"
  where
    lpushLHS :: A.ELeftHandSide t env env' -> LabVal Int env -> Exp Int t -> IdGen (LabVal Int env', DMap (DLabel Int) (Exp Int))
    lpushLHS lhs labelenv rhs = case lhs of
        A.LeftHandSidePair lhs1 lhs2 -> do
            (labelenv1, mp1) <- lpushLHS lhs1 labelenv (smartFst rhs)
            (labelenv2, mp2) <- lpushLHS lhs2 labelenv1 (smartSnd rhs)
            return (labelenv2, DMap.unionWithKey (error "lpushLHS: Overlapping id's") mp1 mp2)
        A.LeftHandSideSingle sty -> do
            lab <- genId (TupRsingle sty)
            return (LPush labelenv lab, DMap.singleton lab rhs)
        A.LeftHandSideWildcard _ -> return (labelenv, mempty)

    smartFst :: OpenExp env lab (t1, t2) -> OpenExp env lab t1
    smartFst (Get tidx ex) = Get (insertFst tidx) ex
      where insertFst :: TupleIdx (t1, t2) t -> TupleIdx t1 t
            insertFst TIHere = TILeft TIHere
            insertFst (TILeft ti) = TILeft (insertFst ti)
            insertFst (TIRight ti) = TIRight (insertFst ti)
    smartFst ex = Get (TILeft TIHere) ex

    smartSnd :: OpenExp env lab (t1, t2) -> OpenExp env lab t2
    smartSnd (Get tidx ex) = Get (insertSnd tidx) ex
      where insertSnd :: TupleIdx (t1, t2) t -> TupleIdx t2 t
            insertSnd TIHere = TIRight TIHere
            insertSnd (TILeft ti) = TILeft (insertSnd ti)
            insertSnd (TIRight ti) = TIRight (insertSnd ti)
    smartSnd ex = Get (TIRight TIHere) ex

{-
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
primal (endlab, nodemap) = primal' nodemap endlab LEmpty

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
              in Let (Const ty value) subexp

          PrimApp restype oper (Label arglbl) ->
              primal' nodemap arglbl labelenv $ \labelenv' ->
                  case labValFind labelenv' (fmapLabel P arglbl) of
                      Just idx ->
                          let subexp = cont (LPush labelenv' (fmapLabel P lbl))
                          in Let (App restype oper (Var (labelType arglbl) idx)) subexp
                      Nothing ->
                          error "primal: App argument did not compute argument"

          Pair restype (Label arglbl1) (Label arglbl2) ->
              primal' nodemap arglbl1 labelenv $ \labelenv1 ->
              primal' nodemap arglbl2 labelenv1 $ \labelenv2 ->
                  case (labValFind labelenv2 (fmapLabel P arglbl1)
                       ,labValFind labelenv2 (fmapLabel P arglbl2)) of
                    (Just idx1, Just idx2) ->
                        let subexp = cont (LPush labelenv2 (fmapLabel P lbl))
                        in Let (Pair restype (Var (labelType arglbl1) idx1) (Var (labelType arglbl2) idx2)) subexp
                    _ ->
                        error "primal: Pair arguments did not compute argument(s)"

          _ ->
              error "primal: Unexpected node shape in Exploded"
-}

-- List of adjoints, collected for a particular label.
-- The exact variable references in the adjoints are dependent on the Let stack, thus the environment is needed.
newtype AdjList lab t = AdjList (forall env. LabVal lab env -> [OpenExp env lab t])

data AnyLabel lab = forall t. AnyLabel (DLabel lab t)

instance Show lab => Show (AnyLabel lab) where
    showsPrec d (AnyLabel lab) = showParen (d > 9) (showString "AnyLabel " . showsPrec 9 lab)

{-
-- The Ord and Eq instances refer only to 'a'.
data OrdBox a b = OrdBox { _ordboxTag :: a, ordboxAuxiliary :: b }
instance Eq  a => Eq  (OrdBox a b) where OrdBox x _    ==     OrdBox y _ = x == y
instance Ord a => Ord (OrdBox a b) where OrdBox x _ `compare` OrdBox y _ = compare x y

dual :: Exploded Int Float
     -> LabVal (PD Int) env
     -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) t)
     -> OpenExp env (PD Int) t
dual (endlab, nodemap) labelenv cont =
    trace ("\nlabelorder: " ++ show [labelLabel l | AnyLabel l <- labelorder]) $
    let sflt = TupSingle TypeFloat
        contribmap = DMap.singleton (fmapLabel D endlab) (AdjList (const [Const sflt 1.0]))
    in dualGate nodemap labelorder labelenv contribmap cont
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
-- This function is only written explicitly, and not merged into dual', so that
-- the 'a' type variable in the signature of dual' can be mentioned explicitly
-- in a type signature wrapping the definition of the 'contribution' variable
-- in dual'. This is necessary, because the 'contribution' variable _must_ have
-- a type signature for GHC to understand it, and that type signature would
-- mention 'a', which would not be mentioned anywhere yet had the current label
-- 'lbl' been extracted from 'labels' ad-hoc in a subexpression of dual'.
dualGate :: DMap (DLabel Int) (Exp Int)
         -> [AnyLabel Int]
         -> LabVal (PD Int) env
         -> DMap (DLabel (PD Int)) (AdjList (PD Int))
         -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) res)
         -> OpenExp env (PD Int) res
dualGate nodemap labels labelenv contribmap cont =
    case labels of
      [] ->
          cont labelenv
      AnyLabel lbl : restlabels ->
          dual' nodemap lbl restlabels labelenv contribmap cont

dual' :: forall a res env.
         DMap (DLabel Int) (Exp Int)
      -> DLabel Int a
      -> [AnyLabel Int]
      -> LabVal (PD Int) env
      -> DMap (DLabel (PD Int)) (AdjList (PD Int))
      -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) res)
      -> OpenExp env (PD Int) res
dual' nodemap lbl restlabels labelenv contribmap cont =
    case nodemap DMap.! lbl of
      -- Note that we normally aren't interested in the adjoint of a constant
      -- node -- seeing as it doesn't have any parents to contribute to.
      -- However, the AD parameter is injected as a constant node too, and we
      -- do need the parameter's adjoint, obviously.
      Const ty _ ->
          let adjoint = case contribmap DMap.! fmapLabel D lbl of
                          AdjList listgen -> fromJust $ expSum' ty (listgen labelenv)
          in Let adjoint (dualGate nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap cont)

      -- For the particular case of the arithmetic operators Add/Mul/Log/etc,
      -- the types are all forced to be explicitly Float anyway, so we can
      -- specify all types manually and thus don't need the trick from Note
      -- [dualGate split]. However, for consistency, we do it here too.
      PrimApp restype (A.PrimAdd argtype) (Label arglab) ->
          dual'Add nodemap lbl restype arglab restlabels labelenv contribmap cont

      PrimApp restype (A.PrimMul argtype) (Label arglab) ->
          dual'Mul nodemap lbl restype arglab restlabels labelenv contribmap cont

      PrimApp restype (A.PrimLog argtype) (Label arglab) ->
          dual'Log nodemap lbl restype arglab restlabels labelenv contribmap cont

      Pair restype (Label arglab1) (Label arglab2) ->
          dual'Pair nodemap lbl restype (arglab1, arglab2) restlabels labelenv contribmap cont

      -- The splitting up of the cases into separate functions here is for
      -- exactly the same reason as Note [dualGate split].
      -- App restype Fst (Label arglab) ->
      --     dual'Fst nodemap lbl restype arglab restlabels labelenv contribmap cont

      -- App restype Snd (Label arglab) ->
      --     dual'Snd nodemap lbl restype arglab restlabels labelenv contribmap cont

      expr -> trace ("\n!! " ++ show expr) undefined

-- TODO: More DRY code!
dual'Add  :: forall res env.
             DMap (DLabel Int) (Exp Int)
          -> DLabel Int Float
          -> TupleType Float
          -> DLabel Int (Float, Float)
          -> [AnyLabel Int]
          -> LabVal (PD Int) env
          -> DMap (DLabel (PD Int)) (AdjList (PD Int))
          -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) res)
          -> OpenExp env (PD Int) res
dual'Add nodemap lbl restype arglab restlabels labelenv contribmap cont =
      let adjoint = case contribmap DMap.! fmapLabel D lbl of
                      AdjList listgen -> fromJust $ expSum' restype (listgen labelenv)
          contribution :: LabVal (PD Int) env' -> OpenExp env' (PD Int) (Float, Float)
          contribution labelenv' =
              case labValFind labelenv' (fmapLabel D lbl) of
                Just adjidx ->
                    Pair (labelType arglab) (Var restype adjidx) (Var restype adjidx)
                _ -> error "dual' App Add: arg P and/or node D was not computed"
          contribmap' = addContribution (fmapLabel D arglab) contribution contribmap
      in Let adjoint (dualGate nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)

dual'Mul  :: forall res env.
             DMap (DLabel Int) (Exp Int)
          -> DLabel Int Float
          -> TupleType Float
          -> DLabel Int (Float, Float)
          -> [AnyLabel Int]
          -> LabVal (PD Int) env
          -> DMap (DLabel (PD Int)) (AdjList (PD Int))
          -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) res)
          -> OpenExp env (PD Int) res
dual'Mul nodemap lbl restype arglab restlabels labelenv contribmap cont =
      let adjoint = case contribmap DMap.! fmapLabel D lbl of
                      AdjList listgen -> fromJust $ expSum' restype (listgen labelenv)
          sflt = TupSingle TypeFloat
          contribution :: LabVal (PD Int) env' -> OpenExp env' (PD Int) (Float, Float)
          contribution labelenv' =
              case (labValFind labelenv' (fmapLabel P arglab), labValFind labelenv' (fmapLabel D lbl)) of
                (Just argidx, Just adjidx) ->
                    Pair (labelType arglab)
                         (App sflt Mul (Pair (labelType arglab) (Var restype adjidx)
                                                                (App sflt Snd (Var (labelType arglab) argidx))))
                         (App sflt Mul (Pair (labelType arglab) (Var restype adjidx)
                                                                (App sflt Fst (Var (labelType arglab) argidx))))
                _ -> error "dual' App Mul: arg P and/or node D was not computed"
          contribmap' = addContribution (fmapLabel D arglab) contribution contribmap
      in Let adjoint (dualGate nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)

dual'Log  :: forall res env.
             DMap (DLabel Int) (Exp Int)
          -> DLabel Int Float
          -> TupleType Float
          -> DLabel Int Float
          -> [AnyLabel Int]
          -> LabVal (PD Int) env
          -> DMap (DLabel (PD Int)) (AdjList (PD Int))
          -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) res)
          -> OpenExp env (PD Int) res
dual'Log nodemap lbl restype arglab restlabels labelenv contribmap cont =
    let adjoint = case contribmap DMap.! fmapLabel D lbl of
                    AdjList listgen -> fromJust $ expSum' restype (listgen labelenv)
        -- See Note [dualGate split]
        contribution :: LabVal (PD Int) env' -> OpenExp env' (PD Int) Float
        contribution labelenv' =
            case (labValFind labelenv' (fmapLabel P arglab), labValFind labelenv' (fmapLabel D lbl)) of
              (Just argidx, Just adjidx) ->
                  -- dE/dx = dE/d(log x) * d(log x)/dx = adjoint * 1/x = adjoint / x
                  App restype Div (Pair (TupPair restype restype) (Var restype adjidx)
                                                                  (Var (labelType arglab) argidx))
              _ -> error "dual' App Log: arg P and/or node D were not computed"
        contribmap' = addContribution (fmapLabel D arglab) contribution contribmap
    in Let adjoint (dualGate nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)

dual'Pair  :: forall a b res env.
              DMap (DLabel Int) (Exp Int)
           -> DLabel Int (a, b)
           -> TupleType (a, b)
           -> (DLabel Int a, DLabel Int b)
           -> [AnyLabel Int]
           -> LabVal (PD Int) env
           -> DMap (DLabel (PD Int)) (AdjList (PD Int))
           -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) res)
           -> OpenExp env (PD Int) res
dual'Pair nodemap lbl restype (arglab1, arglab2) restlabels labelenv contribmap cont =
    let adjoint = case contribmap DMap.! fmapLabel D lbl of
                    AdjList listgen -> fromJust $ expSum' restype (listgen labelenv)
        contributions :: LabVal (PD Int) env' -> (OpenExp env' (PD Int) a, OpenExp env' (PD Int) b)
        contributions labelenv' =
            case labValFind labelenv' (fmapLabel D lbl) of
              Just idx ->
                  (App (labelType arglab1) Fst (Var restype idx)
                  ,App (labelType arglab2) Snd (Var restype idx))
              _ -> error "dual' Pair: D was not computed"
        contribmap' = addContribution (fmapLabel D arglab1) (fst . contributions) $
                      addContribution (fmapLabel D arglab2) (snd . contributions) $
                      contribmap
    in Let adjoint (dualGate nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)
-}

-- dual'Fst  :: forall a b res env.
--              DMap (DLabel Int) (Exp Int)
--           -> DLabel Int a
--           -> TupleType a
--           -> DLabel Int (a, b)
--           -> [AnyLabel Int]
--           -> LabVal (PD Int) env
--           -> DMap (DLabel (PD Int)) (AdjList (PD Int))
--           -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) res)
--           -> OpenExp env (PD Int) res
-- dual'Fst nodemap lbl restype arglab restlabels labelenv contribmap cont =
--     case labelType arglab of
--       TupPair _ argtypeSnd ->
--           let adjoint = case contribmap DMap.! fmapLabel D lbl of
--                           AdjList listgen -> fromJust $ expSum' restype (listgen labelenv)
--               contribution :: LabVal (PD Int) env' -> OpenExp env' (PD Int) (a, b)
--               contribution labelenv' =
--                   case labValFind labelenv' (fmapLabel D lbl) of
--                     Just idx ->
--                         Pair (labelType arglab) (Var restype idx) (zeroForType argtypeSnd)
--                     _ -> error "dual' App Fst: D was not computed"
--               contribmap' = addContribution (fmapLabel D arglab) contribution contribmap
--           in Let adjoint (dualGate nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)
--       _ -> error "Impossible GADT"

-- dual'Snd  :: forall a b res env.
--              DMap (DLabel Int) (Exp Int)
--           -> DLabel Int b
--           -> TupleType b
--           -> DLabel Int (a, b)
--           -> [AnyLabel Int]
--           -> LabVal (PD Int) env
--           -> DMap (DLabel (PD Int)) (AdjList (PD Int))
--           -> (forall env'. LabVal (PD Int) env' -> OpenExp env' (PD Int) res)
--           -> OpenExp env (PD Int) res
-- dual'Snd nodemap lbl restype arglab restlabels labelenv contribmap cont =
--     case labelType arglab of
--       TupPair argtypeFst _ ->
--           let adjoint = case contribmap DMap.! fmapLabel D lbl of
--                           AdjList listgen -> fromJust $ expSum' restype (listgen labelenv)
--               contribution :: LabVal (PD Int) env' -> OpenExp env' (PD Int) (a, b)
--               contribution labelenv' =
--                   case labValFind labelenv' (fmapLabel D lbl) of
--                     Just idx ->
--                         Pair (labelType arglab) (zeroForType argtypeFst) (Var restype idx)
--                     _ -> error "dual' App Snd: D was not computed"
--               contribmap' = addContribution (fmapLabel D arglab) contribution contribmap
--           in Let adjoint (dualGate nodemap restlabels (LPush labelenv (fmapLabel D lbl)) contribmap' cont)
--       _ -> error "Impossible GADT"

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
    zeroForType :: s t -> OpenExp env lab t
    expPlus :: s t -> OpenExp env lab t -> OpenExp env lab t -> OpenExp env lab t

    expSum :: s t -> [OpenExp env lab t] -> OpenExp env lab t
    expSum ty [] = zeroForType ty
    expSum ty es = foldl1 (expPlus ty) es

class IsMaybeAdditive s where
    maybeZeroForType :: s t -> Maybe (OpenExp env lab t)
    maybeExpPlus :: s t -> OpenExp env lab t -> OpenExp env lab t -> Maybe (OpenExp env lab t)

    maybeExpSum :: s t -> [OpenExp env lab t] -> Maybe (OpenExp env lab t)
    maybeExpSum ty [] = maybeZeroForType ty
    maybeExpSum ty (expr:exprs) = go exprs expr
      where go [] accum = Just accum
            go (e:es) accum = maybeExpPlus ty accum e >>= go es

instance IsAdditive IntegralType where
    zeroForType ty = case ty of
        TypeInt -> Const (scalar TypeInt) 0
        TypeInt8 -> Const (scalar TypeInt8) 0
        TypeInt16 -> Const (scalar TypeInt16) 0
        TypeInt32 -> Const (scalar TypeInt32) 0
        TypeInt64 -> Const (scalar TypeInt64) 0
        TypeWord -> Const (scalar TypeWord) 0
        TypeWord8 -> Const (scalar TypeWord8) 0
        TypeWord16 -> Const (scalar TypeWord16) 0
        TypeWord32 -> Const (scalar TypeWord32) 0
        TypeWord64 -> Const (scalar TypeWord64) 0
      where scalar = SingleScalarType . NumSingleType . IntegralNumType

    expPlus ty e1 e2 =
      PrimApp (TupRsingle (scalar ty)) (A.PrimAdd (IntegralNumType ty))
              (Pair (TupRpair (TupRsingle (scalar ty)) (TupRsingle (scalar ty))) e1 e2)
      where scalar = SingleScalarType . NumSingleType . IntegralNumType

instance IsAdditive FloatingType where
    zeroForType ty = case ty of
        TypeHalf -> Const (flttype TypeHalf) 0
        TypeFloat -> Const (flttype TypeFloat) 0
        TypeDouble -> Const (flttype TypeDouble) 0
      where flttype = SingleScalarType . NumSingleType . FloatingNumType

    expPlus ty e1 e2 =
      PrimApp (TupRsingle (scalar ty)) (A.PrimAdd (FloatingNumType ty))
              (Pair (TupRpair (TupRsingle (scalar ty)) (TupRsingle (scalar ty))) e1 e2)
      where scalar = SingleScalarType . NumSingleType . FloatingNumType

instance IsAdditive NumType where
    zeroForType (IntegralNumType t) = zeroForType t
    zeroForType (FloatingNumType t) = zeroForType t

    expPlus ty e1 e2 =
      PrimApp (TupRsingle (scalar ty)) (A.PrimAdd ty)
              (Pair (TupRpair (TupRsingle (scalar ty)) (TupRsingle (scalar ty))) e1 e2)
      where scalar = SingleScalarType . NumSingleType

instance IsMaybeAdditive SingleType where
    maybeZeroForType (NumSingleType t) = Just (zeroForType t)
    maybeZeroForType (NonNumSingleType _) = Nothing

    maybeExpPlus (NumSingleType ty) e1 e2 = Just (expPlus ty e1 e2)
    maybeExpPlus (NonNumSingleType _) _ _ = Nothing

instance IsMaybeAdditive ScalarType where
    maybeZeroForType (SingleScalarType t) = maybeZeroForType t
    maybeZeroForType (VectorScalarType _) = Nothing

    maybeExpPlus (SingleScalarType ty) e1 e2 = maybeExpPlus ty e1 e2
    maybeExpPlus (VectorScalarType _) _ _ = Nothing

instance IsMaybeAdditive TupleType where
    maybeZeroForType TupRunit = Just Nil
    maybeZeroForType (TupRsingle t) = maybeZeroForType t
    maybeZeroForType (TupRpair t1 t2) =
        Pair (TupRpair t1 t2) <$> maybeZeroForType t1 <*> maybeZeroForType t2

    maybeExpPlus ty e1 e2 = tupleZip ty maybeExpPlus e1 e2

-- Errors if any parents are not Label nodes, or if called on a Let or Var node.
expLabelParents :: OpenExp env lab t -> [AnyLabel lab]
expLabelParents = \case
    Const _ _ -> []
    PrimApp _ _ e -> [fromLabel e]
    Pair _ e1 e2 -> [fromLabel e1, fromLabel e2]
    Nil -> []
    Get _ e -> [fromLabel e]
    Let _ _ _ -> unimplemented "Let"
    Var _ -> unimplemented "Var"
    Label _ -> unimplemented "Label"
  where
    unimplemented name =
        error ("expLabelParents: Unimplemented for " ++ name ++ ", semantics unclear")
    fromLabel (Label lbl) = AnyLabel lbl
    fromLabel _ = error ("expLabelParents: Parent is not a label")
