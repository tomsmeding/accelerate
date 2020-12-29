{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Array.Accelerate.Trafo.AD.Common where

import Control.Monad.State.Strict
import Data.Char (isDigit)
import Data.List (intercalate, sortOn, foldl')
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Sum (DSum(..))
import Data.Functor.Product (Product)
import qualified Data.Functor.Product as Product
import Data.GADT.Compare
import Data.GADT.Show
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Some (Some, pattern Some, mkSome, mapSome)
import Data.Typeable ((:~:)(Refl))
import Data.Void
import GHC.Stack (HasCallStack)

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Analysis.Match (matchScalarType, matchArrayR, matchTupR)
import Data.Array.Accelerate.Representation.Array hiding ((!!))
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Var (DeclareVars(..), declareVars)
import Data.Array.Accelerate.Type


data TagVal s env where
    TEmpty :: TagVal s ()
    TPush :: TagVal s env -> s t -> TagVal s (env, t)

-- TODO: type LabVal lty s lab = TagVal (DLabel lty s lab)
data LabVal lty s lab env where
    LEmpty :: LabVal lty s lab ()
    LPush :: LabVal lty s lab env -> DLabel lty s lab t -> LabVal lty s lab (env, t)

data PartialVal s topenv env where
    PTEmpty :: PartialVal s topenv topenv
    PTPush :: PartialVal s topenv env -> s t -> PartialVal s topenv (env, t)

-- This avoids a lot of -Wunticked-promoted-constructors.
data LabelType = NodeLabel_ | EnvLabel_
type NodeLabel = 'NodeLabel_
type EnvLabel = 'EnvLabel_

data DLabel (lty :: LabelType) s lab t =
    DLabel { labelType :: s t
           , labelLabel :: lab }
  deriving (Show)

-- The type of a labelenv, which consists of single-typed environment labels.
type ELabVal = LabVal EnvLabel ScalarType
type ALabVal = LabVal EnvLabel ArrayR

-- Normal environment labels, which are single-typed.
type EDLabel = DLabel EnvLabel ScalarType
type ADLabel = DLabel EnvLabel ArrayR

-- Node labels are generally of tuple type, though sometimes we also need node
-- labels in single-type form: explode deals with these due to destructuring
-- let-bindings, and array labels embedded in expressions (to replace an array
-- variable reference) are also of such type.
type EDLabelN = DLabel NodeLabel TypeR
type EDLabelNS = DLabel NodeLabel ScalarType
type ADLabelN = DLabel NodeLabel ArraysR
type ADLabelNS = DLabel NodeLabel ArrayR

-- A PartLabel is used to refer to an element of the tuple that the full label points to.
data PartLabel lty s lab t t' = PartLabel (DLabel lty s lab t) (TupleIdx t t')
  deriving (Show)

type EPartLabelN = PartLabel NodeLabel TypeR
type APartLabelN = PartLabel NodeLabel ArraysR

-- Existentialises the "large type" parameter of a PartLabel.
data AnyPartLabel lty s lab t' = forall t. AnyPartLabel (PartLabel lty s lab t t')

type EAnyPartLabelN = AnyPartLabel NodeLabel TypeR
type AAnyPartLabelN = AnyPartLabel NodeLabel ArraysR

deriving instance (Show lab, forall t. Show (s t)) => Show (AnyPartLabel lty s lab t')

partLabelLargeType :: PartLabel lty s lab t t' -> s t
partLabelLargeType (PartLabel lab _) = labelType lab

partLabelSmallType :: PartLabel lty (TupR s) lab t t' -> TupR s t'
partLabelSmallType (PartLabel lab tidx) = pickTupR tidx (labelType lab)

instance (Eq lab, GEq s) => GEq (AnyPartLabel lty s lab) where
    geq (AnyPartLabel (PartLabel lab tidx)) (AnyPartLabel (PartLabel lab' tidx'))
      | Just Refl <- geq lab lab'
      , Just Refl <- geq tidx tidx'
      = Just Refl
      | otherwise
      = Nothing

instance (Ord lab, GCompare s) => GCompare (AnyPartLabel lty s lab) where
    gcompare (AnyPartLabel (PartLabel lab tidx)) (AnyPartLabel (PartLabel lab' tidx')) =
        case gcompare lab lab' of
          GEQ -> case gcompare tidx tidx' of
                   GEQ -> GEQ
                   r -> r
          GLT -> GLT
          GGT -> GGT


-- Convenience function like 'scalarType', except for tuple types
class IsTuple t where tupleType :: TypeR t
instance {-# OVERLAPPING #-} IsTuple () where tupleType = TupRunit
instance {-# OVERLAPPING #-} (IsTuple a, IsTuple b) => IsTuple (a, b) where tupleType = TupRpair tupleType tupleType
instance {-# OVERLAPPABLE #-} IsScalar t => IsTuple t where tupleType = TupRsingle scalarType

-- Convenience function like 'scalarType', except for non-label labels
scalarLabel :: IsScalar t => DLabel lty ScalarType () t
scalarLabel = DLabel scalarType ()

-- Convenience function like 'scalarLabel', except for tuple types
magicLabel :: IsTuple t => DLabel lty TypeR () t
magicLabel = DLabel tupleType ()

nilLabel :: s t -> DLabel lty s () t
nilLabel ty = DLabel ty ()


class    IsTupleType scalar s              where toTupleType :: s t -> TupR scalar t
instance IsTupleType ScalarType TypeR      where toTupleType = id
instance IsTupleType ScalarType ScalarType where toTupleType = TupRsingle
instance IsTupleType ArrayR ArraysR where toTupleType = id
instance IsTupleType ArrayR ArrayR  where toTupleType = TupRsingle

-- Only allowed for node labels, since env labels can only usefully refer to
-- non-tuple values due to mandatory let-destructuring. This restriction is not
-- syntactically necessary, but semantically it might prevent mishaps.
tupleLabel :: IsTupleType scalar s => DLabel NodeLabel s lab t -> DLabel NodeLabel (TupR scalar) lab t
tupleLabel (DLabel ty lab) = DLabel (toTupleType ty) lab

-- Same as tupleLabel, but for if you know you have a scalar label in hand.
tupleLabel' :: DLabel NodeLabel s lab t -> DLabel NodeLabel (TupR s) lab t
tupleLabel' (DLabel ty lab) = DLabel (TupRsingle ty) lab



instance Show lab => GShow (DLabel lty TypeR      lab) where gshowsPrec = showsPrec
instance Show lab => GShow (DLabel lty ScalarType lab) where gshowsPrec = showsPrec
instance Show lab => GShow (DLabel lty ArraysR    lab) where gshowsPrec = showsPrec
instance Show lab => GShow (DLabel lty ArrayR     lab) where gshowsPrec = showsPrec

instance (Eq lab, GEq s) => GEq (DLabel lty s lab) where
    geq (DLabel ty1 lab1) (DLabel ty2 lab2)
      | lab1 == lab2 = case geq ty1 ty2 of
                         Just Refl -> Just Refl
                         Nothing -> error "GEq DLabel: Labels match but types differ"
      | otherwise = Nothing

instance (Ord lab, GCompare s) => GCompare (DLabel lty s lab) where
    gcompare (DLabel ty1 lab1) (DLabel ty2 lab2) =
        case compare lab1 lab2 of
          LT -> GLT
          GT -> GGT
          EQ | GEQ <- gcompare ty1 ty2 -> GEQ
             | otherwise -> error "GCompare DLabel: Labels match but types differ"

data TupleIdx t t' where
    TIHere  :: TupleIdx s s
    TILeft  :: TupleIdx a t -> TupleIdx (a, b) t
    TIRight :: TupleIdx b t -> TupleIdx (a, b) t

deriving instance Show (TupleIdx t t')

instance GEq (TupleIdx t) where
    geq tidx tidx' | GEQ <- gcompare tidx tidx' = Just Refl
                   | otherwise = Nothing

instance GCompare (TupleIdx t) where
    gcompare TIHere TIHere = GEQ
    gcompare (TILeft tidx) (TILeft tidx') = gcompare tidx tidx'
    gcompare (TIRight tidx) (TIRight tidx') = gcompare tidx tidx'
    gcompare TIHere _ = GLT
    gcompare _ TIHere = GGT
    gcompare (TILeft _) _ = GLT
    gcompare _ (TILeft _) = GGT

-- TODO: move to Shows
showScalar :: ScalarType t -> t -> String
showScalar = \topty -> case topty of
    SingleScalarType ty -> showSingle ty
    VectorScalarType _ -> const "[vector?]"
  where
    showSingle :: SingleType t -> t -> String
    showSingle (NumSingleType ty) = showNum ty

    showNum :: NumType t -> t -> String
    showNum (IntegralNumType ty) = showIntegral ty
    showNum (FloatingNumType ty) = showFloating ty

    showIntegral :: IntegralType t -> t -> String
    showIntegral TypeInt = show
    showIntegral TypeInt8 = show
    showIntegral TypeInt16 = show
    showIntegral TypeInt32 = show
    showIntegral TypeInt64 = show
    showIntegral TypeWord = show
    showIntegral TypeWord8 = show
    showIntegral TypeWord16 = show
    showIntegral TypeWord32 = show
    showIntegral TypeWord64 = show

    showFloating :: FloatingType t -> t -> String
    showFloating TypeHalf = show
    showFloating TypeFloat = show
    showFloating TypeDouble = show

showTupR :: (forall t'. s t' -> String) -> TupR s t -> String
showTupR _ TupRunit       = "()"
showTupR s (TupRsingle t) = s t
showTupR s (TupRpair a b) = "(" ++ showTupR s a ++ "," ++ showTupR s b ++")"

showTupR' :: (forall t'. s t' -> t' -> String) -> TupR s t -> t -> String
showTupR' _ TupRunit () = "()"
showTupR' f (TupRsingle ty) s = f ty s
showTupR' f (TupRpair t1 t2) (a, b) =
    "(" ++ showTupR' f t1 a ++ ", " ++ showTupR' f t2 b ++ ")"

showDLabel :: (Show (s t), Show lab) => DLabel lty s lab t -> String
showDLabel (DLabel ty lab) =
    let labshow = show lab
    in if all isDigit labshow
           then "L" ++ labshow ++ " :: " ++ show ty
           else labshow ++ " :: " ++ show ty

data ShowEnv eenv lab alab =
    ShowEnv { seLabf :: lab -> String
            , seAlabf :: alab -> String
            , seSeed :: Int
            , seEnv :: eenv
            , seAenv :: [String] }

type EShowEnv = ShowEnv [String]
type AShowEnv = ShowEnv ()

fmapTupR :: (forall t'. s t' -> s' t') -> TupR s t -> TupR s' t
fmapTupR _ TupRunit = TupRunit
fmapTupR f (TupRsingle x) = TupRsingle (f x)
fmapTupR f (TupRpair t1 t2) = TupRpair (fmapTupR f t1) (fmapTupR f t2)

enumerateTupR :: TupR s t -> [Some s]
enumerateTupR TupRunit = []
enumerateTupR (TupRsingle x) = [mkSome x]
enumerateTupR (TupRpair t1 t2) = enumerateTupR t1 ++ enumerateTupR t2

joinTupR :: TupR (TupR s) t -> TupR s t
joinTupR TupRunit = TupRunit
joinTupR (TupRsingle t) = t
joinTupR (TupRpair t1 t2) = TupRpair (joinTupR t1) (joinTupR t2)

tupleIndices :: TupR s t -> TupR (TupleIdx t) t
tupleIndices = \tup -> go tup TIHere
  where
    go :: TupR s t -> TupleIdx top t -> TupR (TupleIdx top) t
    go TupRunit _ = TupRunit
    go (TupRsingle _) tidx = TupRsingle tidx
    go (TupRpair t1 t2) tidx = TupRpair (go t1 (insertFst tidx)) (go t2 (insertSnd tidx))

zipWithTupR :: (forall t'. s1 t' -> s2 t' -> s t') -> TupR s1 t -> TupR s2 t -> TupR s t
zipWithTupR _ TupRunit TupRunit = TupRunit
zipWithTupR f (TupRsingle a) (TupRsingle b) = TupRsingle (f a b)
zipWithTupR f (TupRpair a1 a2) (TupRpair b1 b2) = TupRpair (zipWithTupR f a1 b1) (zipWithTupR f a2 b2)
zipWithTupR _ _ _ = error "impossible GADTs"

zipWithTupRcombine :: a -> (a -> a -> a) -> (forall t'. s1 t' -> s2 t' -> a) -> TupR s1 t -> TupR s2 t -> a
zipWithTupRcombine z _ _ TupRunit TupRunit = z
zipWithTupRcombine _ _ f (TupRsingle a) (TupRsingle b) = f a b
zipWithTupRcombine z c f (TupRpair a1 a2) (TupRpair b1 b2) =
    c (zipWithTupRcombine z c f a1 b1) (zipWithTupRcombine z c f a2 b2)
zipWithTupRcombine _ _ _ _ _ = error "Impossible GADTs"

zipTupRmap :: (HasCallStack, GCompare s1) => TupR s1 t -> TupR s2 t -> DMap s1 s2
zipTupRmap = zipWithTupRcombine mempty (DMap.unionWithKey (error "Overlapping keys in zipTupRmap")) DMap.singleton

prjT :: Idx env t -> TagVal s env -> s t
prjT ZeroIdx (TPush _ x) = x
prjT (SuccIdx idx) (TPush env _) = prjT idx env

prjL :: Idx env t -> LabVal lty s lab env -> DLabel lty s lab t
prjL ZeroIdx (LPush _ x) = x
prjL (SuccIdx idx) (LPush env _) = prjL idx env

mapLabVal :: (lab -> lab') -> LabVal lty s lab env -> LabVal lty s lab' env
mapLabVal _ LEmpty = LEmpty
mapLabVal f (LPush env (DLabel ty lab)) = LPush (mapLabVal f env) (DLabel ty (f lab))

labValContains :: Eq lab => LabVal lty s lab env -> lab -> Bool
labValContains LEmpty _ = False
labValContains (LPush env (DLabel _ lab)) x =
    x == lab || labValContains env x

uniqueLabVal :: Eq lab => LabVal lty s lab env -> Bool
uniqueLabVal LEmpty = True
uniqueLabVal (LPush env (DLabel _ lab)) =
    not (labValContains env lab) && uniqueLabVal env

fmapLabel :: (lab -> lab') -> DLabel lty s lab t -> DLabel lty s lab' t
fmapLabel f (DLabel ty lab) = DLabel ty (f lab)

pickTupR :: TupleIdx t t' -> TupR s t -> TupR s t'
pickTupR TIHere tup = tup
pickTupR (TILeft path) (TupRpair tup _) = pickTupR path tup
pickTupR (TIRight path) (TupRpair _ tup) = pickTupR path tup
pickTupR _ _ = error "pickTupR: impossible GADTs"

-- Used for showing expressions
namifyLHS :: Int -> LeftHandSide s v env env' -> (String, [String], Int)
namifyLHS seed (LeftHandSideSingle _) =
    let n = if seed < 26 then [['a'..'z'] !! seed] else 't' : show (seed - 25)
    in (n, [n], seed + 1)
namifyLHS seed (LeftHandSideWildcard _) = ("_", [], seed)
namifyLHS seed (LeftHandSidePair lhs1 lhs2) =
    let (descr1, descrs1, seed1) = namifyLHS seed lhs1
        (descr2, descrs2, seed2) = namifyLHS seed1 lhs2
    in ("(" ++ descr1 ++ ", " ++ descr2 ++ ")", descrs2 ++ descrs1,seed2)

-- TODO: this is linear, making repeated use of smartFst etc quadratic
composeTIdx :: TupleIdx t1 t2 -> TupleIdx t2 t3 -> TupleIdx t1 t3
composeTIdx TIHere ti = ti
composeTIdx (TILeft ti) ti' = TILeft (composeTIdx ti ti')
composeTIdx (TIRight ti) ti' = TIRight (composeTIdx ti ti')

insertFst :: TupleIdx t (t1, t2) -> TupleIdx t t1
insertFst ti = composeTIdx ti (TILeft TIHere)

insertSnd :: TupleIdx t (t1, t2) -> TupleIdx t t2
insertSnd ti = composeTIdx ti (TIRight TIHere)

data TuplifyWithTrace b f = forall t. TuplifyWithTrace (TupR f t) [(b, Some (Product f (TupleIdx t)))]

-- This function is ridiculously generic for not really a good reason.
tuplify' :: Ord b => [a] -> (a -> Some f) -> (a -> b) -> TuplifyWithTrace b f
tuplify' values toF toKey =
    foldl' (\(TuplifyWithTrace tup traces) value ->
                 case toF value of
                   Some x ->
                       let newTrace = (toKey value, Some (Product.Pair x (TIRight TIHere)))
                       in TuplifyWithTrace (TupRpair tup (TupRsingle x))
                                           (newTrace : map (fmap (mapSome (mapProductSnd TILeft))) traces))
           (TuplifyWithTrace TupRunit [])
           values

tuplify :: [Some f] -> Some (TupR f)
tuplify l | TuplifyWithTrace tup _ <- tuplify' l id (const ()) = Some tup

-- TODO: apply this trick in more places where we _know_ it's not a tuple based on the type information
untupleA :: TupR s (Array sh t) -> s (Array sh t)
untupleA (TupRsingle x) = x


newtype IdGen a = IdGen (State Int a)
  deriving (Functor, Applicative, Monad, MonadState Int)

evalIdGen :: IdGen a -> a
evalIdGen (IdGen s) = evalState s 1

genId' :: s t -> IdGen (DLabel lty s Int t)
genId' ty = state (\s -> (DLabel ty s, succ s))

-- The restriction to env labels is not syntactically necessary, but
-- semantically it generally doesn't make sense to push a tuple of node labels.
-- Hence to prevent mishaps, this function is specialised to EnvLabel.
lpushLabTup :: LeftHandSide s t env env' -> TupR (DLabel EnvLabel s lab) t -> LabVal EnvLabel s lab env -> LabVal EnvLabel s lab env'
lpushLabTup (LeftHandSideWildcard _) _ labelenv = labelenv
lpushLabTup (LeftHandSideSingle _) (TupRsingle lab) labelenv = LPush labelenv lab
lpushLabTup (LeftHandSidePair lhs1 lhs2) (TupRpair labs1 labs2) labelenv =
    lpushLabTup lhs2 labs2 (lpushLabTup lhs1 labs1 labelenv)
lpushLabTup _ _ _ = error "lpushLabTup: impossible GADTs"

lpushLHS_parts :: TagVal (AnyPartLabel NodeLabel (TupR s) Int) env -> DLabel NodeLabel (TupR s) Int tfull -> TupleIdx tfull t -> LeftHandSide s t env env' -> TagVal (AnyPartLabel NodeLabel (TupR s) Int) env'
lpushLHS_parts env' referLab ti (LeftHandSidePair lhs1 lhs2) =
    lpushLHS_parts (lpushLHS_parts env' referLab (insertFst ti) lhs1) referLab (insertSnd ti) lhs2
lpushLHS_parts env' referLab ti (LeftHandSideSingle _) =
    TPush env' (AnyPartLabel (PartLabel referLab ti))
lpushLHS_parts env' _ _ (LeftHandSideWildcard _) = env'


class Matchable s where
    matchMatchable :: s t -> s t' -> Maybe (t :~: t')
instance Matchable ScalarType where matchMatchable = matchScalarType
instance Matchable ArrayR     where matchMatchable = matchArrayR
instance Matchable s => Matchable (TupR s) where
    matchMatchable = matchTupR matchMatchable

labValFind :: (Matchable s, Show (s t), Eq lab, Show lab) => LabVal lty s lab env -> DLabel lty s lab t -> Maybe (Var s env t)
labValFind LEmpty _ = Nothing
labValFind (LPush env (DLabel ty lab)) target@(DLabel ty2 lab2)
  | lab == lab2 = case matchMatchable ty ty2 of
                    Just Refl -> Just (Var ty ZeroIdx)
                    _ -> error $ "labValFind: label " ++ showDLabel target ++ " found but has wrong type"
  | otherwise = (\(Var ty' idx) -> Var ty' (SuccIdx idx)) <$> labValFind env target

labValFinds :: (Matchable s, forall t'. Show (s t'), Eq lab, Show lab) => LabVal lty s lab env -> TupR (DLabel lty s lab) t -> Maybe (Vars s env t)
labValFinds _ TupRunit = Just TupRunit
labValFinds labelenv (TupRsingle lab) = TupRsingle <$> labValFind labelenv lab
labValFinds labelenv (TupRpair labs1 labs2) =
    TupRpair <$> labValFinds labelenv labs1 <*> labValFinds labelenv labs2

resolveEnvLab :: (HasCallStack, forall t'. Show (s t'), Eq lab, Show lab, Matchable s) => Context s tag lab env -> DLabel EnvLabel s lab t -> Var s env t
resolveEnvLab (Context labelenv _) lab
  | Just var <- labValFind labelenv lab = var
  | otherwise = error $ "resolveEnvLab: not found: " ++ showDLabel lab

resolveEnvLabs :: (HasCallStack, forall t'. Show (s t'), Eq lab, Show lab, Matchable s) => Context s tag lab env -> TupR (DLabel EnvLabel s lab) t -> Vars s env t
resolveEnvLabs (Context labelenv _) labs
  | Just vars <- labValFinds labelenv labs = vars
  | otherwise = error $ "resolveEnvLabs: not found: " ++ showTupR showDLabel labs


pvalPushLHS :: LeftHandSide s t env env' -> PartialVal s topenv env -> PartialVal s topenv env'
pvalPushLHS (LeftHandSideWildcard _) tv = tv
pvalPushLHS (LeftHandSideSingle sty) tv = PTPush tv sty
pvalPushLHS (LeftHandSidePair lhs1 lhs2) tv = pvalPushLHS lhs2 (pvalPushLHS lhs1 tv)


indexIntoLHS :: LeftHandSide s t env env' -> TupleIdx t t' -> Maybe (Idx env' t')
indexIntoLHS (LeftHandSideWildcard _) _ = Nothing  -- ignored or out of scope
indexIntoLHS (LeftHandSideSingle _) TIHere = Just ZeroIdx
indexIntoLHS (LeftHandSideSingle _) _ = Nothing  -- out of scope
indexIntoLHS (LeftHandSidePair lhs1 lhs2) (TILeft ti) =
    (weakenWithLHS lhs2 >:>) <$> indexIntoLHS lhs1 ti
indexIntoLHS (LeftHandSidePair _ lhs2) (TIRight ti) = indexIntoLHS lhs2 ti
indexIntoLHS (LeftHandSidePair _ _) TIHere =
    error "indexIntoLHS: TupleIdx doesn't point to a scalar"


-- TODO: Is PDAux actually used anywhere? If not, remove the constructor and the other Aux stuff
data PD tag a = P !a | D !a | PDAux !tag !a
  deriving (Show, Eq, Ord)

type PDAuxTagExp = Void
data PDAuxTagAcc = TmpTup
  deriving (Show, Eq, Ord)

type PDExp = PD PDAuxTagExp
type PDAcc = PD PDAuxTagAcc

type BindMap s tag lab =
    DMap (CMapKey s (PD tag lab))
         (TupR (DLabel EnvLabel s lab))
type EBindMap lab = BindMap ScalarType PDAuxTagExp lab
type ABindMap lab = BindMap ArrayR PDAuxTagAcc lab

-- Expression node labels are of tuple type and have a PD tag; environment
-- labels are of scalar type and have no tag.
-- The labelenv recalls the environment of let-bound variables with environment
-- labels; the bindmap maps node labels to the tuple of environment labels
-- indicating where its value is stored.
data Context s tag lab env = Context (LabVal EnvLabel s lab env) (BindMap s tag lab)

type EContext = Context ScalarType PDAuxTagExp
type AContext = Context ArrayR PDAuxTagAcc

showContext :: (Ord lab, Show lab, Show tag, Ord tag, forall t. Show (s t), forall t. Show (TupR s t))
            => Context s tag lab aenv -> String
showContext (Context labelenv bindmap) = "Context " ++ showLabelenv labelenv ++ " " ++ showBindmap bindmap

showLabelenv :: (Show lab, forall t. Show (s t)) => LabVal lty s lab aenv -> String
showLabelenv LEmpty = "[]"
showLabelenv (LPush env lab) = "[" ++ go env ++ showDLabel lab ++ "]"
  where
    go :: (Show lab, forall t. Show (s t)) => LabVal lty s lab aenv -> String
    go LEmpty = ""
    go (LPush env' lab') = go env' ++ showDLabel lab' ++ ", "

showBindmap :: (Ord lab, Show lab, Show tag, Ord tag, forall t. Show (s t), forall t. Show (TupR s t))
            => BindMap s tag lab -> String
showBindmap bindmap =
    let tups = sortOn fst [(sortKey, (showCMapKey showDLabel dlab, showTupR showDLabel labs))
                          | dlab :=> labs <- DMap.assocs bindmap
                          , let sortKey = case dlab of Argument _ -> Nothing
                                                       Local (DLabel _ lab) -> Just lab]
        s = intercalate ", " ["(" ++ dlabshow ++ ") :=> " ++ labsshow
                             | (_, (dlabshow, labsshow)) <- tups]
    in "[" ++ s ++ "]"

showCMap :: (forall t'. Show (TupR s t')) => DMap (CMapKey s Int) f -> String
showCMap mp = "[" ++ intercalate ", " [showCMapKey showDLabel k ++ " :=> {\\...}" | Some k <- DMap.keys mp] ++ "]"

showProduct :: (forall t'. f t' -> String) -> (forall t'. g t' -> String) -> Product f g t -> String
showProduct fs gs (Product.Pair a b) = "Product (" ++ fs a ++ ") (" ++ gs b ++ ")"

filterBindmap :: (Matchable s, GCompare s, GCompare (TupR s), Ord tag, Ord lab)
              => [Some (DLabel NodeLabel (TupR s) (PD tag lab))]
              -> BindMap s tag lab
              -> BindMap s tag lab
filterBindmap labs bm = DMap.fromList [Local lab :=> bm DMap.! Local lab | Some lab <- labs]

reassignBindmap :: (GCompare s, Ord lab)
                => TupR (DLabel EnvLabel s lab) t
                -> TupR (DLabel EnvLabel s lab) t
                -> BindMap s tag lab
                -> BindMap s tag lab
reassignBindmap old new =
    let oldnew = DMap.fromList
            [l1 :=> l2
            | Some (Product.Pair l1 l2) <-
                  enumerateTupR (zipWithTupR Product.Pair old new)]
    in DMap.map (fmapTupR (\lab -> fromMaybe lab (DMap.lookup lab oldnew)))

reassignLabelmap :: (GCompare s, Ord lab)
                 => TupR (DLabel EnvLabel s lab) t
                 -> TupR (DLabel EnvLabel s lab) t
                 -> Map.Map k [Some (DLabel EnvLabel s lab)]
                 -> Map.Map k [Some (DLabel EnvLabel s lab)]
reassignLabelmap old new =
    let oldnew = DMap.fromList
            [l1 :=> l2
            | Some (Product.Pair l1 l2) <-
                  enumerateTupR (zipWithTupR Product.Pair old new)]
    in fmap (map (\(Some lab) -> Some (fromMaybe lab (DMap.lookup lab oldnew))))

dmapDisjointUnions :: (HasCallStack, GCompare k) => [DMap k v] -> DMap k v
dmapDisjointUnions =
    DMap.unionsWithKey (error "dmapDisjointUnions: overlapping entries")

ctxPushS :: (Matchable s, Ord tag, GCompare s, GCompare (TupR s))
         => DLabel NodeLabel s (PD tag Int) t -> DLabel EnvLabel s Int t -> Context s tag Int env -> Context s tag Int (env, t)
ctxPushS nodelab envlab =
    ctxPush (LeftHandSideSingle (labelType nodelab)) (tupleLabel' nodelab) (TupRsingle envlab)

ctxPush :: (Matchable s, Ord tag, GCompare s, GCompare (TupR s))
        => LeftHandSide s t env env' -> DLabel NodeLabel (TupR s) (PD tag Int) t -> TupR (DLabel EnvLabel s Int) t -> Context s tag Int env -> Context s tag Int env'
ctxPush lhs nodelab envlabs (Context labelenv bindmap) =
    Context (lpushLabTup lhs envlabs labelenv) (DMap.insert (Local nodelab) envlabs bindmap)

ctxPushEnvOnly :: (Ord tag, GCompare s, GCompare (TupR s))
        => LeftHandSide s t env env' -> TupR (DLabel EnvLabel s Int) t -> Context s tag Int env -> Context s tag Int env'
ctxPushEnvOnly lhs envlabs (Context labelenv bindmap) = Context (lpushLabTup lhs envlabs labelenv) bindmap

ctxPushSEnvOnly :: (Ord tag, GCompare s, GCompare (TupR s))
                => DLabel EnvLabel s Int t -> Context s tag Int env -> Context s tag Int (env, t)
ctxPushSEnvOnly envlab = ctxPushEnvOnly (LeftHandSideSingle (labelType envlab)) (TupRsingle envlab)

-- Find the primal of a node in the bindmap
findPrimalBMap :: (HasCallStack, IsTupleType s s_lab, Matchable s, GCompare s, GCompare (TupR s), Show lab, Ord lab, Ord tag)
               => Context s tag lab env
               -> DLabel NodeLabel s_lab lab t
               -> TupR (DLabel EnvLabel s lab) t
findPrimalBMap (Context _ bindmap) lbl =
    fromMaybe (error ("findPrimalBMap: not found: L" ++ show (labelLabel lbl)))
              (DMap.lookup (Local (fmapLabel P (tupleLabel lbl))) bindmap)

findArgumentPrimalBMap :: (HasCallStack, Matchable s, GCompare s, GCompare (TupR s), Ord lab, Ord tag)
                       => Context s tag lab env
                       -> TupR s args
                       -> TupR (DLabel EnvLabel s lab) args
findArgumentPrimalBMap (Context _ bindmap) argsty =
    fromMaybe (error "findArgumentPrimalBMap: not found")
              (DMap.lookup (Argument argsty) bindmap)

-- Find the adjoint of a node in the bindmap
findAdjointBMap :: (HasCallStack, IsTupleType s s_lab, Matchable s, GCompare s, GCompare (TupR s), Show lab, Ord lab, Ord tag)
                => Context s tag lab env
                -> DLabel NodeLabel s_lab lab t
                -> TupR (DLabel EnvLabel s lab) t
findAdjointBMap ctx lbl =
    fromMaybe (error ("findAdjointBMap: not found: L" ++ show (labelLabel lbl)))
              (findAdjointBMap' ctx lbl)

-- Find the adjoint of a node in the bindmap, optionally
findAdjointBMap' :: (IsTupleType s s_lab, Matchable s, GCompare s, GCompare (TupR s), Ord lab, Ord tag)
                 => Context s tag lab env
                 -> DLabel NodeLabel s_lab lab t
                 -> Maybe (TupR (DLabel EnvLabel s lab) t)
findAdjointBMap' (Context _ bindmap) lbl = DMap.lookup (Local (fmapLabel D (tupleLabel lbl))) bindmap


-- TODO: make this 'type AnyLabel lty s lab = Exists (DLabel lty s lab)', and perhaps even inline this because then the typedef is marginally useful. Also apply this to other Any* names.
-- (But consider the specialised Eq/Ord instances below. Can we reproduce that with an Exists version?)
-- Yes we can! Some uses GEq and GCompare for its Eq and Ord instances, and because DLabel acts correctly, that should work.
data AnyLabel lty s lab = forall t. AnyLabel (DLabel lty s lab t)

type EAnyLabel = AnyLabel EnvLabel ScalarType
type EAnyLabelN = AnyLabel NodeLabel TypeR
type AAnyLabel = AnyLabel EnvLabel ArrayR
type AAnyLabelN = AnyLabel NodeLabel ArraysR
type AAnyLabelNS = AnyLabel NodeLabel ArrayR

instance (Eq lab, GEq s) => Eq (AnyLabel lty s lab) where
    AnyLabel (DLabel ty1 lab1) == AnyLabel (DLabel ty2 lab2)
      | lab1 /= lab2 = False
      | Just Refl <- geq ty1 ty2 = True
      | otherwise = error "Eq AnyLabel: labels match, but types do not!"

instance (Ord lab, GCompare s) => Ord (AnyLabel lty s lab) where
    compare (AnyLabel (DLabel ty1 lab1)) (AnyLabel (DLabel ty2 lab2)) =
        case compare lab1 lab2 of
          LT -> LT
          GT -> GT
          EQ | GEQ <- gcompare ty1 ty2 -> EQ
             | otherwise -> error "Ord AnyLabel: labels match, but types do not!"

deriving instance (Show lab, forall t. Show (s t)) => Show (AnyLabel lty s lab)


data EnvCapture s tag env lab =
    forall tmp.
        EnvCapture -- Collects temporaries into a tuple
                   (Vars s env tmp)
                   -- Consumes the tuple and reproduces the labels in a new let-environment
                   (EnvInstantiator s tag lab tmp)

-- Given a new context, and pointers into that context reconstructing the temp
-- tuple, returns a new bindmap that binds the previous tuple labels to the new
-- locations.
-- Precondition: the given context must contain all scalar labels that were in
-- the non-captured part of the environment used to construct the EnvCapture.
data EnvInstantiator s tag lab tmp =
    EnvInstantiator (forall env1.
                     Context s tag lab env1
                  -> Vars s env1 tmp
                  -> BindMap s tag lab)

captureEnvironmentSlice :: (Matchable s, GCompare s, GCompare (TupR s), Ord tag) => Context s tag Int topenv -> Context s tag Int env -> EnvCapture s tag env Int
captureEnvironmentSlice (Context toplabelenv topbindmap) (Context origlabelenv origbindmap)
  | let barrierLab = case toplabelenv of
                       LEmpty -> Nothing
                       LPush _ lab -> Just (AnyLabel lab)
  , Exists origpairs <- collect barrierLab weakenId origlabelenv
  = let origdiffmap = origbindmap `DMap.difference` topbindmap
    in EnvCapture
          (fmapTupR productSnd origpairs)
          (EnvInstantiator $ \(Context newlabelenv newbindmap) pointers ->
              let oldnewmap =  -- only the captured part
                    DMap.fromList $
                      tupRtoList (\(Product.Pair origlab newlab) -> origlab :=> newlab) $
                        zipWithTupR (\origlab (Var _ idx) -> Product.Pair origlab (prjL idx newlabelenv))
                                    (fmapTupR productFst origpairs) pointers
                  -- rebind the variables in the captured part to the new scalar labels
                  rebounddiff = DMap.map (fmapTupR (\lab -> fromMaybe lab (DMap.lookup lab oldnewmap))) origdiffmap
              in DMap.unionWithKey (error "captureEnvironmentSlice: Context at usage of primal bundle contains keys already defined in primal computation")
                                   newbindmap rebounddiff)
  where
    collect :: (Eq lab, GEq s) => Maybe (AnyLabel EnvLabel s lab) -> env :> env' -> LabVal EnvLabel s lab env -> Exists (TupR (Product (DLabel EnvLabel s lab) (Var s env')))
    collect _ _ LEmpty = Exists TupRunit
    collect barrier w (LPush labelenv lab)
      | Just (AnyLabel b) <- barrier, Just Refl <- geq lab b = Exists TupRunit
      | Exists tup <- collect barrier (weakenSucc w) labelenv =
          Exists (TupRpair tup (TupRsingle (Product.Pair lab (Var (labelType lab) (w >:> ZeroIdx)))))

    tupRtoList :: (forall t'. s t' -> a) -> TupR s t -> [a]
    tupRtoList _ TupRunit = []
    tupRtoList f (TupRsingle x) = [f x]
    tupRtoList f (TupRpair t1 t2) = tupRtoList f t1 ++ tupRtoList f t2

productFst :: Product f g t -> f t
productFst (Product.Pair x _) = x

productSnd :: Product f g t -> g t
productSnd (Product.Pair _ x) = x

mapProductFst :: (forall t. f t -> g t) -> Product f h a -> Product g h a
mapProductFst f (Product.Pair x y) = Product.Pair (f x) y

mapProductSnd :: (forall t. g t -> h t) -> Product f g a -> Product f h a
mapProductSnd f (Product.Pair x y) = Product.Pair x (f y)


data LetBoundVars s env t t' =
    forall env'. LetBoundVars (LeftHandSide s t env env') (Vars s env' t')

lhsCopy :: TupR s t -> LetBoundVars s env t t
lhsCopy t
  | DeclareVars lhs _ varsgen <- declareVars t
  = LetBoundVars lhs (varsgen weakenId)


-- Perhaps this should be HList, but really that API is too complicated. Let's keep it simple.
infixr :@
data TypedList f tys where
    TLNil :: TypedList f '[]
    (:@) :: f t -> TypedList f tys -> TypedList f (t ': tys)

tlmap :: (forall t. f t -> g t) -> TypedList f tys -> TypedList g tys
tlmap _ TLNil = TLNil
tlmap f (x :@ xs) = f x :@ tlmap f xs

-- Key for the contribution map in the dual phase. Either a label of the
-- right-hand side from the original expression/program, or a reference to the
-- argument.
-- Also used as key for the bindmap, since there we need to store the location
-- of the argument as well (to be able to locate the right primal vars to
-- generate zeros in the Arg contributions, stupid as hell).
-- TODO: Since it's also used as key of the bindmap, better name please.
data CMapKey s lab t = Argument (TupR s t) | Local (DLabel NodeLabel (TupR s) lab t)

deriving instance (Show (TupR s t), Show lab) => Show (CMapKey s lab t)

instance (GEq s, GEq (TupR s), Eq lab, Matchable (TupR s)) => GEq (CMapKey s lab) where
    geq (Argument t1) (Argument t2) = matchMatchable t1 t2
    geq (Local l1) (Local l2) = geq l1 l2
    geq _ _ = Nothing

instance (GCompare s, GCompare (TupR s), Ord lab, Matchable (TupR s)) => GCompare (CMapKey s lab) where
    gcompare (Argument t1) (Argument t2) = gcompare t1 t2
    gcompare (Local l1) (Local l2) = gcompare l1 l2
    gcompare (Argument _) (Local _) = GLT
    gcompare (Local _) (Argument _) = GGT

cmapKeyType :: CMapKey s lab t -> TupR s t
cmapKeyType (Argument ty) = ty
cmapKeyType (Local lab) = labelType lab

showCMapKey :: (Show (TupR s t), Show lab)
            => (DLabel NodeLabel (TupR s) lab t -> String) -> CMapKey s lab t -> String
showCMapKey _ (Argument ty) = "A :: " ++ show ty
showCMapKey f (Local lab) = f lab


intersectOrd :: Ord a => [a] -> [a] -> [a]
intersectOrd a b = Set.toList (Set.fromList a `Set.intersection` Set.fromList b)
