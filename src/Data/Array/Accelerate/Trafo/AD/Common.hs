{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
module Data.Array.Accelerate.Trafo.AD.Common where

import Control.Monad.State.Strict
import Data.Char (isDigit)
import Data.List (intercalate, sortOn)
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Sum (DSum(..))
import Data.GADT.Compare
import Data.GADT.Show
import Data.Some (Some, mkSome)
import Data.Typeable ((:~:)(Refl))
import Data.Void

import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.Representation.Array hiding ((!!))
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type


data TagVal s env where
    TEmpty :: TagVal s ()
    TPush :: TagVal s env -> s t -> TagVal s (env, t)

data LabVal s lab env where
    LEmpty :: LabVal s lab ()
    LPush :: LabVal s lab env -> DLabel s lab t -> LabVal s lab (env, t)

data PartialVal s topenv env where
    PTEmpty :: PartialVal s topenv topenv
    PTPush :: PartialVal s topenv env -> s t -> PartialVal s topenv (env, t)

data DLabel s lab t =
    DLabel { labelType :: s t
           , labelLabel :: lab }
  deriving (Show)

instance Show lab => GShow (DLabel TypeR      lab) where gshowsPrec = showsPrec
instance Show lab => GShow (DLabel ScalarType lab) where gshowsPrec = showsPrec
instance Show lab => GShow (DLabel ArraysR    lab) where gshowsPrec = showsPrec
instance Show lab => GShow (DLabel ArrayR     lab) where gshowsPrec = showsPrec

instance GEq s => GEq (DLabel s lab) where
    geq (DLabel ty1 _) (DLabel ty2 _) = do
        Refl <- geq ty1 ty2
        return Refl

instance (Ord lab, GCompare s) => GCompare (DLabel s lab) where
    gcompare (DLabel ty1 lab1) (DLabel ty2 lab2) =
        case gcompare ty1 ty2 of
          GLT -> GLT
          GGT -> GGT
          GEQ -> case compare lab1 lab2 of
                   LT -> GLT
                   EQ -> GEQ
                   GT -> GGT

data TupleIdx t t' where
    TIHere  :: TupleIdx s s
    TILeft  :: TupleIdx a t -> TupleIdx (a, b) t
    TIRight :: TupleIdx b t -> TupleIdx (a, b) t

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

showDLabel :: (Show (s t), Show lab) => DLabel s lab t -> String
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

prjL :: Idx env t -> LabVal s lab env -> DLabel s lab t
prjL ZeroIdx (LPush _ x) = x
prjL (SuccIdx idx) (LPush env _) = prjL idx env

mapLabVal :: (lab -> lab') -> LabVal s lab env -> LabVal s lab' env
mapLabVal _ LEmpty = LEmpty
mapLabVal f (LPush env (DLabel ty lab)) = LPush (mapLabVal f env) (DLabel ty (f lab))

labValContains :: Eq lab => LabVal s lab env -> lab -> Bool
labValContains LEmpty _ = False
labValContains (LPush env (DLabel _ lab)) x =
    x == lab || labValContains env x

uniqueLabVal :: Eq lab => LabVal s lab env -> Bool
uniqueLabVal LEmpty = True
uniqueLabVal (LPush env (DLabel _ lab)) =
    not (labValContains env lab) && uniqueLabVal env

data FoundTag s env = forall t. FoundTag (s t) (Idx env t)

labValFind' :: Eq lab => LabVal s lab env -> lab -> Maybe (FoundTag s env)
labValFind' LEmpty _ = Nothing
labValFind' (LPush env (DLabel ty lab)) target
    | lab == target = Just (FoundTag ty ZeroIdx)
    | otherwise =
        case labValFind' env target of
            Just (FoundTag ty' idx) -> Just (FoundTag ty' (SuccIdx idx))
            Nothing -> Nothing

tupleLabel :: DLabel s lab t -> DLabel (TupR s) lab t
tupleLabel (DLabel ty lab) = DLabel (TupRsingle ty) lab

fmapLabel :: (lab -> lab') -> DLabel s lab t -> DLabel s lab' t
fmapLabel f (DLabel ty lab) = DLabel ty (f lab)

fmapLabels :: (lab -> lab') -> TupR (DLabel s lab) t -> TupR (DLabel s lab') t
fmapLabels _ TupRunit = TupRunit
fmapLabels f (TupRsingle lab) = TupRsingle (fmapLabel f lab)
fmapLabels f (TupRpair labs1 labs2) = TupRpair (fmapLabels f labs1) (fmapLabels f labs2)

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


newtype IdGen a = IdGen (State Int a)
  deriving (Functor, Applicative, Monad, MonadState Int)

evalIdGen :: IdGen a -> a
evalIdGen (IdGen s) = evalState s 1

genId' :: s t -> IdGen (DLabel s Int t)
genId' ty = state (\s -> (DLabel ty s, succ s))

lpushLabTup :: LabVal s lab env -> LeftHandSide s t env env' -> TupR (DLabel s lab) t -> LabVal s lab env'
lpushLabTup labelenv (LeftHandSideWildcard _) TupRunit = labelenv
lpushLabTup labelenv (LeftHandSideSingle _) (TupRsingle lab) = LPush labelenv lab
lpushLabTup labelenv (LeftHandSidePair lhs1 lhs2) (TupRpair labs1 labs2) =
    lpushLabTup (lpushLabTup labelenv lhs1 labs1) lhs2 labs2
lpushLabTup _ _ _ = error "lpushLabTup: impossible GADTs"


pvalPushLHS :: LeftHandSide s t env env' -> PartialVal s topenv env -> PartialVal s topenv env'
pvalPushLHS (LeftHandSideWildcard _) tv = tv
pvalPushLHS (LeftHandSideSingle sty) tv = PTPush tv sty
pvalPushLHS (LeftHandSidePair lhs1 lhs2) tv = pvalPushLHS lhs2 (pvalPushLHS lhs1 tv)


-- TODO: Is PDAux actually used anywhere? If not, remove the constructor and the other Aux stuff
data PD tag a = P !a | D !a | PDAux !tag !a
  deriving (Show, Eq, Ord)

type PDAuxTagExp = Void
data PDAuxTagAcc = TmpTup
  deriving (Show, Eq, Ord)

type PDExp = PD PDAuxTagExp
type PDAcc = PD PDAuxTagAcc

-- Expression node labels are of tuple type and have a PD tag.
-- Scalar value labels have no tag.
-- Since the Let bindings are on the scalar level (because Accelerate forces
--   tuple-destructuring), the labels in the environment are scalar labels.
--   These thus also have no tag.
data Context s tag lab env =
    Context (LabVal s lab env)
            (DMap (DLabel (TupR s) (PD tag lab))
                  (TupR (DLabel s lab)))

showContext :: (Ord lab, Show lab, Show tag, Ord tag, forall t. Show (s t), forall t. Show (TupR s t))
            => Context s tag lab aenv -> String
showContext (Context labelenv bindmap) = "Context " ++ showLabelenv labelenv ++ " " ++ showBindmap bindmap

showLabelenv :: (Show lab, forall t. Show (s t)) => LabVal s lab aenv -> String
showLabelenv LEmpty = "[]"
showLabelenv (LPush env lab) = "[" ++ go env ++ showDLabel lab ++ "]"
  where
    go :: (Show lab, forall t. Show (s t)) => LabVal s lab aenv -> String
    go LEmpty = ""
    go (LPush env' lab') = go env' ++ showDLabel lab' ++ ", "

showBindmap :: (Ord lab, Show lab, Show tag, Ord tag, forall t. Show (s t), forall t. Show (TupR s t))
            => DMap (DLabel (TupR s) (PD tag lab)) (TupR (DLabel s lab)) -> String
showBindmap bindmap =
    let tups = sortOn fst [(lab, (showDLabel dlab, showTupR showDLabel labs))
                          | dlab@(DLabel _ lab) :=> labs <- DMap.assocs bindmap]
        s = intercalate ", " ["(" ++ dlabshow ++ ") :=> " ++ labsshow
                             | (_, (dlabshow, labsshow)) <- tups]
    in "[" ++ s ++ "]"


-- TODO: make this 'type AnyLabel s lab = Exists (DLabel s lab)', and perhaps even inline this because then the typedef is marginally useful. Also apply this to other Any* names.
-- (But consider the specialised Eq/Ord instances below. Can we reproduce that with an Exists version?)
data AnyLabel s lab = forall t. AnyLabel (DLabel s lab t)

instance (Eq lab, GEq s) => Eq (AnyLabel s lab) where
    AnyLabel (DLabel ty1 lab1) == AnyLabel (DLabel ty2 lab2)
      | lab1 /= lab2 = False
      | Just Refl <- geq ty1 ty2 = True
      | otherwise = error "Eq AnyLabel: labels match, but types do not!"

instance (Ord lab, GCompare s) => Ord (AnyLabel s lab) where
    compare (AnyLabel (DLabel ty1 lab1)) (AnyLabel (DLabel ty2 lab2)) =
        case compare lab1 lab2 of
          LT -> LT
          GT -> GT
          EQ | GEQ <- gcompare ty1 ty2 -> EQ
             | otherwise -> error "Ord AnyLabel: labels match, but types do not!"
