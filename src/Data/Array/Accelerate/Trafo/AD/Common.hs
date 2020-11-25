{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.AD.Common where

import Control.Monad.State.Strict
import Data.Char (isDigit)
import Data.List (intercalate, sortOn)
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Sum (DSum(..))
import Data.Functor.Product (Product)
import qualified Data.Functor.Product as Product
import Data.GADT.Compare
import Data.GADT.Show
import Data.Maybe (fromMaybe)
import Data.Some (Some, mkSome)
import Data.Typeable ((:~:)(Refl))
import Data.Void

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Representation.Array hiding ((!!))
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type


data TagVal s env where
    TEmpty :: TagVal s ()
    TPush :: TagVal s env -> s t -> TagVal s (env, t)

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

data FoundTag s env = forall t. FoundTag (s t) (Idx env t)

labValFind' :: Eq lab => LabVal lty s lab env -> lab -> Maybe (FoundTag s env)
labValFind' LEmpty _ = Nothing
labValFind' (LPush env (DLabel ty lab)) target
    | lab == target = Just (FoundTag ty ZeroIdx)
    | otherwise =
        case labValFind' env target of
            Just (FoundTag ty' idx) -> Just (FoundTag ty' (SuccIdx idx))
            Nothing -> Nothing

-- Only allowed for node labels, since env labels can only usefully refer to
-- non-tuple values due to mandatory let-destructuring. This restriction is not
-- syntactically necessary, but semantically it might prevent mishaps.
tupleLabel :: DLabel NodeLabel s lab t -> DLabel NodeLabel (TupR s) lab t
tupleLabel (DLabel ty lab) = DLabel (TupRsingle ty) lab

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


newtype IdGen a = IdGen (State Int a)
  deriving (Functor, Applicative, Monad, MonadState Int)

evalIdGen :: IdGen a -> a
evalIdGen (IdGen s) = evalState s 1

genId' :: s t -> IdGen (DLabel lty s Int t)
genId' ty = state (\s -> (DLabel ty s, succ s))

-- The restriction to env labels is not syntactically necessary, but
-- semantically it generally doesn't make sense to push a tuple of node labels.
-- Hence to prevent mishaps, this function is specialised to EnvLabel.
lpushLabTup :: LabVal EnvLabel s lab env -> LeftHandSide s t env env' -> TupR (DLabel EnvLabel s lab) t -> LabVal EnvLabel s lab env'
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

-- Expression node labels are of tuple type and have a PD tag; environment
-- labels are of scalar type and have no tag.
-- The labelenv recalls the environment of let-bound variables with environment
-- labels; the bindmap maps node labels to the tuple of environment labels
-- indicating where its value is stored.
data Context s tag lab env =
    Context (LabVal EnvLabel s lab env)
            (DMap (DLabel NodeLabel (TupR s) (PD tag lab))
                  (TupR (DLabel EnvLabel s lab)))

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
            => DMap (DLabel NodeLabel (TupR s) (PD tag lab)) (TupR (DLabel EnvLabel s lab)) -> String
showBindmap bindmap =
    let tups = sortOn fst [(lab, (showDLabel dlab, showTupR showDLabel labs))
                          | dlab@(DLabel _ lab) :=> labs <- DMap.assocs bindmap]
        s = intercalate ", " ["(" ++ dlabshow ++ ") :=> " ++ labsshow
                             | (_, (dlabshow, labsshow)) <- tups]
    in "[" ++ s ++ "]"


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

instance (Show lab, forall t. Show (s t)) => Show (AnyLabel lty s lab) where
    showsPrec p (AnyLabel lab) = showParen (p > 10) (showString "AnyLabel " . showsPrec 11 lab)


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
                  -> DMap (DLabel NodeLabel (TupR s) (PD tag lab)) (TupR (DLabel EnvLabel s lab)))

captureEnvironmentSlice :: (GCompare s, GCompare (TupR s), Ord tag) => Context s tag Int topenv -> Context s tag Int env -> EnvCapture s tag env Int
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

    zipWithTupR :: (forall t'. s1 t' -> s2 t' -> s t') -> TupR s1 t -> TupR s2 t -> TupR s t
    zipWithTupR _ TupRunit TupRunit = TupRunit
    zipWithTupR f (TupRsingle a) (TupRsingle b) = TupRsingle (f a b)
    zipWithTupR f (TupRpair a1 a2) (TupRpair b1 b2) = TupRpair (zipWithTupR f a1 b1) (zipWithTupR f a2 b2)
    zipWithTupR _ _ _ = error "impossible GADTs"

    tupRtoList :: (forall t'. s t' -> a) -> TupR s t -> [a]
    tupRtoList _ TupRunit = []
    tupRtoList f (TupRsingle x) = [f x]
    tupRtoList f (TupRpair t1 t2) = tupRtoList f t1 ++ tupRtoList f t2

    productFst :: Product f g t -> f t
    productFst (Product.Pair x _) = x

    productSnd :: Product f g t -> g t
    productSnd (Product.Pair _ x) = x
