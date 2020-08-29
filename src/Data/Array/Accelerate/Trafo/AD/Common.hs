{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Data.Array.Accelerate.Trafo.AD.Common where

import Data.Char (isDigit)
import Data.GADT.Compare
import Data.GADT.Show
import Data.Typeable ((:~:)(Refl))

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

pickDLabels :: TupleIdx t t' -> TupR (DLabel s lab) t -> TupR (DLabel s lab) t'
pickDLabels TIHere labs = labs
pickDLabels (TILeft path) (TupRpair lab _) = pickDLabels path lab
pickDLabels (TIRight path) (TupRpair _ lab) = pickDLabels path lab
pickDLabels _ _ = error "pickDLabels: impossible GADTs"

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
