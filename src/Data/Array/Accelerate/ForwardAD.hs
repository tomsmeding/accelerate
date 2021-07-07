{- | A basic implementation of forward automatic differentiation (AD) for
Accelerate. This module should be imported qualified; we suggest @AD@.

The types here are usable not only in Accelerate, but also in plain Haskell
code. Use the @Plain@-suffixed functions for that.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Array.Accelerate.ForwardAD (
    -- * Dual numbers
    ADF, -- pattern ADF,
    ADFClasses,
    -- * Forward AD
    forwardADA', forwardADE', forwardAD'Plain,
    forwardADA, forwardADE, forwardADPlain,
    -- * Forward AD, alternative style
    variable, constant, value, derivative,
    variablePlain, constantPlain, valuePlain, derivativePlain,
    -- * Additional utilities
    -- adfOut, adfIn
    gradientA_FAD_Vector
) where

import Data.Proxy

import Data.Array.Accelerate (Generic, Elt, Exp, Acc, Array, Vector, Scalar, Shape)
import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Smart as A
import qualified Data.Array.Accelerate.Sugar.Elt as A
import qualified Data.Array.Accelerate.Type as A
import qualified Data.Array.Accelerate.Representation.Type as A


-- | Forward AD. This type is an instance of many of the standard numeric
-- classes, meaning that it should be usable seamlessly in place of e.g.
-- 'Float'.
-- NOTE: The current representation is inefficient for higher-order
-- derivatives, since it computes intermediate derivatives an exponential
-- number of times. For first-order derivatives, however, it's fine and has
-- normal forward AD complexity: the runtime increases by at most a constant
-- factor, and memory usage multiplies by two.
data ADF s a = ADF_ a a
  deriving (Show, Generic)

pattern ADF :: Elt a => Exp a -> Exp a -> Exp (ADF s a)
pattern ADF x dx = A.Pattern (x, dx)
{-# COMPLETE ADF #-}

instance Elt a => Elt (ADF s a)

instance Eq a => Eq (ADF s a) where
    ADF_ x _ == ADF_ y _ = x == y

instance A.Eq a => A.Eq (ADF s a) where
    ADF x _ == ADF y _ = x A.== y

instance Ord a => Ord (ADF s a) where
    compare (ADF_ x _) (ADF_ y _) = compare x y

instance A.Ord a => A.Ord (ADF s a) where
    compare (ADF x _) (ADF y _) = A.compare x y

instance Num a => Num (ADF s a) where
    ADF_ x dx + ADF_ y dy = ADF_ (x + y) (dx + dy)
    ADF_ x dx * ADF_ y dy = ADF_ (x * y) (dx * y + x * dy)
    abs (ADF_ x dx) = ADF_ (abs x) (signum x * dx)
    signum (ADF_ x _) = ADF_ (signum x) 0
    fromInteger n = ADF_ (fromInteger n) 0
    negate (ADF_ x dx) = ADF_ (negate x) (negate dx)

instance Fractional a => Fractional (ADF s a) where
    fromRational r = ADF_ (fromRational r) 0
    ADF_ x dx / ADF_ y dy = ADF_ (x / y) ((y * dx - x * dy) / (y * y))
    recip (ADF_ x dx) = ADF_ (recip x) (negate (recip (x * x)) * dx)

instance Floating a => Floating (ADF s a) where
    pi = ADF_ pi 0
    exp (ADF_ x dx) = ADF_ (exp x) (exp x * dx)
    log (ADF_ x dx) = ADF_ (log x) (recip x * dx)
    sqrt (ADF_ x dx) = ADF_ (sqrt x) (dx / (2 * sqrt x))
    ADF_ x dx ** ADF_ y dy = ADF_ (x ** y) ((y * x ** y) / x * dx + log x * x ** y * dy)
    sin (ADF_ x dx) = ADF_ (sin x) (cos x * dx)
    cos (ADF_ x dx) = ADF_ (cos x) (negate (sin x) * dx)
    tan (ADF_ x dx) = ADF_ (tan x) (recip (cos x * cos x) * dx)
    asin (ADF_ x dx) = ADF_ (asin x) (recip (sqrt (1 - x * x)) * dx)
    acos (ADF_ x dx) = ADF_ (acos x) (negate (recip (sqrt (1 - x * x))) * dx)
    atan (ADF_ x dx) = ADF_ (atan x) (recip (1 + x * x) * dx)
    sinh = undefined
    cosh = undefined
    tanh = undefined
    asinh = undefined
    acosh = undefined
    atanh = undefined

-- instance RealFrac a => RealFrac (ADF s a) where
--     properFraction _ = error "properFraction unimplemented, the typeclass is not general enough"
--     truncate (ADF_ x _) = truncate x
--     round (ADF_ x _) = round x
--     ceiling (ADF_ x _) = ceiling x
--     floor (ADF_ x _) = floor x

-- | The plain version of 'forwardAD'.
forwardADPlain :: (forall s. ADF s a -> ADF s b) -> (a, a) -> (b, b)
forwardADPlain f (x, d) = let ADF_ y d' = f (ADF_ x d) in (y, d')

-- | The plain version of 'forwardADE''.
--
-- > forwardAD'Plain f x = snd (forwardADPlain f (x, 1))
forwardAD'Plain :: Num a => (forall s. ADF s a -> ADF s b) -> a -> b
forwardAD'Plain f x = snd (forwardADPlain f (x, 1))

type family Dual s a = r | r -> a where
    Dual s A.Half = ADF s A.Half
    Dual s Float = ADF s Float
    Dual s Double = ADF s Double

    Dual s Int = Int
    Dual s A.Int8 = A.Int8
    Dual s A.Int16 = A.Int16
    Dual s A.Int32 = A.Int32
    Dual s A.Int64 = A.Int64
    Dual s Word = Word
    Dual s A.Word8 = A.Word8
    Dual s A.Word16 = A.Word16
    Dual s A.Word32 = A.Word32
    Dual s A.Word64 = A.Word64

    Dual s () = ()
    Dual s (a, b) = (Dual s a, Dual s b)
    Dual s A.Z = A.Z
    Dual s (a A.:. b) = Dual s a A.:. Dual s b
    Dual s (Array sh a) = Array sh (Dual s a)

type family Tan a where
    Tan A.Half = A.Half
    Tan Float = Float
    Tan Double = Double

    Tan Int = ()
    Tan A.Int8 = ()
    Tan A.Int16 = ()
    Tan A.Int32 = ()
    Tan A.Int64 = ()
    Tan Word = ()
    Tan A.Word8 = ()
    Tan A.Word16 = ()
    Tan A.Word32 = ()
    Tan A.Word64 = ()

    Tan () = ()
    Tan (a, b) = (Tan a, Tan b)
    Tan A.Z = A.Z
    Tan (a A.:. b) = Tan a A.:. Tan b
    Tan (Array sh a) = Array sh (Tan a)

-- | Given a function that can compute with dual numbers, an argument and the
-- tangent (derivative) of that argument, compute the normal function output
-- value and the tangent of that output value. This is a Jacobian-vector
-- product.
forwardADE :: (Elt a, Elt b) => (forall s. Proxy s -> Exp (Dual s a) -> Exp (Dual s b)) -> Exp (a, Tan a) -> Exp (b, Tan b)
forwardADE f x =
    let dualres = f (Proxy @()) (zipTanExp (Proxy @()) (A.typeR (A.fst x)) x)
    in unzipTanExp (Proxy @()) (unzipTanType (Proxy @()) (A.typeR dualres)) dualres

zipTanExp :: proxy s -> A.TypeR a -> Exp (a, Tan a) -> Exp (Dual s a)
zipTanExp _ A.TupRunit _ = A.constant ()
zipTanExp p (A.TupRpair t1 t2) (A.T2 e e') =
    A.T2 (zipTanExp p t1 (A.T2 (A.fst e) (A.fst e')))
         (zipTanExp p t2 (A.T2 (A.snd e) (A.snd e')))
zipTanExp proxy1 (A.TupRsingle typ) expr = go proxy1 typ expr
  where
    go :: proxy s -> A.ScalarType a -> Exp (a, Tan a) -> Exp (Dual s a)
    go p (A.SingleScalarType (A.NumSingleType (A.IntegralNumType t))) e = goI p t e
    go p (A.SingleScalarType (A.NumSingleType (A.FloatingNumType t))) e = goF p t e
    go _ (A.VectorScalarType _) _ = error "Vector types not yet supported for forward AD"

    goI :: proxy s -> A.IntegralType a -> Exp (a, Tan a) -> Exp (Dual s a)
    goI _ A.TypeInt e = A.fst e
    goI _ A.TypeInt8 e = A.fst e
    goI _ A.TypeInt16 e = A.fst e
    goI _ A.TypeInt32 e = A.fst e
    goI _ A.TypeInt64 e = A.fst e
    goI _ A.TypeWord e = A.fst e
    goI _ A.TypeWord8 e = A.fst e
    goI _ A.TypeWord16 e = A.fst e
    goI _ A.TypeWord32 e = A.fst e
    goI _ A.TypeWord64 e = A.fst e

    goF :: proxy s -> A.FloatingType a -> Exp (a, Tan a) -> Exp (Dual s a)
    goF _ A.TypeHalf e = ADF (A.fst e) (A.snd e)
    goF _ A.TypeFloat e = ADF (A.fst e) (A.snd e)
    goF _ A.TypeDouble e = ADF (A.fst e) (A.snd e)

unzipTanExp :: proxy s -> A.TypeR a -> Exp (Dual s a) -> Exp (a, Tan a)
unzipTanExp _ A.TupRunit _ = A.T2 (A.constant ()) (A.constant ())
unzipTanExp p (A.TupRpair t1 t2) e =
    let A.T2 e1 e1' = unzipTanExp p t1 (A.fst e)
        A.T2 e2 e2' = unzipTanExp p t2 (A.snd e)
    in A.T2 (A.T2 e1 e2) (A.T2 e1' e2')
unzipTanExp proxy1 (A.TupRsingle typ) expr = go proxy1 typ expr
  where
    go :: proxy s -> A.ScalarType a -> Exp (Dual s a) -> Exp (a, Tan a)
    go p (A.SingleScalarType (A.NumSingleType (A.IntegralNumType t))) e = goI p t e
    go p (A.SingleScalarType (A.NumSingleType (A.FloatingNumType t))) e = goF p t e
    go _ (A.VectorScalarType _) _ = error "Vector types not yet supported for forward AD"

    goI :: proxy s -> A.IntegralType a -> Exp (Dual s a) -> Exp (a, Tan a)
    goI _ A.TypeInt e = A.T2 e (A.constant ())
    goI _ A.TypeInt8 e = A.T2 e (A.constant ())
    goI _ A.TypeInt16 e = A.T2 e (A.constant ())
    goI _ A.TypeInt32 e = A.T2 e (A.constant ())
    goI _ A.TypeInt64 e = A.T2 e (A.constant ())
    goI _ A.TypeWord e = A.T2 e (A.constant ())
    goI _ A.TypeWord8 e = A.T2 e (A.constant ())
    goI _ A.TypeWord16 e = A.T2 e (A.constant ())
    goI _ A.TypeWord32 e = A.T2 e (A.constant ())
    goI _ A.TypeWord64 e = A.T2 e (A.constant ())

    goF :: proxy s -> A.FloatingType a -> Exp (Dual s a) -> Exp (a, Tan a)
    goF _ A.TypeHalf (ADF e e') = A.T2 e e'
    goF _ A.TypeFloat (ADF e e') = A.T2 e e'
    goF _ A.TypeDouble (ADF e e') = A.T2 e e'

unzipTanType :: proxy s -> A.TypeR (Dual s a) -> A.TypeR a
unzipTanType = undefined
-- unzipTanType _ A.TupRunit = A.TupRunit
-- unzipTanType p (A.TupRpair t1 t2) =
--     let A.T2 e1 e1' = unzipTanType p t1
--         A.T2 e2 e2' = unzipTanType p t2
--     in A.T2 (A.T2 e1 e2) (A.T2 e1' e2')
-- unzipTanType proxy1 (A.TupRsingle typ) = go proxy1 typ expr
--   where
--     go :: proxy s -> A.ScalarType a -> Exp (Dual s a) -> Exp (a, Tan a)
--     go p (A.SingleScalarType (A.NumSingleType (A.IntegralNumType t))) e = goI p t e
--     go p (A.SingleScalarType (A.NumSingleType (A.FloatingNumType t))) e = goF p t e
--     go _ (A.VectorScalarType _) _ = error "Vector types not yet supported for forward AD"

--     goI :: proxy s -> A.IntegralType a -> Exp (Dual s a) -> Exp (a, Tan a)
--     goI _ A.TypeInt e = A.T2 e (A.constant ())
--     goI _ A.TypeInt8 e = A.T2 e (A.constant ())
--     goI _ A.TypeInt16 e = A.T2 e (A.constant ())
--     goI _ A.TypeInt32 e = A.T2 e (A.constant ())
--     goI _ A.TypeInt64 e = A.T2 e (A.constant ())
--     goI _ A.TypeWord e = A.T2 e (A.constant ())
--     goI _ A.TypeWord8 e = A.T2 e (A.constant ())
--     goI _ A.TypeWord16 e = A.T2 e (A.constant ())
--     goI _ A.TypeWord32 e = A.T2 e (A.constant ())
--     goI _ A.TypeWord64 e = A.T2 e (A.constant ())

--     goF :: proxy s -> A.FloatingType a -> Exp (Dual s a) -> Exp (a, Tan a)
--     goF _ A.TypeHalf (ADF e e') = A.T2 e e'
--     goF _ A.TypeFloat (ADF e e') = A.T2 e e'
--     goF _ A.TypeDouble (ADF e e') = A.T2 e e'

-- | Given a function that can compute with dual numbers, an argument and the
-- tangent (derivative) of that argument, compute the normal function output
-- value and the tangent of that output value. This is a Jacobian-vector
-- product.
--
-- Array version of 'forwardADE'.
forwardADA :: (Elt a, Elt b, Shape sh, Shape sh')
           => (forall s. Acc (Array sh (ADF s a)) -> Acc (Array sh' (ADF s b)))
           -> Acc (Array sh a, Array sh a) -> Acc (Array sh' b, Array sh' b)
forwardADA f (A.T2 xs ds) =
    let res = f (A.zipWith ADF xs ds)
    in A.T2 (A.map (\(ADF ys _)  -> ys) res)
            (A.map (\(ADF _ ds') -> ds') res)

-- | Given a single-argument function that can compute with dual numbers, and
-- given an argument, compute the derivative of the function evaluated at that
-- argument. Convenience wrapper of 'forwardADE'.
--
-- > forwardADE' f x = snd (forwardADE f (T2 x 1))
forwardADE' :: (A.Num a, Elt a, Elt b) => (forall s. Exp (ADF s a) -> Exp (ADF s b)) -> Exp a -> Exp b
forwardADE' _ = undefined
-- forwardADE' f x = A.snd (forwardADE f (A.T2 x 1))

-- | Given a function taking a single scalar input that can compute with dual
-- numbers, and given an argument, compute the derivative of the function
-- evaluated at that argument. Convenience wrapper of 'forwardADA'.
--
-- > forwardADA' f x = asnd (forwardADA f (T2 x (unit 1)))
forwardADA' :: (A.Num a, Elt a, Elt b, Shape sh)
           => (forall s. Acc (Scalar (ADF s a)) -> Acc (Array sh (ADF s b)))
           -> Acc (Scalar a) -> Acc (Array sh b)
forwardADA' f x = A.asnd (forwardADA f (A.T2 x (A.unit 1)))

variablePlain :: Num a => a -> ADF s a
variablePlain x = ADF_ x 1

variable :: (Elt a, Num a) => Exp a -> Exp (ADF s a)
variable x = ADF x (A.constant 1)

constantPlain :: Num a => a -> ADF s a
constantPlain x = ADF_ x 0

constant :: (Elt a, Num a) => Exp a -> Exp (ADF s a)
constant x = ADF x (A.constant 0)

valuePlain :: (forall s. ADF s a) -> a
valuePlain (ADF_ x _) = x

value :: Elt a => (forall s. Exp (ADF s a)) -> Exp a
value (ADF x _) = x

derivativePlain :: (forall s. ADF s a) -> a
derivativePlain (ADF_ _ dx) = dx

derivative :: Elt a => (forall s. Exp (ADF s a)) -> Exp a
derivative (ADF _ dx) = dx

adfOut :: Elt a => Exp (ADF s a) -> ADF s (Exp a)
adfOut (ADF x dx) = ADF_ x dx

adfIn :: Elt a => ADF s (Exp a) -> Exp (ADF s a)
adfIn (ADF_ x dx) = ADF x dx

expADFUnary :: Elt a
            => (ADF s (Exp a) -> ADF s (Exp a))
            -> Exp (ADF s a) -> Exp (ADF s a)
expADFUnary f = adfIn . f . adfOut

expADFBinary :: Elt a
             => (ADF s (Exp a) -> ADF s (Exp a) -> ADF s (Exp a))
             -> Exp (ADF s a) -> Exp (ADF s a) -> Exp (ADF s a)
expADFBinary f = \x y -> adfIn (adfOut x `f` adfOut y)

instance (Elt a, Num a, Num (Exp a)) => Num (Exp (ADF s a)) where
    (+) = expADFBinary (+)
    (*) = expADFBinary (*)
    abs = expADFUnary abs
    signum = expADFUnary signum
    fromInteger = adfIn . fromInteger
    negate = expADFUnary negate

instance (Elt a, Fractional a, Fractional (Exp a)) => Fractional (Exp (ADF s a)) where
    (/) = expADFBinary (/)
    recip = expADFUnary recip
    fromRational = adfIn . fromRational

instance (Elt a, Floating a, Floating (Exp a)) => Floating (Exp (ADF s a)) where
    pi    = constant pi
    exp   = expADFUnary exp
    log   = expADFUnary log
    sqrt  = expADFUnary sqrt
    sin   = expADFUnary sin
    cos   = expADFUnary cos
    tan   = expADFUnary tan
    asin  = expADFUnary asin
    acos  = expADFUnary acos
    atan  = expADFUnary atan
    sinh  = expADFUnary sinh
    cosh  = expADFUnary cosh
    tanh  = expADFUnary tanh
    asinh = expADFUnary asinh
    acosh = expADFUnary acosh
    atanh = expADFUnary atanh

instance (RealFrac a, A.RealFrac a) => A.RealFrac (ADF s a) where
    properFraction _ = error "properFraction on ADF unimplemented, the typeclass is not general enough"
    truncate (ADF x _) = A.truncate x
    round (ADF x _) = A.round x
    ceiling (ADF x _) = A.ceiling x
    floor (ADF x _) = A.floor x

instance (A.ToFloating a b, Num b, A.Floating b) => A.ToFloating a (ADF s b) where
    toFloating = constant . A.toFloating

-- Omits ToFloating due to not being able to specify that as an isolated constraint
type ADFClasses a = (A.Ord a, A.Num a, A.Fractional a, A.Floating a, A.RealFrac a, A.ToFloating Int a)


-- | Compute the gradient of an array computation taking a Vector of
-- floating-point values using forward AD.
--
-- This function runs on the meta-level (in Haskell, not in Accelerate),
-- because it must run the Accelerate function multiple times. Because it uses
-- forward AD, it will in general be very slow (because it executes the
-- function once for each element in the input vector), but it does not rely on
-- the reverse AD implementation and can thus be used to test the correctness
-- of reverse AD.
--
-- The test suite contains a slightly more elaborate implementation of this
-- function that can handle non-vector arguments, as well as some other
-- correctness-testing infrastructure.
gradientA_FAD_Vector
  :: (forall arr arr2. (A.Arrays arr, A.Arrays arr2) => (Acc arr -> Acc arr2) -> arr -> arr2)
  -> (forall a. ADFClasses a => Acc (Vector a) -> Acc (Scalar a))
  -> Vector Float
  -> Vector Float
gradientA_FAD_Vector run1 func arg =
    let sh@(A.Z A.:. n) = A.arrayShape arg
    in A.fromList sh
                  [derivativePlain $ (`A.linearIndexArray` 0) $ run1 func $
                      A.fromFunction sh
                                     (\j -> let x = arg `A.indexArray` j
                                            in if j == idx then variablePlain x
                                                           else constantPlain x)
                  | idx <- [A.Z A.:. i | i <- [0 .. n-1]]]
