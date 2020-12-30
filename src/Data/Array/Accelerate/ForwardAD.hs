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
module Data.Array.Accelerate.ForwardAD (
    ADF, -- pattern ADF,
    ADFClasses,
    variablePlain, constantPlain, valuePlain, derivativePlain,
    variable, constant, value, derivative,
    -- adfOut, adfIn
    gradientA_FAD_Vector
) where

import Data.Array.Accelerate (Generic, Elt, Exp, Acc, Vector, Scalar)
import qualified Data.Array.Accelerate as A


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
    properFraction _ = error "properFraction unimplemented, the typeclass is not general enough"
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
-- function once for each element in the input vector), but it does not rely in
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
