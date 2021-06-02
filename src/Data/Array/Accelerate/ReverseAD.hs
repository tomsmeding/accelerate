{- | An implementation of reverse automatic differentiation (AD) for
Accelerate. This module should be imported qualified; we suggest @AD@.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Data.Array.Accelerate.ReverseAD (
  -- * Differentiation
  reverseAD, gradient,
  areverseAD, agradient,

  -- * Custom derivatives
  customDeriv, acustomDeriv,
) where

import Data.Array.Accelerate.Language                               ( unit )
import qualified Data.Array.Accelerate.Prelude as A                 ( uncurry )
import Data.Array.Accelerate.Smart                                  hiding ( arraysR )
import Data.Array.Accelerate.Sugar.Array                            ( Arrays(..), Scalar )
import Data.Array.Accelerate.Sugar.Elt


-- | Reverse AD on the expression level. (See 'areverseAD' for the array level.)
--
-- In the invocation @reverseAD f x a@, what is computed is the derivative of
-- @z@ with respect to @x@ given that @a@ is the derivative of @z@ with respect
-- to @f x@. Formulated differently, this invocation computes a linear
-- combination of the rows of the Jacobian matrix of @f@ at @x@, where the
-- coefficients of the linear combination are given by @a@.
reverseAD :: forall t t'. (Elt t, Elt t')
          => (Exp t -> Exp t')
          -> Exp t
          -> Exp t'
          -- -> Exp (t', t)
          -> Exp t
reverseAD f (Exp e) (Exp a) = mkExp $ Evjp (eltR @t) (unExp . f . Exp) e a

-- | A special case of 'reverseAD' that works only for functions that return a single scalar, floating-point value.
--
-- > gradient f x = reverseAD f x (constant 1)
--
-- Note: The restriction to a floating-point result is technically unnecessary,
-- but returning an integral value would always produce a zero gradient, which
-- is usually not the intended result.
gradient :: (Elt t, Elt e, Floating e)
         => (Exp t -> Exp e)
         -> Exp t
         -> Exp t
gradient f x = reverseAD f x (constant 1)

-- | Reverse AD on the array level. (See 'reverseAD' for the expression level.)
--
-- In the invocation @areverseAD f x a@, what is computed is the derivative of
-- @z@ with respect to @x@ given that @a@ is the derivative of @z@ with respect
-- to @f x@. Formulated differently, this invocation computes a linear
-- combination of the rows of the Jacobian matrix of @f@ at @x@, where the
-- coefficients of the linear combination are given by @a@.
areverseAD :: forall a b. (Arrays a, Arrays b)
           => (Acc a -> Acc b)
           -> Acc a
           -> Acc b
           -- -> Acc (b, a)
           -> Acc a
areverseAD = Acc $$$ applyAcc $ Avjp (arraysR @a)

-- | A special case of 'areverseAD' that works only for functions that return a single scalar, floating-point value.
--
-- > agradient f x = areverseAD f x (unit (constant 1))
--
-- Note: The restriction to a floating-point result is technically unnecessary,
-- but returning an integral value would always produce a zero gradient, which
-- is usually not the intended result.
agradient :: (Arrays a, Elt e, Floating e)
          => (Acc a -> Acc (Scalar e))
          -> Acc a
          -> Acc a
agradient f x = areverseAD f x (unit (constant 1))

-- | Provide a custom derivative for a subcomputation.
--
-- __Important note__: The full derivative behaviour of the operation is
-- assumed to be contained within the given reverse derivative function. That
-- is, while both the primal and dual functions are allowed to have free
-- variables, the reverse AD algorithm assumes that these free variable
-- references can be assumed to contribute no adjoints at all to the referenced
-- values.
--
-- This function allows you to define a new primitive operation for the reverse
-- AD transformation as implemented by the other functions in this module.
-- 'customDeriv' defines an expression-level operation, while 'acustomDeriv'
-- defines an array-level operation.
--
-- The first argument is the usual semantics of the operation; outside of
-- reverse AD, the semantics of an operation defined using 'customDeriv' is
-- exactly this first argument. Inside reverse AD, however, the /derivative/ of
-- the operation is assumed to be precisely the second argument. This
-- derivative function gets two arguments: the original (primal) input value of
-- the operation and the reverse derivative (adjoint) of the /output/ of the
-- operation. It should then return the adjoint of the input value.
--
-- For example, to define a new operation that squares its argument, you might
-- write the following:
--
-- @
-- square :: Exp Float -> Exp Float
-- square = customDeriv (\\x -> x * x) (\\x d -> d * 2 * x)
-- @
--
-- This is correct since the derivative of the input of (@\\x -> x * x@) is
-- @2x@ times the derivative of the output value, by the chain rule.
--
-- Of course, the built-in reverse AD algorithm can very well handle a function
-- like @\\x -> x * x@; this is just an example.
--
-- Creating custom derivatives may be useful for two reasons:
--
--     1. To use an operation that the built-in reverse AD algorithm doesn't
--        support, but that you do know the derivative of;
--     2. To give a more efficient implementation of the derivative of an
--        operation, perhaps making use of additional properties of your
--        function that the built-in reverse AD algorithm does not spot.
customDeriv :: forall a b. (Elt a, Elt b)
            => (Exp a -> Exp b)
            -> (Exp a -> Exp b -> Exp a)
            -> Exp a -> Exp b
customDeriv f f' (Exp x) = mkExp $ EcustomDeriv (eltR @b) (unExp . f . Exp) (unExp . A.uncurry f' . Exp) x

-- | Provide a custom derivative for a subcomputation.
--
-- __Important note__: The full derivative behaviour of the operation is
-- assumed to be contained within the given reverse derivative function. That
-- is, while both the primal and dual functions are allowed to have free
-- variables, the reverse AD algorithm assumes that these free variable
-- references can be assumed to contribute no adjoints at all to the referenced
-- values.
--
-- For more information about how custom derivatives work, see the
-- documentation for the expression-level equivalent: 'customDeriv'.
acustomDeriv :: forall a b. (Arrays a, Arrays b)
             => (Acc a -> Acc b)
             -> (Acc a -> Acc b -> Acc a)
             -> Acc a -> Acc b
acustomDeriv f f' x = Acc $ applyAcc (AcustomDeriv (arraysR @b)) f (A.uncurry f') x
