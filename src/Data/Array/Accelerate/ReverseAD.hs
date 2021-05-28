{- | An implementation of reverse automatic differentiation (AD) for
Accelerate. This module should be imported qualified; we suggest @AD@.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Data.Array.Accelerate.ReverseAD where

import Data.Array.Accelerate.Language                               ( unit )
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
