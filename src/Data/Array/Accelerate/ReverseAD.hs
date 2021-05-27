{- | An implementation of reverse automatic differentiation (AD) for
Accelerate. This module should be imported qualified; we suggest @AD@.
-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Data.Array.Accelerate.ReverseAD where

import Data.Array.Accelerate.Smart                                  hiding ( arraysR )
import Data.Array.Accelerate.Sugar.Array                            ( Arrays(..), Array, arrayR )
import Data.Array.Accelerate.Sugar.Elt
import qualified Data.Array.Accelerate.Sugar.Shape                  as Shape


-- | Reverse AD on the expression level. (See 'gradientA' for the array level.)
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
gradient :: (Elt t, Elt e, Floating e)
         => (Exp t -> Exp e)
         -> Exp t
         -> Exp t
gradient f x = reverseAD f x (constant 1)

gradientA :: forall a t. (Arrays a, Elt t)
          => (Acc a -> Acc (Array Shape.Z t))
          -> Acc a
          -- -> Acc (t, a)
          -> Acc a
gradientA = Acc $$ applyAcc $ GradientA (arraysR @a) (arrayR @Shape.Z @t)
