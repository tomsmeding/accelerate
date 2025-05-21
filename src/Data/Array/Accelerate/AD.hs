{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.AD where

import Data.Array.Accelerate.AD.Types
import Data.Array.Accelerate.Language
import Data.Array.Accelerate.Sugar.Array                            ( Arrays(..), Scalar )
import Data.Array.Accelerate.Sugar.Elt                              ( EltR, Elt )
import Data.Array.Accelerate.Smart                                  hiding ( arraysR )


vjp :: forall a b.
       (Arrays a, Arrays b
       ,Arrays (Ctg a), Arrays (Ctg b)
       ,Ctg (ArraysR a) ~ ArraysR (Ctg a), Ctg (ArraysR b) ~ ArraysR (Ctg b))
    => (Acc a -> Acc b)
    -> Acc a
    -> Acc (Ctg b)
    -> Acc (Ctg a)
vjp = Acc $$$ applyAcc (Avjp (arraysR @a) (arraysR @b))

gradient :: forall a b.
            (Arrays a, Floating b, Elt b
            ,Arrays (Ctg a), Ctg (ArraysR a) ~ ArraysR (Ctg a), EltR b ~ b, Ctg b ~ b)
         => (Acc a -> Acc (Scalar b)) -> Acc a -> Acc (Ctg a)
gradient f x = vjp @a @(Scalar b) f x (unit (constant (1.0 :: b)))
