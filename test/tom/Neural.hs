{-# LANGUAGE TypeOperators #-}
module Neural (forward, matmat, matvec) where

import qualified Data.Array.Accelerate as A
import Data.Array.Accelerate (Z(..), (:.)(..))

-- layers: from closest to input, to output layer; Z :. output :. input
-- input: Z :. batchsize :. vector
-- output: Z :. batchsize :. vector
forward :: A.Acc (A.Matrix Float, A.Matrix Float) -> A.Acc (A.Matrix Float) -> A.Acc (A.Matrix Float)
forward (A.T2 ly1m ly2m) input =
    layer ly2m . layer ly1m $ A.transpose input
  where layer = (A.map sigmoid .) . matmat

sigmoid :: A.Exp Float -> A.Exp Float
sigmoid x = 1 / (1 + exp (-x))

matvec :: A.Acc (A.Matrix Float) -> A.Acc (A.Vector Float) -> A.Acc (A.Vector Float)
matvec mat vec =
    let A.I2 nrows _ = A.shape mat
        vecm = A.replicate (slice2 nrows liftAll) vec
    in A.sum (A.zipWith (*) mat vecm)

matmat :: A.Acc (A.Matrix Float) -> A.Acc (A.Matrix Float) -> A.Acc (A.Matrix Float)
matmat m1 m2 =
    let A.I2 k _ = A.shape m1
        A.I2 _ n = A.shape m2
        m1' = A.replicate (slice3 liftAll n liftAll) m1
        m2' = A.replicate (slice3 k liftAll liftAll) (A.transpose m2)
    in A.sum (A.zipWith (*) m1' m2')

slice2 :: (A.Elt i, A.Elt j) => A.Exp i -> A.Exp j -> A.Exp (Z :. i :. j)
slice2 i j = A.constant Z A.::. i A.::. j

slice3 :: (A.Elt i, A.Elt j, A.Elt k) => A.Exp i -> A.Exp j -> A.Exp k -> A.Exp (Z :. i :. j :. k)
slice3 i j k = A.constant Z A.::. i A.::. j A.::. k

liftAll :: A.Exp A.All
liftAll = A.constant A.All
