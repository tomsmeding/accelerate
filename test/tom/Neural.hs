{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Neural (forward, matmat, matvec, Network(..)) where

import qualified Data.Array.Accelerate as A
import Data.Array.Accelerate (Z(..), (:.)(..))

type Weights = A.Matrix Float
type RowBatch = A.Matrix Float
type ColBatch = A.Matrix Float

data Network a where
    InputLayer :: Network ()
    NextLayer :: A.Acc Weights -> Network a -> Network (a, ())

-- layers: from closest to input, to output layer; Z :. output :. input
-- input: Z :. batchsize :. vector
-- output: Z :. batchsize :. vector
forward :: Network a -> A.Acc RowBatch -> A.Acc RowBatch
forward net input = A.transpose $ applyNetwork (\w i -> A.map sigmoid (matmat w i)) net (A.transpose input)

applyNetwork :: (A.Acc Weights -> A.Acc ColBatch -> A.Acc ColBatch) -> Network a -> A.Acc ColBatch -> A.Acc ColBatch
applyNetwork _ InputLayer i = i
applyNetwork f (NextLayer ws net) i = f ws (applyNetwork f net i)

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
