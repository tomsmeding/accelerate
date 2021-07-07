{-| Inefficiently compute gradients using forward AD.

If you want to compute a gradient of your Accelerate function, please use the
functionality in 'Data.Array.Accelerate.ReverseAD' instead of this module. This
module is horribly inefficient compared to the reverse AD implementation. It
exists solely as a reference implementation, and as something to play with.
Indeed, it is used in the test suite for the reverse AD algorithm.

This module should be imported qualified; we suggest @AD@.
-}
module Data.Array.Accelerate.ForwardAD.Gradient where

import Data.Array.Accelerate (Array, Scalar, Shape, Elt)
import qualified Data.Array.Accelerate as A


data Ddict r a tan adj = Ddict
    { -- | Zero tangent given a primal value
      dtZeroTan :: a -> tan

    , -- | Zero adjoint given a primal value
      dtZeroAdj :: a -> adj

    , -- | Sum of adjoints in its commutative monoid
      dtAdjSum :: adj -> adj -> adj

    , -- | Gradient using repeated forward AD.
      -- Given:
      -- 1. The value at this point in the program,
      -- 2. A function that computes the tangent of a scalar result given the
      --    tangent of the current value,
      -- 3. The adjoint of that scalar result,
      -- compute the adjoint of the current value.
      dtFwdgrad :: a -> (tan -> r) -> r -> adj

    , -- Dot product of tangent and adjoint, which gives the partial derivative
      -- of the eventual result with respect to the original reference input.
      --   \sum_{i=1}^n ∂x_i/∂α · ∂ζ/∂x_i = ∂ζ/∂α
      dtTanAdjDot :: tan -> adj -> r
    }


floatDict :: Num r => Ddict r r r r
floatDict = Ddict
    { dtZeroTan = const 0
    , dtZeroAdj = const 0
    , dtAdjSum = (+)
    , dtFwdgrad = \_ f adj -> f 1 * adj
    , dtTanAdjDot = \a b -> a * b }

intDict :: Num r => Ddict r a () ()
intDict = Ddict
    { dtZeroTan = \_ -> ()
    , dtZeroAdj = \_ -> ()
    , dtAdjSum = \_ _ -> ()
    , dtFwdgrad = \_ _ _ -> ()
    , dtTanAdjDot = \_ _ -> 0 }

pairDict :: Num r => Ddict r a af ar -> Ddict r b bf br -> Ddict r (a, b) (af, bf) (ar, br)
pairDict t1 t2 = Ddict
    { dtZeroTan = \(x, y) -> (dtZeroTan t1 x, dtZeroTan t2 y)
    , dtZeroAdj = \(x, y) -> (dtZeroAdj t1 x, dtZeroAdj t2 y)
    , dtAdjSum = \(a, b) (x, y) -> (dtAdjSum t1 a x, dtAdjSum t2 b y)
    , dtFwdgrad = \(x, y) f adj ->
          (dtFwdgrad t1 x (\tn -> f (tn, dtZeroTan t2 y)) adj
          ,dtFwdgrad t2 y (\tn -> f (dtZeroTan t1 x, tn)) adj)
    , dtTanAdjDot = \(a, b) (x, y) -> dtTanAdjDot t1 a x + dtTanAdjDot t2 b y
    }

listDict :: Num r => Ddict r a af ar -> Ddict r [a] [af] [ar]
listDict t = Ddict
    { dtZeroTan = map (dtZeroTan t)
    , dtZeroAdj = map (dtZeroAdj t)
    , dtAdjSum = zipWith (dtAdjSum t)
    , dtFwdgrad = \prim f adj ->
          let splits :: [a] -> [([a], a, [a])]
              splits = go id
                where
                  go :: ([a] -> [a]) -> [a] -> [([a], a, [a])]
                  go _ [] = []
                  go pre (x:xs) = (pre [], x, xs) : go (pre . (x :)) xs
          in map (\(pre, x, post) ->
                      dtFwdgrad t x
                                  (\dx -> let pre' = map (dtZeroTan t) pre
                                              post' = map (dtZeroTan t) post
                                          in f (pre' ++ dx : post'))
                                  adj)
                 (splits prim)
    , dtTanAdjDot = (sum .) . zipWith (dtTanAdjDot t)
    }

scalarDict :: (Elt a, Elt af, Elt ar)
           => Ddict r a af ar -> Ddict r (Scalar a) (Scalar af) (Scalar ar)
scalarDict t = Ddict
    { dtZeroTan = amap (dtZeroTan t)
    , dtZeroAdj = amap (dtZeroAdj t)
    , dtAdjSum = azipWith (dtAdjSum t)
    , dtFwdgrad = \prim f adj ->
          A.fromList A.Z
            [dtFwdgrad t (A.indexArray prim A.Z) (f . A.fromList A.Z . pure) adj]
    , dtTanAdjDot = \a b -> dtTanAdjDot t (A.indexArray a A.Z) (A.indexArray b A.Z)
    }

arrayDict :: (Eq sh, Shape sh, Elt a, Elt af, Elt ar, Elt r, Num r)
          => Ddict r a af ar -> Ddict r (Array sh a) (Array sh af) (Array sh ar)
arrayDict t = Ddict
    { dtZeroTan = amap (dtZeroTan t)
    , dtZeroAdj = amap (dtZeroAdj t)
    , dtAdjSum = azipWith (dtAdjSum t)
    , dtFwdgrad = \prim f adj ->
          onehots prim (dtZeroTan t)
                  (\primelt onehot -> dtFwdgrad t primelt (f . onehot) adj)
    , dtTanAdjDot = (asum .) . azipWith (dtTanAdjDot t)
    }
  where
    onehots :: (Eq sh, Shape sh, Elt a, Elt b, Elt e)
            => Array sh e -> (e -> a) -> (e -> (a -> Array sh a) -> b) -> Array sh b
    onehots ref zero f =
        let sh = A.arrayShape ref
        in A.fromFunction sh $ \idx ->
               let elt = A.indexArray ref idx
               in f elt (\one ->
                           A.fromFunction sh
                               (\idx' -> if idx == idx' then one else zero elt))

amap :: (Shape sh, Elt a, Elt b) => (a -> b) -> Array sh a -> Array sh b
amap f a = A.fromFunction (A.arrayShape a) (\idx -> f (A.indexArray a idx))

asum :: (Shape sh, Elt a, Num a) => Array sh a -> a
asum = sum . A.toList

azipWith :: (Eq sh, Shape sh, Elt a, Elt b, Elt c) => (a -> b -> c) -> Array sh a -> Array sh b -> Array sh c
azipWith f a b
  | A.arrayShape a == A.arrayShape b
  = A.fromFunction (A.arrayShape a) (\idx -> f (A.indexArray a idx) (A.indexArray b idx))
  | otherwise
  = error "Unequal array sizes in arrayDict"

forwardGradient :: Num r => Ddict r a af ar -> Ddict r b bf br -> ((a, af) -> bf) -> a -> br -> ar
forwardGradient t1 t2 df arg adjoint =
    dtFwdgrad t1 arg (\tn -> dtTanAdjDot t2 (df (arg, tn)) adjoint) 1
