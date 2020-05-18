{-# LANGUAGE FlexibleContexts #-}
module Main where

import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Interpreter as I
import Data.Array.Accelerate (Z(..), (:.)(..))


-- Format: ([[1, ...x]], [y])
type Dataset = (A.Matrix Float, A.Vector Float)

type Theta = A.Vector Float

dotprod :: (A.Elt a, Num a) => A.Vector a -> A.Vector a -> a
dotprod v w =
  let Z :. n = A.arrayShape v
  in sum [A.indexArray v (Z :. i) * A.indexArray w (Z :. i) | i <- [0 .. n-1]]

-- Generated with y = 2 * a + b > 1.2
dataset :: Dataset
dataset =
  let (xi, yi) = unzip
        [ ([1, 0.592201, 0.887620], 1)
        , ([1, 0.977664, 0.786781], 1)
        , ([1, 0.984866, 0.637364], 1)
        , ([1, 0.095042, 0.719785], 0)
        , ([1, 0.259553, 0.223710], 0)
        , ([1, 0.775019, 0.716203], 1)
        , ([1, 0.533287, 0.977955], 1)
        , ([1, 0.305722, 0.839927], 1)
        , ([1, 0.279132, 0.535238], 0)
        , ([1, 0.304926, 0.972317], 1)
        , ([1, 0.846427, 0.731793], 1)
        , ([1, 0.636495, 0.838927], 1)
        , ([1, 0.943514, 0.731650], 1)
        , ([1, 0.301785, 0.627461], 1)
        , ([1, 0.440637, 0.134468], 0)
        , ([1, 0.948220, 0.726402], 1)
        , ([1, 0.864635, 0.808614], 1)
        , ([1, 0.187325, 0.471742], 0)
        , ([1, 0.285828, 0.530989], 0)
        , ([1, 0.089730, 0.397127], 0) ]
  in (A.fromList (Z :. 20 :. 3) (concat xi), A.fromList (Z :. 20) yi)

-- TODO: ADD A BIAS/INTERCEPT NUMBER TO THE COMPUTATION
-- Like Matthis described: h(x·y + b) instead of h(x·y) with a 1 in the x vector
loglikelihood :: Dataset -> Theta -> Float
loglikelihood (dataX, dataY) theta =
  let Z :. n :. m = A.arrayShape dataX
  in sum [let yi = A.indexArray dataY (Z :. i)
              dot = sum [A.indexArray dataX (Z :. i :. j) * A.indexArray theta (Z :. j)
                        | j <- [0 .. m-1]]
              e = exp dot
          in -yi * log (1 + recip e) - (1 - yi) * log (1 + e)
         | i <- [0 .. n-1]]

-- Used primitives: Map, ZipWith, Fold, Backpermute
loglikelihoodAcc :: A.Acc Dataset -> A.Acc Theta -> A.Acc (A.Scalar Float)
loglikelihoodAcc (A.T2 dataX dataY) theta =
  let broadTheta = A.backpermute (A.shape dataX) (A.index1 . A.indexHead) theta
      dotprods = A.sum (A.zipWith (*) broadTheta dataX)
      exps = A.map exp dotprods
      dot v w = A.sum (A.zipWith (*) v w)
      left = dataY `dot` A.map (\e -> log (1 + recip e)) exps
      right = A.map (1-) dataY `dot` A.map (\e -> log (1 + e)) exps
  in A.map negate (A.zipWith (+) left right)

main :: IO ()
main = do
  let theta = (A.fromList (Z :. 3) [-1.2, 2, 1])
  print (loglikelihood dataset theta)
  print (I.run (loglikelihoodAcc (A.use dataset) (A.use theta)))
  print (I.run (A.map (A.gradientE id) (A.use (A.fromList Z [1.0 :: Float]))))
