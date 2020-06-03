module Optimise (optimise, dimension) where

import qualified Data.Array.Accelerate as A
import Data.Array.Accelerate (Z(..), (:.)(..))


type Theta = A.Vector Float

dimension :: Int
dimension = 10

lossTarget :: A.Acc Theta
lossTarget = A.use (A.fromList (Z :. dimension) [1..])

norm :: A.Acc Theta -> A.Acc (A.Scalar Float)
norm = A.sum . A.map (\x -> x * x)

-- lossFunction :: A.Acc Theta -> A.Acc (A.Scalar Float)
-- lossFunction vec = norm (A.zipWith (-) vec lossTarget)

-- d/dv_i (sum_j (v_j - t_j)^2) = d/dv_i (v_i^2 - 2 v_i t_i + t_i^2) = 2 (v_i - t_i)
lossGradient :: A.Acc Theta -> A.Acc Theta
lossGradient vec = A.map (*2) (A.zipWith (-) vec lossTarget)

optimise :: A.Acc Theta -> A.Acc (A.Scalar Float) -> A.Acc Theta
optimise theta0 lrate =
  A.afst $
    A.awhile (\(A.T2 _ dtheta) -> A.unit (A.the (norm dtheta) A.> 0.1))
             (\(A.T2 theta dtheta) ->
                 let theta' = A.zipWith (-) theta (A.map (* A.the lrate) dtheta)
                 in A.T2 theta' (lossGradient theta'))
             (A.T2 theta0 (lossGradient theta0))
