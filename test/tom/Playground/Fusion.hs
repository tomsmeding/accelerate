module Playground.Fusion where

-- import qualified Prelude as P
import Prelude (IO, print)
import Data.Array.Accelerate


main :: IO ()
main = do
  print inputProgram

inputProgram :: Acc (Scalar Float)
inputProgram =
  let arr = use (fromList Z [1 :: Float])
  in zipWith
       (\x _ -> x)
       (generate Z_ (\_ -> 1 :: Exp Float))
       (zipWith (\x y -> T2 x y)
                (map (\x -> x) arr)
                (map (\x -> x) arr))
