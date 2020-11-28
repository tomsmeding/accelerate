module Playground.Fusion where

-- import qualified Prelude as P
import Prelude (IO, print, id)
import Data.Array.Accelerate


main :: IO ()
main = do
  -- print inputProgram
  print producesTransform
  print looseMapId

inputProgram :: Acc (Scalar Float)
inputProgram =
  let arr = use (fromList Z [1 :: Float])
  in zipWith
       (\x _ -> x)
       (generate Z_ (\_ -> 1 :: Exp Float))
       (zipWith (\x y -> T2 x y)
                (map (\x -> x) arr)
                (map (\x -> x) arr))

shapeTest :: Acc (Matrix Float)
shapeTest =
  let a7 = use (fromList (Z :. (1 :: Int) :. (1 :: Int)) [5.0 :: Float])
      a8 = map (\x0 -> T2 (x0 * x0) x0) a7
      a9 = map (\(T2 x0 _) -> x0) a8
  in zipWith (+)
       (generate (shape a9) (\_ -> 1.0))
       (map (\(T2 _ tup) -> tup) a8)

producesTransform :: Acc (Vector Float) -> Acc (Vector Float)
producesTransform a =
  zipWith (+)
    (zipWith (\x y -> x * 2 * y) a a)
    (map (\x -> x * x) a)

looseMapId :: Acc (Vector Float) -> Acc (Vector Float)
looseMapId a = zipWith (+) a (map id a)
