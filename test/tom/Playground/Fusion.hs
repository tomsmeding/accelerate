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

reportDualExampleProg :: Acc (Vector Float) -> Acc (Scalar Float)
reportDualExampleProg arg =
    let b = map (\x -> x * 3.0) arg
    in sum (map (\x -> x * b ! I1 (round x)) b)

reportDualExampleGrad :: Acc (Vector Float) -> Acc (Vector Float)
reportDualExampleGrad arg =
    let a2 = arg
        primal_1 :: Exp Float -> Exp (Float, (Float, Float, Float))
        primal_1 x = T2 (x * 3.0) (T3 x 3.0 (x * 3.0))
        a1res = map primal_1 a2
        a1 = map fst a1res
        a1tmp = map snd a1res
        a5 = a1
        primal_4 :: Exp Float -> Exp (Float, (Float, Int, Float, Float))
        primal_4 x = T2 (x * a1 ! I1 (round x)) (T4 x (round x) (a1 ! I1 (round x)) (x * a1 ! I1 (round x)))
        a4res = map primal_4 a5
        a4 = map fst a4res
        a4tmp = map snd a4res
        a3 = sum a4
        d3 = generate I0 (\_ -> 1.0)
        d4 = generate (shape a4) (\i -> d3 ! indexTail i)
        dual_4 :: Exp Float -> Exp (Float, Int, Float, Float) -> Exp (Float, ((), ((Bool, DIM1), Float)))
        dual_4 d (T4 x1 x2 x3 _) = T2 x3 (T2 (constant ()) (T2 (T2 (constant True) (I1 x2)) (d * x1)))
        d4res = zipWith dual_4 d4 a4tmp
        d5 = map fst d4res
        d4ia = map snd d4res
        d1 = zipWith (+)
                     (permute (+)
                              (generate (shape a1) (\_ -> 0.0))
                              (\i -> let iai = d4ia ! i
                                     in cond (fst (fst (snd iai))) (Just_ (snd (fst (snd iai)))) Nothing_)
                              (map (\iai -> snd (snd iai)) d4ia))
                     d5
        dual_1 :: Exp Float -> Exp (Float, Float, Float) -> Exp (Float, ())
        dual_1 d (T3 _ x2 _) = T2 (x2 * d) (constant ())
        d1res = zipWith dual_1 d1 a1tmp
        d2 = map fst d1res
        d1ia = map snd d1res
    in d2
