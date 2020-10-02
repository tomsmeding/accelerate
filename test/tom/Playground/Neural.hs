module Playground.Neural where

-- import qualified Prelude as P
import Prelude (IO, print)
import Data.Array.Accelerate


-- This module explores the program in notes-neural-1layer*.txt. This program results from the following program:
--   import qualified Neural
--   let network1_l1 = A.fromList (Z :. 1 :. 3) [7.9, 3.9, -7.5]
--       network1_l1' = A.use network1_l1
--       input1 = A.use (A.fromList (Z :. 4 :. 3) [0,0,1, 0,1,1, 1,0,1, 1,1,1])
--       output1 = A.use (A.fromList (Z :. 4 :. 1) [0, 1, 1, 0])
--       lossfunc wanted got = A.fold1All (+) (A.map (\x -> x*x) (A.zipWith (-) wanted got))
--   in print $ A.gradientA (\l1 -> lossfunc output1 (Neural.forward (Neural.NextLayer l1 Neural.InputLayer) input1)) network1_l1'

main :: IO ()
main = do
  -- print inputProgram
  -- print afterAD
  -- print afterADunshared
  -- print afterADnoexptemps
  -- print afterADsharedreplicate
  print afterADtranspose

-- As it is received from the result of sharing recovery (cleaned up to conform
-- to Accelerate surface syntax).
inputProgram :: Acc (Matrix Float)
inputProgram =
  gradientA (\a0 ->
     fold1 (+)
       (let a1 = map (\x -> x * x)
                   (zipWith (-)
                      (use (fromList (Z :. 4 :. 1) [0.0, 1.0, 1.0, 0.0]))
                      (let a2 = map (\x -> 1.0 / (1.0 + exp (-x)))
                                  (fold (+) 0.0
                                     (let a3 = let a4 = use (fromList (Z :. 4 :. 3)
                                                              [ 0.0, 0.0, 1.0,
                                                                0.0, 1.0, 1.0,
                                                                1.0, 0.0, 1.0,
                                                                1.0, 1.0, 1.0])
                                               in backpermute
                                                    (let I2 x2 x1 = shape a4 in I2 x1 x2)
                                                    (\(I2 x0 x1) -> I2 x1 x0)
                                                    a4
                                      in zipWith (*)
                                           (replicate (Z_ ::. constant All ::. (let I2 _ x1 = shape a3 in x1) ::. constant All) a0)
                                           (replicate
                                              (Z_ ::. (let I2 x0 _ = shape a0 in x0) ::. constant All ::. constant All)
                                              (backpermute
                                                 (let I2 x0 x1 = shape a3 in I2 x1 x0)
                                                 (\(I2 x0 x1) -> I2 x1 x0)
                                                 a3))))
                       in backpermute
                            (let I2 x0 x1 = shape a2 in I2 x1 x0)
                            (\(I2 x0 x1) -> I2 x1 x0)
                            a2))
        in reshape (Z_ ::. shapeSize (shape a1)) a1))
    (use (fromList (Z :. 1 :. 3) [7.9, 3.9, -7.5]))

-- After the AD pass has eliminated gradientA, and some cleanup has been
-- performed by Trafo.AD.Simplify. The AST this produces is almost equivalent
-- to the one produced with the input program, except for two minor
-- differences:
-- - AD uses plain pairs (lowered as (a, b)) for certain things, whereas this
--   program uses T2 (lowered as (((), a), b)). This adds some () here and
--   there (which shows up as T2 instead of (,) in the AST printout).
-- - Sharing recovery realises that the definitions in this program do not all
--   need to be in 1 let-expression, so it uses some smaller-scoped let's.
afterAD :: Acc (Matrix Float)
afterAD =
  let a0 = use (fromList (Z :. (1 :: Int) :. (3 :: Int))    [ 7.9, 3.9, -7.5])
      a1 = use
             (fromList (Z :. (4 :: Int) :. (3 :: Int))
               [ 0.0, 0.0, 1.0,
                 0.0, 1.0, 1.0,
                 1.0, 0.0, 1.0,
                 1.0, 1.0, 1.0])
      a2 = backpermute (let I2 x0 x1 = shape a1 in I2 x1 x0) (\(I2 x0 x1) -> I2 x1 x0) a1
      a3 = zipWith
             (\x0 x1 -> let x2 = x0 * x1 in T2 x2 (T3 x0 x1 x2))
             (replicate (Z_ ::. constant All ::. (let I2 _ x1 = shape a2 in x1) ::. constant All) a0)
             (replicate
                (Z_ ::. (let I2 x0 _ = shape a0 in x0) ::. constant All ::. constant All)
                (backpermute (let I2 x0 x1 = shape a2 in I2 x1 x0) (\(I2 x0 x1) -> I2 x1 x0) a2))
      a4 = map (\(T2 x0 _) -> x0) a3
      a5 = map
             (\x0 -> let x1 = -x0
                         x2 = exp x1
                         x3 = 1.0 + x2
                         x4 = 1.0 / x3
                     in T2 x4 (T6 1.0 x0 x1 x2 x3 x4))
             (fold (+) 0.0 a4)
      a6 = map (\(T2 x0 _) -> x0) a5
      a7 = zipWith
             (\x0 x1 -> let x2 = x0 - x1 in T2 x2 (T3 x0 x1 x2))
             (use (fromList (Z :. 4 :. 1)    [ 0.0,     1.0,     1.0,     0.0]))
             (backpermute (let I2 x0 x1 = shape a6 in I2 x1 x0) (\(I2 x0 x1) -> I2 x1 x0) a6)
      a8 = map (\x0 -> let x1 = x0 * x0 in T2 x1 (T2 x0 x1)) (map (\(T2 x0 _) -> x0) a7)
      a9 = map (\(T2 x0 _) -> x0) a8
      a10 = reshape (Z_ ::. shapeSize (shape a9)) a9
      a11 = generate Z_ (\_ -> 1.0)
      a12 = zipWith
              (\x0 (T6 x1 _ _ x4 x5 _) -> let x7 = x0 * ((-x1) / (x5 * x5)) in -x7 * x4)
              (permute (+)
                 (generate (shape a6) (\_ -> 0.0))
                 (\(I2 x0 x1) -> Just_ (I2 x1 x0))
                 (map (\(T2 _ x0) -> x0)
                    (zipWith
                       (\x0 _ -> T2 (0.0 + x0) (-x0 + 0.0))
                       (zipWith
                          (\x0 (T2 x1 _) -> x0 * x1 + x0 * x1)
                          (reshape (shape a9) (generate (shape a10) (\_ -> a11 ! Z_)))
                          (map (\(T2 _ tup) -> tup) a8))
                       (map (\(T2 _ tup) -> tup) a7))))
              (map (\(T2 _ (T6 x0 x1 x2 x3 x4 x5)) -> T6 x0 x1 x2 x3 x4 x5) a5)
      a13 = zipWith
              (\x0 (T3 x1 x2 _) -> T2 (0.0 + x0 * x2) (x0 * x1 + 0.0))
              (generate (shape a4) (\(I3 x0 x1 _) -> a12 ! I2 x0 x1))
              (map (\(T2 _ tup) -> tup) a3)
      a14 = map (\(T2 x0 _) -> x0) a13
  in fold1 (+)
       (reshape
          (let I3 x0 x1 x2 = shape a14 in I3 x0 x2 x1)
          (backpermute (let I3 x0 x1 x2 = shape a14 in I3 x0 x2 x1) (\(I3 x0 x1 x2) -> I3 x0 x2 x1) a14))

-- Starting from afterAD, manually reducing sharing of array variables to un-prevent fusion.
-- Types of changes applied:
-- - "shape-prop from X": Previously, the expression contained the
--   subexpression 'shape X'. Since the shape of X can be directly computed
--   based on a dependency of X, the shape expression can be "sunk", or
--   equivalently, the shape computation from X's parent can be propagated to
--   this 'shape X' query.
-- - 'use (Scalar Z [1.0])' is worse than 'generate Z_ (\_ -> 1.0)', since the
--   latter is a compile-time constant, rather than runtime, so it can be fused
--   in.
afterADunshared :: Acc (Matrix Float)
afterADunshared =
  let a0 = use (fromList (Z :. (1 :: Int) :. (3 :: Int))    [ 7.9, 3.9, -7.5])
      a1 = use
             (fromList (Z :. (4 :: Int) :. (3 :: Int))
               [ 0.0, 0.0, 1.0,
                 0.0, 1.0, 1.0,
                 1.0, 0.0, 1.0,
                 1.0, 1.0, 1.0])
      a2 = backpermute (let I2 x0 x1 = shape a1 in I2 x1 x0) (\(I2 x0 x1) -> I2 x1 x0) a1
      a3 = zipWith
             (\x0 x1 -> let x2 = x0 * x1 in T2 x2 (T3 x0 x1 x2))
             (replicate (Z_ ::. constant All ::. (let I2 x1 _ = shape a1 in x1 {- shape-prop from a2 -}) ::. constant All) a0)
             (replicate
                (Z_ ::. (let I2 x0 _ = shape a0 in x0) ::. constant All ::. constant All)
                (backpermute (let I2 x1 x0 = shape a1 in I2 x1 x0 {- shape-prop from a2 -}) (\(I2 x0 x1) -> I2 x1 x0) a2))
      a4 = map (\(T2 x0 _) -> x0) a3
      a5 = map
             (\x0 -> let x1 = -x0
                         x2 = exp x1
                         x3 = 1.0 + x2
                         x4 = 1.0 / x3
                     in T2 x4 (T6 1.0 x0 x1 x2 x3 x4))
             (fold (+) 0.0 a4)
      a6 = map (\(T2 x0 _) -> x0) a5
      a7 = zipWith
             (\x0 x1 -> let x2 = x0 - x1 in T2 x2 (T3 x0 x1 x2))
             (use (fromList (Z :. 4 :. 1)    [ 0.0,     1.0,     1.0,     0.0]))
             (backpermute (let I2 x0 x1 = shape a5 in I2 x1 x0 {- shape-prop from a6 -}) (\(I2 x0 x1) -> I2 x1 x0) a6)
      a8 = map (\x0 -> let x1 = x0 * x0 in T2 x1 (T2 x0 x1)) (map (\(T2 x0 _) -> x0) a7)
      -- a9 = map (\(T2 x0 _) -> x0) a8
      -- a10 = reshape (Z_ ::. shapeSize (shape a8) {- shape-prop from a9 -}) a9
      a11 = generate Z_ (\_ -> 1.0)
      a12 = zipWith
              (\x0 (T6 x1 _ _ x4 x5 _) -> let x7 = x0 * ((-x1) / (x5 * x5)) in -x7 * x4)
              (permute (+)
                 (generate (shape a5 {- shape-prop from a6 -}) (\_ -> 0.0))
                 (\(I2 x0 x1) -> Just_ (I2 x1 x0))
                 (map (\(T2 _ x0) -> x0)
                    (zipWith
                       (\x0 _ -> T2 (0.0 + x0) (-x0 + 0.0))
                       (zipWith
                          (\x0 (T2 x1 _) -> x0 * x1 + x0 * x1)
                          (reshape (shape a8 {- shape-prop from a9 -}) (generate (Z_ ::. shapeSize (shape a8) {- shape-prop from a10, a9 -}) (\_ -> a11 ! Z_)))
                          (map (\(T2 _ tup) -> tup) a8))
                       (map (\(T2 _ tup) -> tup) a7))))
              (map (\(T2 _ (T6 x0 x1 x2 x3 x4 x5)) -> T6 x0 x1 x2 x3 x4 x5) a5)
      a13 = zipWith
              (\x0 (T3 x1 x2 _) -> T2 (0.0 + x0 * x2) (x0 * x1 + 0.0))
              (generate (shape a3 {- shape-prop from a4 -}) (\(I3 x0 x1 _) -> a12 ! I2 x0 x1))
              (map (\(T2 _ tup) -> tup) a3)
      a14 = map (\(T2 x0 _) -> x0) a13
  in fold1 (+)
       (reshape
          (let I3 x0 x1 x2 = shape a14 in I3 x0 x2 x1)
          (backpermute (let I3 x0 x1 x2 = shape a14 in I3 x0 x2 x1) (\(I3 x0 x1 x2) -> I3 x0 x2 x1) a14))

-- Starting from afterADunshared, additionally remove all expression temporary
-- stores. Essentially, this means that expressions use forward AD and the
-- array program uses reverse AD.
-- This is done manually here in the following way: for each primitive
-- returning both a primal output and a primal temporaries tuple, _inline_ that
-- primitive (lifting out its dependencies) in both places where it is used,
-- and fuse in the (map fst) and (map snd) into those inlined versions.
-- Additionally, some more shape propagations are performed, some a bit more
-- complex (shape propagation through zipWith, which introduces 'min's).
afterADnoexptemps :: Acc (Matrix Float)
afterADnoexptemps =
  let a0 = use (fromList (Z :. (1 :: Int) :. (3 :: Int))    [ 7.9, 3.9, -7.5])
      a1 = use
             (fromList (Z :. (4 :: Int) :. (3 :: Int))
               [ 0.0, 0.0, 1.0,
                 0.0, 1.0, 1.0,
                 1.0, 0.0, 1.0,
                 1.0, 1.0, 1.0])
      a2 = backpermute (let I2 x0 x1 = shape a1 in I2 x1 x0) (\(I2 x0 x1) -> I2 x1 x0) a1
      r1 = replicate (Z_ ::. constant All ::. (let I2 x1 _ = shape a1 in x1) ::. constant All) a0
      r2 = replicate
             (Z_ ::. (let I2 x0 _ = shape a0 in x0) ::. constant All ::. constant All)
             (backpermute (let I2 x1 x0 = shape a1 in I2 x1 x0) (\(I2 x0 x1) -> I2 x1 x0) a2)
      shape_r1 = let I2 k n = shape a0
                     I2 m _ = shape a1
                 in I3 k m n
      shape_r2 = let I2 m n = shape a1
                     I2 k _ = shape a0
                 in I3 k m n
      a4 = zipWith (*) r1 r2
      shape_a4 = let I3 r1x0 r1x1 r1x2 = shape_r1
                     I3 r2x0 r2x1 r2x2 = shape_r2
                 in I3 (min r1x0 r2x0) (min r1x1 r2x1) (min r1x2 r2x2)
      f1 = fold (+) 0.0 a4
      a6 = map (\x0 -> 1.0 / (1.0 + exp (-x0))) f1
      u1 = use (fromList (Z :. 4 :. 1)    [ 0.0,     1.0,     1.0,     0.0])
      b1 = backpermute (let I3 x0 x1 _ = shape_a4 in I2 x1 x0) (\(I2 x0 x1) -> I2 x1 x0) a6
      z1 = zipWith (-) u1 b1
      a11 = generate Z_ (\_ -> 1.0)
      a12 = zipWith
              (\x0 (T6 x1 _ _ x4 x5 _) -> let x7 = x0 * ((-x1) / (x5 * x5)) in -x7 * x4)
              (permute (+)
                 (generate (let I3 x0 x1 _ = shape_a4 in I2 x0 x1) (\_ -> 0.0))
                 (\(I2 x0 x1) -> Just_ (I2 x1 x0))
                 (map (\(T2 _ x0) -> x0)
                    (zipWith
                       (\x0 _ -> T2 x0 (-x0))
                       (zipWith
                          (\x0 (T2 x1 _) -> x0 * x1 + x0 * x1)
                          (let shape_a7 = let I2 ux0 ux1 = shape u1
                                              I2 bx0 bx1 = let I3 x0 x1 _ = shape_a4 in I2 x1 x0
                                          in I2 (min ux0 bx0) (min ux1 bx1)
                           in reshape shape_a7 (generate (Z_ ::. shapeSize shape_a7) (\_ -> a11 ! Z_)))
                          (map (\x0 -> let x1 = x0 * x0 in T2 x0 x1) z1))
                       (zipWith (\x0 x1 -> let x2 = x0 - x1 in T3 x0 x1 x2) u1 b1))))
              (map
                 (\x0 -> let x1 = -x0
                             x2 = exp x1
                             x3 = 1.0 + x2
                         in T6 1.0 x0 x1 x2 x3 (1.0 / x3))
                 f1)
      a13 = zipWith
              (\x0 (T2 x1 x2) -> T2 (x0 * x2) (x0 * x1))
              (generate shape_r1 (\(I3 x0 x1 _) -> a12 ! I2 x0 x1))
              (zipWith (\x0 x1 -> T2 x0 x1) r1 r2)
      shape_a13 = shape_a4  -- minshape (shape r1) (minshape (shape r1) (shape r2)) = minshape (shape r1) (shape r2) = shape a4
      a14 = map (\(T2 x0 _) -> x0) a13
  in fold1 (+)
       (reshape
          (let I3 x0 x1 x2 = shape_a13 in I3 x0 x2 x1)
          (backpermute (let I3 x0 x1 x2 = shape_a13 in I3 x0 x2 x1) (\(I3 x0 x1 x2) -> I3 x0 x2 x1) a14))

-- Never store Replicate nodes, just recompute them whenever needed. (This
-- should probably only be if they can indeed be fused in in the place where
-- they are recomputed; is there a situation where a replicate can _not_ be
-- fused in?)
afterADsharedreplicate :: Acc (Matrix Float)
afterADsharedreplicate =
  let a0 = use (fromList (Z :. (1 :: Int) :. (3 :: Int))    [ 7.9, 3.9, -7.5])
      a1 = use
             (fromList (Z :. (4 :: Int) :. (3 :: Int))
               [ 0.0, 0.0, 1.0,
                 0.0, 1.0, 1.0,
                 1.0, 0.0, 1.0,
                 1.0, 1.0, 1.0])
      a2 = backpermute (let I2 x0 x1 = shape a1 in I2 x1 x0) (\(I2 x0 x1) -> I2 x1 x0) a1
      b0 = backpermute (let I2 x1 x0 = shape a1 in I2 x1 x0) (\(I2 x0 x1) -> I2 x1 x0) a2
      shape_r1 = let I2 k n = shape a0
                     I2 m _ = shape a1
                 in I3 k m n
      shape_r2 = let I2 m n = shape a1
                     I2 k _ = shape a0
                 in I3 k m n
      a4 = zipWith (*)
              (replicate (Z_ ::. constant All ::. (let I2 x1 _ = shape a1 in x1) ::. constant All) a0)  -- = r1
              (replicate (Z_ ::. (let I2 x0 _ = shape a0 in x0) ::. constant All ::. constant All) b0)  -- = r2
      shape_a4 = let I3 r1x0 r1x1 r1x2 = shape_r1
                     I3 r2x0 r2x1 r2x2 = shape_r2
                 in I3 (min r1x0 r2x0) (min r1x1 r2x1) (min r1x2 r2x2)
      f1 = fold (+) 0.0 a4
      a6 = map (\x0 -> 1.0 / (1.0 + exp (-x0))) f1
      u1 = use (fromList (Z :. 4 :. 1)    [ 0.0,     1.0,     1.0,     0.0])
      b1 = backpermute (let I3 x0 x1 _ = shape_a4 in I2 x1 x0) (\(I2 x0 x1) -> I2 x1 x0) a6
      z1 = zipWith (-) u1 b1
      a11 = generate Z_ (\_ -> 1.0)
      a12 = zipWith
              (\x0 (T6 x1 _ _ x4 x5 _) -> let x7 = x0 * ((-x1) / (x5 * x5)) in -x7 * x4)
              (permute (+)
                 (generate (let I3 x0 x1 _ = shape_a4 in I2 x0 x1) (\_ -> 0.0))
                 (\(I2 x0 x1) -> Just_ (I2 x1 x0))
                 (map (\(T2 _ x0) -> x0)
                    (zipWith
                       (\x0 _ -> T2 x0 (-x0))
                       (zipWith
                          (\x0 (T2 x1 _) -> x0 * x1 + x0 * x1)
                          (let shape_a7 = let I2 ux0 ux1 = shape u1
                                              I2 bx0 bx1 = let I3 x0 x1 _ = shape_a4 in I2 x1 x0
                                          in I2 (min ux0 bx0) (min ux1 bx1)
                           in reshape shape_a7 (generate (Z_ ::. shapeSize shape_a7) (\_ -> a11 ! Z_)))
                          (map (\x0 -> let x1 = x0 * x0 in T2 x0 x1) z1))
                       (zipWith (\x0 x1 -> let x2 = x0 - x1 in T3 x0 x1 x2) u1 b1))))
              (map
                 (\x0 -> let x1 = -x0
                             x2 = exp x1
                             x3 = 1.0 + x2
                         in T6 1.0 x0 x1 x2 x3 (1.0 / x3))
                 f1)
      a13 = zipWith
              (\x0 (T2 x1 x2) -> T2 (x0 * x2) (x0 * x1))
              (generate shape_r1 (\(I3 x0 x1 _) -> a12 ! I2 x0 x1))
              (zipWith (\x0 x1 -> T2 x0 x1)
                  (replicate (Z_ ::. constant All ::. (let I2 x1 _ = shape a1 in x1) ::. constant All) a0)  -- = r1
                  (replicate (Z_ ::. (let I2 x0 _ = shape a0 in x0) ::. constant All ::. constant All) b0))  -- = r2
      shape_a13 = shape_a4  -- minshape (shape r1) (minshape (shape r1) (shape r2)) = minshape (shape r1) (shape r2) = shape a4
      a14 = map (\(T2 x0 _) -> x0) a13
  in fold1 (+)
       (reshape
          (let I3 x0 x1 x2 = shape_a13 in I3 x0 x2 x1)
          (backpermute (let I3 x0 x1 x2 = shape_a13 in I3 x0 x2 x1) (\(I3 x0 x1 x2) -> I3 x0 x2 x1) a14))

-- The derivative of a transpose is a transpose, not a permute.
-- To be more precise, the following:
--   permute (+) (generate _ (\_ -> 0.0)) (\idx -> Just_ (permutation_of idx)) a
-- is equal to:
--   backpermute (shape a) (\idx -> inverse_permutation_of idx) a
-- where 'permutation_of' is an index permutation, and 'inverse_permutation_of'
-- is its algebraic inverse permutation.
-- (Also some more shape propagation.)
-- This version is finally optimised to the point where after fusion, only the
-- input 'use' calls remain, as well as two 'fold' calls, nothing else except
-- delayed representations. That may be optimal (ignoring expression-level
-- stuff, which LLVM will hopefully fix for us).
afterADtranspose :: Acc (Matrix Float)
afterADtranspose =
  let a0 = use (fromList (Z :. (1 :: Int) :. (3 :: Int))    [ 7.9, 3.9, -7.5])
      a1 = use
             (fromList (Z :. (4 :: Int) :. (3 :: Int))
               [ 0.0, 0.0, 1.0,
                 0.0, 1.0, 1.0,
                 1.0, 0.0, 1.0,
                 1.0, 1.0, 1.0])
      a2 = backpermute (let I2 x0 x1 = shape a1 in I2 x1 x0) (\(I2 x0 x1) -> I2 x1 x0) a1
      b0 = backpermute (let I2 x1 x0 = shape a1 in I2 x1 x0) (\(I2 x0 x1) -> I2 x1 x0) a2
      shape_r1 = let I2 k n = shape a0
                     I2 m _ = shape a1
                 in I3 k m n
      shape_r2 = let I2 m n = shape a1
                     I2 k _ = shape a0
                 in I3 k m n
      a4 = zipWith (*)
              (replicate (Z_ ::. constant All ::. (let I2 x1 _ = shape a1 in x1) ::. constant All) a0)  -- = r1
              (replicate (Z_ ::. (let I2 x0 _ = shape a0 in x0) ::. constant All ::. constant All) b0)  -- = r2
      shape_a4 = let I3 r1x0 r1x1 r1x2 = shape_r1
                     I3 r2x0 r2x1 r2x2 = shape_r2
                 in I3 (min r1x0 r2x0) (min r1x1 r2x1) (min r1x2 r2x2)
      f1 = fold (+) 0.0 a4
      a6 = map (\x0 -> 1.0 / (1.0 + exp (-x0))) f1
      u1 = use (fromList (Z :. 4 :. 1)    [ 0.0,     1.0,     1.0,     0.0])
      b1 = backpermute (let I3 x0 x1 _ = shape_a4 in I2 x1 x0) (\(I2 x0 x1) -> I2 x1 x0) a6
      z1 = zipWith (-) u1 b1
      a11 = generate Z_ (\_ -> 1.0)
      shape_a7 = let I2 ux0 ux1 = shape u1
                     I2 bx0 bx1 = let I3 x0 x1 _ = shape_a4 in I2 x1 x0
                 in I2 (min ux0 bx0) (min ux1 bx1)
      m1 = map (\(T2 _ x0) -> x0)
             (zipWith
                (\x0 _ -> T2 x0 (-x0))
                (zipWith
                   (\x0 (T2 x1 _) -> x0 * x1 + x0 * x1)
                   (reshape shape_a7 (generate (Z_ ::. shapeSize shape_a7) (\_ -> a11 ! Z_)))
                   (map (\x0 -> let x1 = x0 * x0 in T2 x0 x1) z1))
                (zipWith (\x0 x1 -> let x2 = x0 - x1 in T3 x0 x1 x2) u1 b1))
      shape_m1 = let I2 ax0 ax1 = shape_a7
                     I2 bx0 bx1 = shape z1
                     I2 cx0 cx1 = shape u1
                     I2 dx0 dx1 = shape b1
                 in I2 (min (min ax0 bx0) (min cx0 dx0)) (min (min ax1 bx1) (min cx1 dx1))
      a12 = zipWith
              (\x0 (T6 x1 _ _ x4 x5 _) -> let x7 = x0 * ((-x1) / (x5 * x5)) in -x7 * x4)
              (backpermute shape_m1 (\(I2 x1 x0) -> I2 x0 x1) m1)
              (map
                 (\x0 -> let x1 = -x0
                             x2 = exp x1
                             x3 = 1.0 + x2
                         in T6 1.0 x0 x1 x2 x3 (1.0 / x3))
                 f1)
      a13 = zipWith
              (\x0 (T2 x1 x2) -> T2 (x0 * x2) (x0 * x1))
              (generate shape_r1 (\(I3 x0 x1 _) -> a12 ! I2 x0 x1))
              (zipWith (\x0 x1 -> T2 x0 x1)
                  (replicate (Z_ ::. constant All ::. (let I2 x1 _ = shape a1 in x1) ::. constant All) a0)  -- = r1
                  (replicate (Z_ ::. (let I2 x0 _ = shape a0 in x0) ::. constant All ::. constant All) b0))  -- = r2
      shape_a13 = shape_a4  -- minshape (shape r1) (minshape (shape r1) (shape r2)) = minshape (shape r1) (shape r2) = shape a4
      a14 = map (\(T2 x0 _) -> x0) a13
  in fold1 (+)
       (reshape
          (let I3 x0 x1 x2 = shape_a13 in I3 x0 x2 x1)
          (backpermute (let I3 x0 x1 x2 = shape_a13 in I3 x0 x2 x1) (\(I3 x0 x1 x2) -> I3 x0 x2 x1) a14))
