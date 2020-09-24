{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module ADHelp where

import Data.List (intercalate)
import qualified Data.List as List

import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Interpreter as I
import Data.Array.Accelerate (Z(..))


class (A.Elt a, A.Lift A.Exp a, a ~ A.Plain a, Show a) => FinDiff a where
  hfindiff :: Float -> (a -> Float) -> a -> a

  findiff :: (a -> Float) -> a -> a
  findiff = hfindiff 1e-5

instance FinDiff Float where
  hfindiff h f x = (f (x + h) - f (x - h)) / (2 * h)

instance (FinDiff a, FinDiff b) => FinDiff (a, b) where
  hfindiff h f (x, y) = (hfindiff h (\x' -> f (x', y)) x, hfindiff h (\y' -> f (x, y')) y)

instance (FinDiff a, FinDiff b, FinDiff c) => FinDiff (a, b, c) where
  hfindiff h f (x, y, z) = (hfindiff h (\x' -> f (x', y, z)) x, hfindiff h (\y' -> f (x, y', z)) y, hfindiff h (\z' -> f (x, y, z')) z)


runExp :: (FinDiff a, A.Elt b) => (A.Exp a -> A.Exp b) -> a -> b
runExp f x =
  let res = I.run (A.unit (f (A.lift x)))
  in A.indexArray res Z

compareAD :: FinDiff a => (A.Exp a -> A.Exp Float) -> (a -> Float) -> a -> IO ()
compareAD facc fnative x =
  let res1 = runExp (A.gradientE facc) x
      res2 = [hfindiff (10.0 ** ex) fnative x | ex <- [-3, -4, -5]]
  in do
      putStrLn ("\x1B[1mAccelerate AD: " ++ show res1 ++ "\x1B[0m")
      putStrLn ("\x1B[1mFinite differencing: " ++ intercalate ", " (map show res2) ++ "\x1B[0m")


class (A.Arrays a, Show a) => AFinDiff a where
  ahfindiff :: Float -> (A.Acc a -> A.Acc (A.Scalar Float)) -> a -> a

  afindiff :: (A.Acc a -> A.Acc (A.Scalar Float)) -> a -> a
  afindiff = ahfindiff 1e-5

  -- | All arrays must have the same shape. Summarises many arrays in a single
  -- array elementwise.
  fdfmap :: ([Float] -> Float) -> [a] -> a

instance A.Shape sh => AFinDiff (A.Array sh Float) where
  ahfindiff h f x =
    A.fromList (A.arrayShape x)
        [(the' (I.run (f adds')) - the' (I.run (f subs'))) / (2 * h)
        | elempairs <- mutations (\x1 -> (x1 + h, x1 - h))
                                 (\x1 -> (x1, x1))
                                 (A.toList x)
        , let (adds, subs) = unzip elempairs
              adds' = A.use (A.fromList (A.arrayShape x) adds)
              subs' = A.use (A.fromList (A.arrayShape x) subs)
              the' = (`A.indexArray` Z)]

  fdfmap f xs@(x0:_) =
    A.fromList (A.arrayShape x0)
        [f (map (`A.linearIndexArray` i) xs)
        | i <- [0 .. A.arraySize x0 - 1]]
  fdfmap _ _ = error "fdfmap: Cannot extract shape from empty list of arrays"

instance (AFinDiff a, AFinDiff b) => AFinDiff (a, b) where
  ahfindiff h f (x, y) =
    (ahfindiff h (\x' -> f (A.T2 x' (A.use y))) x, ahfindiff h (\y' -> f (A.T2 (A.use x) y')) y)

  fdfmap f xs = (fdfmap f (map fst xs), fdfmap f (map snd xs))

-- f applied at pointwise mutations, g at all other entries
mutations :: (a -> b) -> (a -> b) -> [a] -> [[b]]
mutations f g = go id
  where
    go _ [] = []
    go build (x:xs) = build (f x : map g xs) : go (build . (g x :)) xs

aCompareAD :: AFinDiff a => (A.Acc a -> A.Acc (A.Scalar Float)) -> a -> IO ()
aCompareAD facc x =
  let res1 = I.run1 (A.gradientA facc) x
      pollxs = [2.0 ** (-ex) | ex <- [2..7]]
      res2 = [ahfindiff pollx facc x | pollx <- pollxs]
      res2' = fdfmap (\ys -> lagrangeInterp (zip pollxs ys) 0) res2
      zipList = zipWith (\a b -> [a, b])
      res2'' = fdfmap (\ys -> let [_, b] = olsRegression (zipList pollxs (repeat 1)) ys
                              in b)
                      res2
      absdiffs xref xcmp = fdfmap (\[xr, xc] -> abs (xc - xr)) [xref, xcmp]
  in do
      length (show res1) `seq` return ()
      length (show res2) `seq` return ()
      putStrLn ("\x1B[1mAccelerate AD: " ++ show res1 ++ "\x1B[0m")
      -- putStrLn "\x1B[1mFinite differencing:"
      -- mapM_ putStrLn $ zipWith (curry show) pollxs res2
      -- putStr "\x1B[0m"
      -- putStrLn ("\x1B[1mFinite differencing + Richardson: " ++ show res2' ++ "\x1B[0m")
      -- putStrLn ("\x1B[1mFinite differencing + Richardson [abs.diff.]: " ++ show (absdiffs res1 res2') ++ "\x1B[0m")
      -- putStrLn ("\x1B[1mFinite differencing + OLS: " ++ show res2'' ++ "\x1B[0m")
      putStrLn ("\x1B[1mFinite differencing + OLS [abs.diff.]: " ++ show (absdiffs res1 res2'') ++ "\x1B[0m")

lagrangeInterp :: Fractional a => [(a, a)] -> a -> a
lagrangeInterp points evalx =
  sum [yi * product [(evalx - xj) / (xi - xj)
                    | (j, (xj, _)) <- zip [0..] points
                    , j /= i]
      | (i, (xi, yi)) <- zip [0::Int ..] points]

-- Ordinary least squares regression
olsRegression :: Fractional a => [[a]] -> [a] -> [a]
olsRegression xmat yvec =
  let xmat' = List.transpose xmat
      matmul x y = [[sum (zipWith (*) xrow ycol) | ycol <- List.transpose y] | xrow <- x]
      matvec x y = [sum (zipWith (*) xrow y) | xrow <- x]
      matinv [[a,b],[c,d]] = let discr = a * d - b * c
                             in [[d/discr, -b/discr], [-c/discr, a/discr]]
      matinv _ = error "olsRegression not implemented for more than 2 parameters"
  in matinv (xmat' `matmul` xmat) `matvec` (xmat' `matvec` yvec)
