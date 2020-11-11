{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module ADHelp where

import Data.Functor.Identity
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
  fdfmap f l = runIdentity (fdfmap' (Identity . f) l)

  -- | Same as fdfmap, except the function may be effectful.
  fdfmap' :: Applicative f => ([Float] -> f Float) -> [a] -> f a

  -- | List of all values in all arrays in the tuple.
  fdtoList :: a -> [Float]

  -- | The total number of values in the arrays.
  fdTotalSize :: a -> Int

instance A.Shape sh => AFinDiff (A.Array sh Float) where
  ahfindiff h f x =
    A.fromList (A.arrayShape x)
        [(the' (I.run (A.zipWith (-) (f adds') (f subs')))) / (2 * h)
        | elempairs <- mutations (\x1 -> (x1 + h, x1 - h))
                                 (\x1 -> (x1, x1))
                                 (A.toList x)
        , let (adds, subs) = unzip elempairs
              adds' = A.use (A.fromList (A.arrayShape x) adds)
              subs' = A.use (A.fromList (A.arrayShape x) subs)
              the' = (`A.indexArray` Z)]

  fdfmap' f xs@(x0:_) =
    A.fromList (A.arrayShape x0) <$>
        traverse f [map (`A.linearIndexArray` i) xs | i <- [0 .. A.arraySize x0 - 1]]
  fdfmap' _ _ = error "fdfmap: Cannot extract shape from empty list of arrays"

  fdtoList = A.toList
  fdTotalSize = A.arraySize

instance (AFinDiff a, AFinDiff b) => AFinDiff (a, b) where
  ahfindiff h f (x, y) =
    (ahfindiff h (\x' -> f (A.T2 x' (A.use y))) x, ahfindiff h (\y' -> f (A.T2 (A.use x) y')) y)

  fdfmap' f xs = (,) <$> fdfmap' f (map fst xs) <*> fdfmap' f (map snd xs)

  fdtoList (x, y) = fdtoList x ++ fdtoList y
  fdTotalSize (x, y) = fdTotalSize x + fdTotalSize y

data AFinDiffRes a = AFinDiffRes [Float] [a]

afindiffPerform :: AFinDiff a => (A.Acc a -> A.Acc (A.Scalar Float)) -> a -> AFinDiffRes a
afindiffPerform facc x =
  let pollxs = [2.0 ** (-ex) | ex <- [4..7]]
      result = [ahfindiff pollx facc x | pollx <- pollxs]
  in length (show result) `seq` AFinDiffRes pollxs result

afdrSamples :: AFinDiff a => AFinDiffRes a -> [(Float, a)]
afdrSamples (AFinDiffRes pollxs samples) = zip pollxs samples

afdrRichardson :: AFinDiff a => AFinDiffRes a -> a
afdrRichardson (AFinDiffRes pollxs samples) = fdfmap (\ys -> lagrangeInterp (zip pollxs ys) 0) samples

afdrOLS' :: AFinDiff a => AFinDiffRes a -> ((String, Float), a)
afdrOLS' (AFinDiffRes pollxs samples) =
  let zipList = zipWith (\a b -> [a, b])
      (errors, res) =
          fdfmap' (\ys -> let xmat = zipList pollxs (repeat 1)
                              params@[_, b] = olsRegression xmat ys
                              errs = olsErrors params xmat ys
                          in ([errs], b))
                  samples
  in ((unlines ["ols errors: " ++ show errors
               ,"poll xs: " ++ show pollxs
               ,"samples: " ++ show samples], if null errors then 0 else maximum errors)
     ,res)

afdrOLS :: AFinDiff a => AFinDiffRes a -> a
afdrOLS = snd . afdrOLS'

-- f applied at pointwise mutations, g at all other entries
mutations :: (a -> b) -> (a -> b) -> [a] -> [[b]]
mutations f g = go id
  where
    go _ [] = []
    go build (x:xs) = build (f x : map g xs) : go (build . (g x :)) xs

aCompareAD :: AFinDiff a => (A.Acc a -> A.Acc (A.Scalar Float)) -> a -> IO ()
aCompareAD facc x =
  let res1 = I.run1 (A.gradientA facc) x
      afdr = afindiffPerform facc x
      absdiffs xref xcmp = fdfmap (\[xr, xc] -> abs (xc - xr)) [xref, xcmp]
  in do
      afdr `seq` return ()
      putStrLn ("\x1B[1mAccelerate AD: " ++ show res1 ++ "\x1B[0m")
      -- putStrLn "\x1B[1mFinite differencing:"
      -- mapM_ putStrLn $ map show (afdrSamples afdr)
      -- putStr "\x1B[0m"
      let resRich = afdrRichardson afdr
      -- putStrLn ("\x1B[1mFinite differencing + Richardson: " ++ show resRich ++ "\x1B[0m")
      putStrLn ("\x1B[1mFinite differencing + Richardson [abs.diff.]: " ++ show (absdiffs res1 resRich) ++ "\x1B[0m")
      let resOLS = afdrOLS afdr
      -- putStrLn ("\x1B[1mFinite differencing + OLS: " ++ show resOLS ++ "\x1B[0m")
      putStrLn ("\x1B[1mFinite differencing + OLS [abs.diff.]: " ++ show (absdiffs res1 resOLS) ++ "\x1B[0m")

lagrangeInterp :: Fractional a => [(a, a)] -> a -> a
lagrangeInterp points evalx =
  sum [yi * product [(evalx - xj) / (xi - xj)
                    | (j, (xj, _)) <- zip [0..] points
                    , j /= i]
      | (i, (xi, yi)) <- zip [0::Int ..] points]

-- Ordinary least squares regression; computes β such that Xβ ~= Y
olsRegression :: Fractional a => [[a]] -> [a] -> [a]
olsRegression xmat yvec =
  let xmat' = List.transpose xmat
  in matinv (xmat' `matmul` xmat) `matvec` (xmat' `matvec` yvec)

-- Given (β, X, Y), returns the sum-of-squares error between Xβ and Y.
olsErrors :: Fractional a => [a] -> [[a]] -> [a] -> a
olsErrors params xmat yvec =
  sum (zipWith (\x y -> (x - y) * (x - y)) (xmat `matvec` params) yvec)

matmul :: Num a => [[a]] -> [[a]] -> [[a]]
matmul x y = [[sum (zipWith (*) xrow ycol) | ycol <- List.transpose y] | xrow <- x]

matvec :: Num a => [[a]] -> [a] -> [a]
matvec x y = [sum (zipWith (*) xrow y) | xrow <- x]

matinv :: Fractional a => [[a]] -> [[a]]
matinv [[a,b],[c,d]] = let discr = a * d - b * c
                       in [[d/discr, -b/discr], [-c/discr, a/discr]]
matinv _ = error "olsRegression not implemented for more than 2 parameters"


class A.Shape sh => InnerDim sh where
  -- Copies dimension tail of SECOND argument
  onInnerDim :: (A.Exp Int -> A.Exp Int -> A.Exp Int) -> A.Exp sh -> A.Exp sh -> A.Exp sh

instance InnerDim Z where
  onInnerDim _ _ _ = A.constant Z

instance A.Shape sh => InnerDim (sh A.:. Int) where
  onInnerDim f (_ A.::. i) (sh' A.::. j) = sh' A.::. f i j

innerReverse :: (A.Elt a, InnerDim sh) => A.Acc (A.Array sh a) -> A.Acc (A.Array sh a)
innerReverse a = A.backpermute (A.shape a) (onInnerDim (\len i -> len - 1 - i) (A.shape a)) a

afoldl :: (InnerDim sh, A.Elt a) => (A.Exp a -> A.Exp a -> A.Exp a) -> A.Exp a -> A.Acc (A.Array (sh A.:. Int) a) -> A.Acc (A.Array sh a)
afoldl f x0 a = innerReverse (A.fold f x0 (innerReverse a))

data T a = T (T a) (T a) | L a
  deriving (Eq)
instance Show a => Show (T a) where
  show (L a) = show a
  show (T t u) = show (t, u)
