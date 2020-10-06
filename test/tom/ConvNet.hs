{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module ConvNet where

import Control.Monad (when)
import Data.Functor.Identity
-- import Data.Proxy
import System.Random

import qualified Data.Array.Accelerate as A
import Data.Array.Accelerate (Z(..), (:.)((:.)), pattern Z_, pattern (::.))
import qualified Data.Array.Accelerate.Sugar.Shape as Shape

import Neural.Help


type Image = A.Array A.DIM3 Float
type Weights = A.Matrix Float
type Kernel = A.Array A.DIM4 Float  -- Z :. (output channel) :. (input channel) :. (y offset) :. (x offset)
type Kernel3x3 = A.Scalar ((Float, Float, Float), (Float, Float, Float), (Float, Float, Float))

data Network acc a where
    InputLayer :: Geometry  -- geometry of the input (thus, the "output" of the input layer)
               -> Network acc ()
    DenseLayer :: A.Arrays a  -- input must be single-channel
               => Geometry1C  -- (width, height) of output
               -> acc Weights
               -> Network acc a
               -> Network acc (a, Weights)
    ConvLayer2dG :: A.Arrays a
                 => Geometry  -- geometry of the output
                 -> Geometry  -- geometry of the kernel
                 -> ConvBoundary
                 -> acc Kernel
                 -> Network acc a
                 -> Network acc (a, Kernel)
    ConvLayer2dS3x3 :: A.Arrays a
                    => Geometry  -- geometry of the output
                    -> ConvBoundary
                    -> acc Kernel3x3
                    -> Network acc a
                    -> Network acc (a, Kernel3x3)
    -- ConvLayer2dS :: (A.Arrays a, PlainStencil (Z :. Int :. Int) Float stencil pstencil)
    --              => Geometry  -- geometry of the output
    --              -> ConvBoundary
    --              -> acc (A.Scalar pstencil)
    --              -> Network acc a
    --              -> Network acc (a, A.Scalar pstencil)

data ConvBoundary = ConvShrink  -- do not pad; for size n input and size k kernel, output will be size (n-k+1)
                  | ConvSame    -- pad ceil((k-1)/2) zeros on left size, floor((k-1)/2) on right side; output will be same size as input
                  | ConvExpand  -- pad k-1 zeros on both sides; output will be size (n+k-1)
  deriving (Show, Eq)

data NetworkSpec a where
    SInput :: Geometry  -- geometry of the input
           -> NetworkSpec ()
    SDense :: A.Arrays a  -- input must be single-channel
           => Geometry1C  -- (width, height) of the output
           -> NetworkSpec a
           -> NetworkSpec (a, Weights)
    SConv2dG :: A.Arrays a
             => Geometry      -- kernel geometry
             -> ConvBoundary  -- boundary behaviour
             -> NetworkSpec a
             -> NetworkSpec (a, Kernel)
    SConv2dS3x3 :: A.Arrays a
                => ConvBoundary  -- boundary behaviour
                -> NetworkSpec a
                -> NetworkSpec (a, Kernel3x3)
    -- SConv2dS :: A.Arrays a
    --          => Proxy pstencil
    --          -> ConvBoundary
    --          -> NetworkSpec a
    --          -> NetworkSpec (a, A.Scalar pstencil)

data Geometry' c =
    Geometry { geomChannels :: c
             , geomHeight :: Int
             , geomWidth :: Int }
  deriving (Show, Eq)

type Geometry = Geometry' Int
type Geometry1C = Geometry' ()

deriving instance A.Arrays a => Show (Network Identity a)
deriving instance A.Arrays a => Show (Network A.Acc a)
deriving instance Show (NetworkSpec a)

-- class (A.Stencil sh e stencil, A.Shape sh, A.Elt pstencil, A.Show pstencil) => PlainStencil sh e stencil pstencil | pstencil -> stencil, pstencil -> e where
--     zipStencilE :: Proxy sh -> (A.Exp e -> A.Exp e -> A.Exp e) -> A.Exp pstencil -> A.Exp pstencil -> A.Exp pstencil
--     genStencil :: Monad m => Proxy sh -> m e -> m pstencil
--     stencilExtent :: Proxy pstencil -> sh

-- instance (A.Elt e, Show e) => PlainStencil A.DIM1 e (A.Exp e, A.Exp e, A.Exp e) (e, e, e) where
--     zipStencilE _ f (A.T3 a1 a2 a3) (A.T3 b1 b2 b3) = A.T3 (f a1 b1) (f a2 b2) (f a3 b3)
--     genStencil _ g = (,,) <$> g <*> g <*> g
--     stencilExtent _ = Z :. 3

-- instance (A.Elt e, Show e) => PlainStencil A.DIM1 e (A.Exp e, A.Exp e, A.Exp e, A.Exp e, A.Exp e) (e, e, e, e, e) where
--     zipStencilE _ f (A.T5 a1 a2 a3 a4 a5) (A.T5 b1 b2 b3 b4 b5) = A.T5 (f a1 b1) (f a2 b2) (f a3 b3) (f a4 b4) (f a5 b5)
--     genStencil _ g = (,,,,) <$> g <*> g <*> g <*> g <*> g
--     stencilExtent _ = Z :. 5

-- instance (A.Elt e, Show e) => PlainStencil A.DIM1 e (A.Exp e, A.Exp e, A.Exp e, A.Exp e, A.Exp e, A.Exp e, A.Exp e) (e, e, e, e, e, e, e) where
--     zipStencilE _ f (A.T7 a1 a2 a3 a4 a5 a6 a7) (A.T7 b1 b2 b3 b4 b5 b6 b7) = A.T7 (f a1 b1) (f a2 b2) (f a3 b3) (f a4 b4) (f a5 b5) (f a6 b6) (f a7 b7)
--     genStencil _ g = (,,,,,,) <$> g <*> g <*> g <*> g <*> g <*> g <*> g
--     stencilExtent _ = Z :. 7

-- instance (A.Elt e, Show e) => PlainStencil A.DIM1 e (A.Exp e, A.Exp e, A.Exp e, A.Exp e, A.Exp e, A.Exp e, A.Exp e, A.Exp e, A.Exp e) (e, e, e, e, e, e, e, e, e) where
--     zipStencilE _ f (A.T9 a1 a2 a3 a4 a5 a6 a7 a8 a9) (A.T9 b1 b2 b3 b4 b5 b6 b7 b8 b9) = A.T9 (f a1 b1) (f a2 b2) (f a3 b3) (f a4 b4) (f a5 b5) (f a6 b6) (f a7 b7) (f a8 b8) (f a9 b9)
--     genStencil _ g = (,,,,,,,,) <$> g <*> g <*> g <*> g <*> g <*> g <*> g <*> g <*> g
--     stencilExtent _ = Z :. 9

-- instance (CompareShape sh,
--           PlainStencil (sh :. Int) e s1 p1, PlainStencil (sh :. Int) e s2 p2, PlainStencil (sh :. Int) e s3 p3)
--          => PlainStencil (sh :. Int :. Int) e (s1, s2, s3) (p1, p2, p3) where
--     zipStencilE _ f (A.T3 a1 a2 a3) (A.T3 b1 b2 b3) =
--         A.T3 (zipStencilE (Proxy @(sh :. Int)) f a1 b1) (zipStencilE (Proxy @(sh :. Int)) f a2 b2) (zipStencilE (Proxy @(sh :. Int)) f a3 b3)
--     genStencil _ g = let p = Proxy @(sh :. Int) in (,,) <$> genStencil p g <*> genStencil p g <*> genStencil p g
--     stencilExtent _ = (:.3) $ maxshape [stencilExtent (Proxy @p1), stencilExtent (Proxy @p2), stencilExtent (Proxy @p3)]

-- instance (CompareShape sh,
--           PlainStencil (sh :. Int) e s1 p1, PlainStencil (sh :. Int) e s2 p2, PlainStencil (sh :. Int) e s3 p3,
--           PlainStencil (sh :. Int) e s4 p4, PlainStencil (sh :. Int) e s5 p5)
--          => PlainStencil (sh :. Int :. Int) e (s1, s2, s3, s4, s5) (p1, p2, p3, p4, p5) where
--     zipStencilE _ f (A.T5 a1 a2 a3 a4 a5) (A.T5 b1 b2 b3 b4 b5) =
--         A.T5 (zipStencilE (Proxy @(sh :. Int)) f a1 b1) (zipStencilE (Proxy @(sh :. Int)) f a2 b2) (zipStencilE (Proxy @(sh :. Int)) f a3 b3)
--              (zipStencilE (Proxy @(sh :. Int)) f a4 b4) (zipStencilE (Proxy @(sh :. Int)) f a5 b5)
--     genStencil _ g = let p = Proxy @(sh :. Int) in (,,,,) <$> genStencil p g <*> genStencil p g <*> genStencil p g <*> genStencil p g <*> genStencil p g
--     stencilExtent _ = (:.5) $ maxshape [stencilExtent (Proxy @p1), stencilExtent (Proxy @p2), stencilExtent (Proxy @p3)
--                                        ,stencilExtent (Proxy @p4), stencilExtent (Proxy @p5)]

-- instance (CompareShape sh,
--           PlainStencil (sh :. Int) e s1 p1, PlainStencil (sh :. Int) e s2 p2, PlainStencil (sh :. Int) e s3 p3,
--           PlainStencil (sh :. Int) e s4 p4, PlainStencil (sh :. Int) e s5 p5, PlainStencil (sh :. Int) e s6 p6,
--           PlainStencil (sh :. Int) e s7 p7)
--          => PlainStencil (sh :. Int :. Int) e (s1, s2, s3, s4, s5, s6, s7) (p1, p2, p3, p4, p5, p6, p7) where
--     zipStencilE _ f (A.T7 a1 a2 a3 a4 a5 a6 a7) (A.T7 b1 b2 b3 b4 b5 b6 b7) =
--         A.T7 (zipStencilE (Proxy @(sh :. Int)) f a1 b1) (zipStencilE (Proxy @(sh :. Int)) f a2 b2) (zipStencilE (Proxy @(sh :. Int)) f a3 b3)
--              (zipStencilE (Proxy @(sh :. Int)) f a4 b4) (zipStencilE (Proxy @(sh :. Int)) f a5 b5) (zipStencilE (Proxy @(sh :. Int)) f a6 b6)
--              (zipStencilE (Proxy @(sh :. Int)) f a7 b7)
--     genStencil _ g = let p = Proxy @(sh :. Int) in (,,,,,,) <$> genStencil p g <*> genStencil p g <*> genStencil p g <*> genStencil p g <*> genStencil p g
--                                                             <*> genStencil p g <*> genStencil p g
--     stencilExtent _ = (:.7) $ maxshape [stencilExtent (Proxy @p1), stencilExtent (Proxy @p2), stencilExtent (Proxy @p3)
--                                        ,stencilExtent (Proxy @p4), stencilExtent (Proxy @p5), stencilExtent (Proxy @p6)
--                                        ,stencilExtent (Proxy @p7)]

-- instance (CompareShape sh,
--           PlainStencil (sh :. Int) e s1 p1, PlainStencil (sh :. Int) e s2 p2, PlainStencil (sh :. Int) e s3 p3,
--           PlainStencil (sh :. Int) e s4 p4, PlainStencil (sh :. Int) e s5 p5, PlainStencil (sh :. Int) e s6 p6,
--           PlainStencil (sh :. Int) e s7 p7, PlainStencil (sh :. Int) e s8 p8, PlainStencil (sh :. Int) e s9 p9)
--          => PlainStencil (sh :. Int :. Int) e (s1, s2, s3, s4, s5, s6, s7, s8, s9) (p1, p2, p3, p4, p5, p6, p7, p8, p9) where
--     zipStencilE _ f (A.T9 a1 a2 a3 a4 a5 a6 a7 a8 a9) (A.T9 b1 b2 b3 b4 b5 b6 b7 b8 b9) =
--         A.T9 (zipStencilE (Proxy @(sh :. Int)) f a1 b1) (zipStencilE (Proxy @(sh :. Int)) f a2 b2) (zipStencilE (Proxy @(sh :. Int)) f a3 b3)
--              (zipStencilE (Proxy @(sh :. Int)) f a4 b4) (zipStencilE (Proxy @(sh :. Int)) f a5 b5) (zipStencilE (Proxy @(sh :. Int)) f a6 b6)
--              (zipStencilE (Proxy @(sh :. Int)) f a7 b7) (zipStencilE (Proxy @(sh :. Int)) f a8 b8) (zipStencilE (Proxy @(sh :. Int)) f a9 b9)
--     genStencil _ g = let p = Proxy @(sh :. Int) in (,,,,,,,,) <$> genStencil p g <*> genStencil p g <*> genStencil p g <*> genStencil p g <*> genStencil p g
--                                                               <*> genStencil p g <*> genStencil p g <*> genStencil p g <*> genStencil p g
--     stencilExtent _ = (:.9) $ maxshape [stencilExtent (Proxy @p1), stencilExtent (Proxy @p2), stencilExtent (Proxy @p3)
--                                        ,stencilExtent (Proxy @p4), stencilExtent (Proxy @p5), stencilExtent (Proxy @p6)
--                                        ,stencilExtent (Proxy @p7), stencilExtent (Proxy @p8), stencilExtent (Proxy @p8)]

zipStencil3x3 :: (A.Elt a, A.Elt b, A.Elt c)
              => (A.Exp a -> A.Exp b -> A.Exp c)
              -> A.Exp ((a, a, a), (a, a, a), (a, a, a))
              -> A.Exp ((b, b, b), (b, b, b), (b, b, b))
              -> A.Exp ((c, c, c), (c, c, c), (c, c, c))
zipStencil3x3 f (A.T3 (A.T3 a1 a2 a3) (A.T3 a4 a5 a6) (A.T3 a7 a8 a9))
                (A.T3 (A.T3 b1 b2 b3) (A.T3 b4 b5 b6) (A.T3 b7 b8 b9)) =
    A.T3 (A.T3 (f a1 b1) (f a2 b2) (f a3 b3))
         (A.T3 (f a4 b4) (f a5 b5) (f a6 b6))
         (A.T3 (f a7 b7) (f a8 b8) (f a9 b9))

sumStencil3x3 :: (Num (A.Exp e), A.Elt e)
              => A.Exp ((e, e, e), (e, e, e), (e, e, e))
              -> A.Exp e
sumStencil3x3 (A.T3 (A.T3 a1 a2 a3) (A.T3 a4 a5 a6) (A.T3 a7 a8 a9)) =
    a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9

liftStencil3x3 :: A.Elt e
               => A.Stencil3x3 e
               -> A.Exp ((e, e, e), (e, e, e), (e, e, e))
liftStencil3x3 ((a1, a2, a3), (a4, a5, a6), (a7, a8, a9)) = A.T3 (A.T3 a1 a2 a3) (A.T3 a4 a5 a6) (A.T3 a7 a8 a9)

from1C :: Geometry1C -> Geometry
from1C geom = geom { geomChannels = 1 }

assert1C :: Geometry -> Geometry1C
assert1C geom@(Geometry { geomChannels = 1 }) = geom { geomChannels = () }
assert1C geom = error $ "assert1C: randomNetwork: Input to dense layer has " ++
                            show (geomChannels geom) ++ " channels, should have 1"

outputGeometry :: Network f a -> Geometry
outputGeometry (InputLayer geom) = geom
outputGeometry (DenseLayer geom _ _) = from1C geom
outputGeometry (ConvLayer2dG geom _ _ _ _) = geom
outputGeometry (ConvLayer2dS3x3 geom _ _ _) = geom
-- outputGeometry (ConvLayer2dS geom _ _ _) = geom

liftNetwork :: Network A.Acc a -> A.Acc a
liftNetwork (InputLayer _) = A.lift ()
liftNetwork (DenseLayer _ w net) = A.T2 (liftNetwork net) w
liftNetwork (ConvLayer2dG _ _ _ w net) = A.T2 (liftNetwork net) w
liftNetwork (ConvLayer2dS3x3 _ _ w net) = A.T2 (liftNetwork net) w
-- liftNetwork (ConvLayer2dS _ _ w net) = A.T2 (liftNetwork net) w

-- First argument only used as model for the types; its contained arrays are not inspected
unliftNetwork :: Network f a -> A.Acc a -> Network A.Acc a
unliftNetwork (InputLayer geom) _ = InputLayer geom
unliftNetwork (DenseLayer geom _ net) (A.T2 lnet w) = DenseLayer geom w (unliftNetwork net lnet)
unliftNetwork (ConvLayer2dG geom kgeom bnd _ net) (A.T2 lnet w) = ConvLayer2dG geom kgeom bnd w (unliftNetwork net lnet)
unliftNetwork (ConvLayer2dS3x3 geom bnd _ net) (A.T2 lnet w) = ConvLayer2dS3x3 geom bnd w (unliftNetwork net lnet)
-- unliftNetwork (ConvLayer2dS geom bnd _ net) (A.T2 lnet w) = ConvLayer2dS geom bnd w (unliftNetwork net lnet)

-- First argument only used as model for the types; its contained arrays are not inspected
unliftNetwork' :: Network f a -> a -> Network Identity a
unliftNetwork' (InputLayer geom) _ = InputLayer geom
unliftNetwork' (DenseLayer geom _ net) (lnet, w) = DenseLayer geom (Identity w) (unliftNetwork' net lnet)
unliftNetwork' (ConvLayer2dG geom kgeom bnd _ net) (lnet, w) = ConvLayer2dG geom kgeom bnd (Identity w) (unliftNetwork' net lnet)
unliftNetwork' (ConvLayer2dS3x3 geom bnd _ net) (lnet, w) = ConvLayer2dS3x3 geom bnd (Identity w) (unliftNetwork' net lnet)
-- unliftNetwork' (ConvLayer2dS geom bnd _ net) (lnet, w) = ConvLayer2dS geom bnd (Identity w) (unliftNetwork' net lnet)

useNetwork :: Network Identity a -> Network A.Acc a
useNetwork (InputLayer geom) = InputLayer geom
useNetwork (DenseLayer geom (Identity w) net) = DenseLayer geom (A.use w) (useNetwork net)
useNetwork (ConvLayer2dG geom kgeom bnd (Identity w) net) = ConvLayer2dG geom kgeom bnd (A.use w) (useNetwork net)
useNetwork (ConvLayer2dS3x3 geom bnd (Identity w) net) = ConvLayer2dS3x3 geom bnd (A.use w) (useNetwork net)
-- useNetwork (ConvLayer2dS geom bnd (Identity w) net) = ConvLayer2dS geom bnd (A.use w) (useNetwork net)

networkZip :: (A.Exp Float -> A.Exp Float -> A.Exp Float) -> Network A.Acc a -> Network A.Acc a -> Network A.Acc a
networkZip _ (InputLayer geom1) (InputLayer geom2)
  | geom1 == geom2 = InputLayer geom1
networkZip f (DenseLayer geom1 w1 net1) (DenseLayer geom2 w2 net2)
  | geom1 == geom2 = DenseLayer geom1 (A.zipWith f w1 w2) (networkZip f net1 net2)
networkZip f (ConvLayer2dG geom1 kgeom1 bnd1 w1 net1) (ConvLayer2dG geom2 kgeom2 bnd2 w2 net2)
  | geom1 == geom2, kgeom1 == kgeom2, bnd1 == bnd2 = ConvLayer2dG geom1 kgeom1 bnd1 (A.zipWith f w1 w2) (networkZip f net1 net2)
networkZip f (ConvLayer2dS3x3 geom1 bnd1 w1 net1) (ConvLayer2dS3x3 geom2 bnd2 w2 net2)
  | geom1 == geom2, bnd1 == bnd2 = ConvLayer2dS3x3 geom1 bnd1 (A.zipWith (zipStencil3x3 f) w1 w2) (networkZip f net1 net2)
-- networkZip f (ConvLayer2dS geom1 bnd1 w1 net1) (ConvLayer2dS geom2 bnd2 w2 net2)
--   | geom1 == geom2, bnd1 == bnd2 = ConvLayer2dS geom1 bnd1 (A.zipWith (zipStencilE (Proxy @(Z :. Int :. Int)) f) w1 w2) (networkZip f net1 net2)
networkZip _ _ _ = error "networkZip: Unequal network designs"


randomArray :: A.Shape sh => sh -> IO (A.Array sh Float)
randomArray sh = A.fromList sh <$> sequence (replicate (Shape.size sh) (randomRIO (0.0, 1.0)))

randomWeights :: Geometry1C -> Geometry1C -> IO Weights
randomWeights ingeom outgeom =
    randomArray (Z :. geomWidth outgeom * geomHeight outgeom
                   :. geomWidth ingeom * geomHeight ingeom)

randomKernel :: Int -> Geometry -> IO Kernel
randomKernel inchans kgeom =
    randomArray (Z :. geomChannels kgeom
                   :. inchans
                   :. geomHeight kgeom
                   :. geomWidth kgeom)

randomNetwork :: NetworkSpec a -> IO (Network Identity a)
randomNetwork (SInput geom) = return (InputLayer geom)
randomNetwork (SDense geom net) = do
    net' <- randomNetwork net
    let ingeom = assert1C (outputGeometry net')
    w <- randomWeights ingeom geom
    return (DenseLayer geom (Identity w) net')
randomNetwork (SConv2dG kgeom bnd net) = do
    net' <- randomNetwork net
    let ingeom = outputGeometry net'
    w <- randomKernel (geomChannels ingeom) kgeom
    let outsizef insz k = case bnd of
            ConvShrink -> insz - k + 1
            ConvSame -> insz
            ConvExpand -> insz + k - 1
        outgeom = Geometry { geomWidth = outsizef (geomWidth ingeom) (geomWidth kgeom)
                           , geomHeight = outsizef (geomHeight ingeom) (geomHeight kgeom)
                           , geomChannels = geomChannels kgeom }
    return (ConvLayer2dG outgeom kgeom bnd (Identity w) net')
randomNetwork (SConv2dS3x3 bnd net) = do
    net' <- randomNetwork net
    let ingeom = outputGeometry net'
    when (geomChannels ingeom /= 1) $ error "Input to SConv2dS3x3 must be single-channel"
    let gen1 = randomRIO (0.0, 1.0)
        gen3 = (,,) <$> gen1 <*> gen1 <*> gen1
        gen9 = (,,) <$> gen3 <*> gen3 <*> gen3
    w <- A.fromList Z . pure <$> gen9
    let outsizef insz k = case bnd of
            ConvShrink -> insz - k + 1
            ConvSame -> insz
            ConvExpand -> insz + k - 1
        outgeom = Geometry { geomWidth = outsizef (geomWidth ingeom) 3
                           , geomHeight = outsizef (geomHeight ingeom) 3
                           , geomChannels = 1 }
    return (ConvLayer2dS3x3 outgeom bnd (Identity w) net')
-- randomNetwork (SConv2dS proxy bnd net) = do
--     net' <- randomNetwork net
--     let ingeom = outputGeometry net'
--     when (geomChannels ingeom /= 1) $ error "Input to SConv2dS must be single-channel"
--     w <- A.fromList Z . pure <$> genStencil proxy (randomRIO (0.0 :: Float, 1.0))
--     let outsizef insz k = case bnd of
--             ConvShrink -> insz - k + 1
--             ConvSame -> insz
--             ConvExpand -> insz + k - 1
--         Z :. kheight :. kwidth = stencilExtent proxy
--         outgeom = Geometry { geomWidth = outsizef (geomWidth ingeom) kwidth
--                            , geomHeight = outsizef (geomHeight ingeom) kheight
--                            , geomChannels = 1 }
--     return (ConvLayer2dS outgeom bnd (Identity w) net')


forward :: Network A.Acc a -> A.Acc Image -> A.Acc Image
forward (InputLayer _) i = i
forward (DenseLayer _ ws net) i =
    let Geometry { geomWidth = w, geomHeight = h } = outputGeometry net
        i' = A.reshape (A.lift (Z :. h * w)) (forward net i)
    in A.reshape (A.lift (Z :. (1 :: Int) :. h :. w))
                 (A.map sigmoid (ws `matvec` i'))
forward (ConvLayer2dG geom kgeom ConvShrink ws net) i =
    let i' = forward net i
        ingeom = outputGeometry net
        outshape = Z :. geomChannels kgeom :. geomHeight geom :. geomWidth geom
    in A.generate (A.lift outshape)
                  (\(A.I3 ochan y x) ->
                      Shape.iter (Z :. geomChannels ingeom :. geomHeight kgeom :. geomWidth kgeom)
                                 (\idx -> let Z_ ::. ichan ::. dy ::. dx = A.lift idx
                                          in (i' A.! A.I3 ichan (y + dy) (x + dx)) * (ws A.! A.I4 ochan ichan dy dx))
                                 (+) 0)
forward (ConvLayer2dG _ _ bnd _ _) _ = error $ "Convolutional layer for boundary type " ++ show bnd ++ " not yet supported"
forward (ConvLayer2dS3x3 geom ConvShrink ws net) i =
    let i' = forward net i
    in A.backpermute (Z_ ::. (1 :: A.Exp Int) ::. A.constant (geomHeight geom) ::. A.constant (geomWidth geom))
                     (\(Z_ ::. _ ::. y ::. x) -> Z_ ::. y + 1 ::. x + 1) $
       A.stencil (\((a,b,c),(d,e,f),(g,h,j)) -> sumStencil3x3 $ zipStencil3x3 (*) (A.the ws) $ liftStencil3x3 ((a,b,c),(d,e,f),(g,h,j)))
                 (A.function (const 0))
                 (A.slice i' (Z_ ::. (0 :: A.Exp Int) ::. liftAll ::. liftAll))
forward (ConvLayer2dS3x3 _ bnd _ _) _ = error $ "Convolutional Stencil3x3 layer for boundary type " ++ show bnd ++ " not yet supported"


-- class A.Shape sh => CompareShape sh where
--     maxshape :: [sh] -> sh

-- instance CompareShape Z where
--     maxshape _ = Z

-- instance CompareShape sh => CompareShape (sh :. Int) where
--     maxshape l = let (tls, hds) = unzip (map (\(sh :. i) -> (sh, i)) l)
--                  in maxshape tls :. maximum hds
