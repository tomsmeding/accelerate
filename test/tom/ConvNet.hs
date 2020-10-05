{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
module ConvNet where

import Data.Functor.Identity
import System.Random

import qualified Data.Array.Accelerate as A
import Data.Array.Accelerate (Z(..), (:.)((:.)), pattern Z_, pattern (::.))
import qualified Data.Array.Accelerate.Sugar.Shape as Shape

import Neural.Help


type Image = A.Array A.DIM3 Float
type Weights = A.Matrix Float
type Kernel = A.Array A.DIM4 Float  -- Z :. (output channel) :. (input channel) :. (y offset) :. (x offset)

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

data Geometry' c =
    Geometry { geomWidth :: Int
             , geomHeight :: Int
             , geomChannels :: c }
  deriving (Show, Eq)

type Geometry = Geometry' Int
type Geometry1C = Geometry' ()

deriving instance A.Arrays a => Show (Network Identity a)
deriving instance A.Arrays a => Show (Network A.Acc a)
deriving instance Show (NetworkSpec a)

from1C :: Geometry1C -> Geometry
from1C geom = geom { geomChannels = 1 }

outputGeometry :: Network f a -> Geometry
outputGeometry (InputLayer geom) = geom
outputGeometry (DenseLayer geom _ _) = from1C geom
outputGeometry (ConvLayer2dG geom _ _ _ _) = geom

liftNetwork :: Network A.Acc a -> A.Acc a
liftNetwork (InputLayer _) = A.lift ()
liftNetwork (DenseLayer _ w net) = A.T2 (liftNetwork net) w
liftNetwork (ConvLayer2dG _ _ _ w net) = A.T2 (liftNetwork net) w

-- First argument only used as model for the types; its contained arrays are not inspected
unliftNetwork :: Network f a -> A.Acc a -> Network A.Acc a
unliftNetwork (InputLayer geom) _ = InputLayer geom
unliftNetwork (DenseLayer geom _ net) (A.T2 lnet w) = DenseLayer geom w (unliftNetwork net lnet)
unliftNetwork (ConvLayer2dG geom kgeom bnd _ net) (A.T2 lnet w) = ConvLayer2dG geom kgeom bnd w (unliftNetwork net lnet)

-- First argument only used as model for the types; its contained arrays are not inspected
unliftNetwork' :: Network f a -> a -> Network Identity a
unliftNetwork' (InputLayer geom) _ = InputLayer geom
unliftNetwork' (DenseLayer geom _ net) (lnet, w) = DenseLayer geom (Identity w) (unliftNetwork' net lnet)
unliftNetwork' (ConvLayer2dG geom kgeom bnd _ net) (lnet, w) = ConvLayer2dG geom kgeom bnd (Identity w) (unliftNetwork' net lnet)

useNetwork :: Network Identity a -> Network A.Acc a
useNetwork (InputLayer geom) = InputLayer geom
useNetwork (DenseLayer geom (Identity w) net) = DenseLayer geom (A.use w) (useNetwork net)
useNetwork (ConvLayer2dG geom kgeom bnd (Identity w) net) = ConvLayer2dG geom kgeom bnd (A.use w) (useNetwork net)

networkZip :: (forall sh. A.Acc (A.Array sh Float) -> A.Acc (A.Array sh Float) -> A.Acc (A.Array sh Float))
           -> Network A.Acc a -> Network A.Acc a -> Network A.Acc a
networkZip _ (InputLayer geom1) (InputLayer geom2)
  | geom1 == geom2 = InputLayer geom1
networkZip f (DenseLayer geom1 w1 net1) (DenseLayer geom2 w2 net2)
  | geom1 == geom2 = DenseLayer geom1 (f w1 w2) (networkZip f net1 net2)
networkZip f (ConvLayer2dG geom1 kgeom1 bnd1 w1 net1) (ConvLayer2dG geom2 kgeom2 bnd2 w2 net2)
  | geom1 == geom2, kgeom1 == kgeom2, bnd1 == bnd2 = ConvLayer2dG geom1 kgeom1 bnd1 (f w1 w2) (networkZip f net1 net2)
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
randomNetwork = fmap snd . go
  where
    -- Also returns output size
    go :: NetworkSpec a -> IO (Geometry, Network Identity a)
    go (SInput geom) = return (geom, InputLayer geom)
    go (SDense geom net) = do
        (ingeom, net') <- go net
        let ingeom' = assert1C ingeom
        w <- randomWeights ingeom' geom
        return (from1C geom, DenseLayer geom (Identity w) net')
    go (SConv2dG kgeom bnd net) = do
        (ingeom, net') <- go net
        w <- randomKernel (geomChannels ingeom) kgeom
        let outsizef insz k = case bnd of
               ConvShrink -> insz - k + 1
               ConvSame -> insz
               ConvExpand -> insz + k - 1
            outgeom = Geometry { geomWidth = outsizef (geomWidth ingeom) (geomWidth kgeom)
                               , geomHeight = outsizef (geomHeight ingeom) (geomHeight kgeom)
                               , geomChannels = geomChannels kgeom }
        return (outgeom, ConvLayer2dG outgeom kgeom bnd (Identity w) net')

    assert1C :: Geometry -> Geometry1C
    assert1C geom@(Geometry { geomChannels = 1 }) = geom { geomChannels = () }
    assert1C geom = error $ "assert1C: randomNetwork: Input to dense layer has " ++
                                show (geomChannels geom) ++ " channels, should have 1"


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
