{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module TestSuite.Util where

import qualified Data.Array.Accelerate as A


data ShapeType sh where
  SZ :: ShapeType A.Z
  SCons :: ShapeType sh -> ShapeType (sh A.:. Int)

class (Eq sh, A.Shape sh) => Shape sh where
  magicShapeType :: ShapeType sh

instance Shape A.Z where
  magicShapeType = SZ

instance Shape sh => Shape (sh A.:. Int) where
  magicShapeType = SCons magicShapeType

shapeSize :: Shape sh => sh -> Int
shapeSize = go magicShapeType
  where go :: ShapeType sh -> sh -> Int
        go SZ _ = 1
        go (SCons st) (sh A.:. n) = n * go st sh

enumShape :: Shape sh => sh -> [sh]
enumShape = go magicShapeType
  where
    go :: ShapeType sh -> sh -> [sh]
    go SZ A.Z = [A.Z]
    go (SCons sht) (sh A.:. n) = [idx A.:. i | idx <- go sht sh, i <- [0 .. n-1]]
