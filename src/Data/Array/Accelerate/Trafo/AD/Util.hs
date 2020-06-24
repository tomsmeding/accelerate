{-# LANGUAGE TupleSections #-}
module Data.Array.Accelerate.Trafo.AD.Util where

import Data.Function (on)
import Data.List
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Ord (comparing)


oppositeGraph :: Ord a => Map a [a] -> Map a [a]
oppositeGraph graph =
    let nodes = concat [k : vs | (k, vs) <- Map.assocs graph]
        edges = map ((,) <$> fst . head <*> map snd)
                . groupBy ((==) `on` fst)
                . sortBy (comparing fst)
                $ [(to, from) | (from, tos) <- Map.assocs graph, to <- tos]
    in Map.fromList (map (,[]) nodes ++ edges)
