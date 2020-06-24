{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
module Data.Array.Accelerate.Trafo.AD.Algorithms where

import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)


floodfill :: Ord a => a -> (a -> [a]) -> Set a -> Set a
floodfill startpt nbfunc stopset = go mempty (Set.singleton startpt)
  where
    go body rim =
        let newrim = Set.fromList (concatMap nbfunc (Set.toList rim)) Set.\\ stopset
            newbody = body <> rim
        in if Set.null newrim
               then newbody
               else go newbody newrim

-- 'afterfunc' should give all nodes that must come after its argument.
topsort :: forall t a. (Foldable t, Ord a) => [a] -> (a -> t a) -> [a]
topsort = topsort' id

-- 'afterfunc' should give all nodes that must come after its argument.
-- 'ordinject' should be an **injection** from 'a' into an Ord type 'orda'.
--   This injectivity is not checked.
topsort' :: forall t a orda. (Foldable t, Ord orda) => (a -> orda) -> [a] -> (a -> t a) -> [a]
topsort' ordinject nodes afterfunc =
    let incoming = Map.fromListWith (\(n, num1) (_, num2) -> (n, num1 + num2)) $
                        [(ordinject n, (n, 0)) | n <- nodes] ++
                        [(ordinject n', (n', 1)) | n <- nodes, n' <- toList (afterfunc n)]
        headNodes = map fst (Map.elems (Map.filter ((== 0) . snd) incoming))
    in if Map.size incoming == length nodes
           then go incoming headNodes
           else error "topsort: afterfunc gaves nodes outside 'nodes' argument"
  where
    go :: Map orda (a, Int) -> [a] -> [a]
    go _ [] = []
    go incoming (n:stk) =
        let nexts = toList (afterfunc n)
            incoming' = foldr (\n' -> Map.adjust (fmap pred) (ordinject n')) incoming nexts
            newHeads = filter (\n' -> snd (incoming' Map.! ordinject n') == 0) nexts
        in n : go incoming' (newHeads ++ stk)
