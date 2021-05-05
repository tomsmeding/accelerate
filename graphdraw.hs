#!/usr/bin/env cabal
{- cabal:
build-depends: base >= 4.14 && < 4.16
             , containers
             , parsec
ghc-options: -Wall -O2
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
module Main where

import Control.Monad (guard)
import Data.Function (on)
import Data.List (groupBy, partition, sort, sortBy)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Ord (comparing)
import Data.Type.Equality ((:~:)(..))
import GHC.Stack (HasCallStack)
import System.Environment (getArgs)
import System.Exit (die)
import qualified Text.Parsec as P
import Unsafe.Coerce (unsafeCoerce)


(!) :: (HasCallStack, Ord k) => Map k v -> k -> v
m ! k = case Map.lookup k m of
          Just v -> v
          Nothing -> error "Map ! not found"

uniq :: Eq a => [a] -> [a]
uniq (x:y:xs) | x == y = uniq (x:xs)
              | otherwise = x : uniq (y:xs)
uniq l = l


data Dir = Fwd | Rev
  deriving (Show)

type family Flip a = r | r -> a where
    Flip 'Fwd = 'Rev
    Flip 'Rev = 'Fwd

newtype Graph (dir :: Dir) = Graph (Map Int (String, [(Int, String)]))
  deriving (Show)

instance Semigroup (Graph dir) where
    Graph a <> Graph b =
        Graph (Map.unionWith (\(s, l) (s', l') ->
                                if s == s' then (s, l <> l')
                                           else (if null s || null s' then s ++ s' else s ++ " | " ++ s', l <> l'))
                             a b)

instance Monoid (Graph dir) where
    mempty = Graph mempty

type Parser = P.Parsec String ()

parse :: String -> Either P.ParseError (Graph 'Fwd)
parse source = P.parse (P.spaces >> pFile <* P.eof) "" source
  where
    pFile = mconcat <$> P.many pLine
    pLine =
        P.choice [do _ <- P.try (P.string "node")
                     P.spaces
                     i <- pString
                     P.spaces
                     name <- pString
                     P.spaces
                     _ <- P.string ";"
                     P.spaces
                     return $ Graph (Map.singleton (read i) (name, []))
                 ,do _ <- P.try (P.string "edge")
                     P.spaces
                     i <- pString
                     P.spaces
                     _ <- P.string "->"
                     P.spaces
                     j <- pString
                     P.spaces
                     label <- pString
                     P.spaces
                     _ <- P.string ";"
                     P.spaces
                     return $ Graph (Map.singleton (read i) ("", [(read j, label)]))
                 ]
    pString :: Parser String
    pString = do
        _ <- P.char '"'
        s <- P.many (P.try $ P.anyChar >>= \case '\\' -> P.anyChar
                                                 '"' -> P.unexpected "\""
                                                 c -> return c)
        _ <- P.char '"'
        return s

toDot :: Graph 'Fwd -> String
toDot (Graph graph) =
    unlines . concat $
        [["digraph G {"]
         -- Reversing seems to, anecdotally, produce graphs that are structurally much more similar to Accelerate's own dot graphs.
        ,reverse ["\t\"" ++ show i ++ "\" [label=\"" ++ show i ++ ":" ++ name ++ "\"];" | (i, (name, _)) <- Map.assocs graph]
        ,["\t\"" ++ show i ++ "\" -> \"" ++ show j ++ "\" [label=\"" ++ label ++ "\"];" | (i, (_, es)) <- Map.assocs graph, (j, label) <- es]
        ,["}"]]

flipFlip :: dir :~: Flip (Flip dir)
flipFlip = unsafeCoerce Refl

oppositeGraph :: HasCallStack => Graph dir -> Graph (Flip dir)
oppositeGraph (Graph graph) =
    let namemap = Map.fromList [(n, name) | (n, (name, _)) <- Map.assocs graph]
    in Graph
       . Map.mapWithKey (\n es -> (namemap ! n, es))
       . Map.fromListWith (++)
       . (++) (map (,[]) (Map.keys graph))
       . map ((,) <$> fst . head <*> map snd)
       . groupBy ((==) `on` fst)
       . sortBy (comparing fst)
       . concatMap (\(n, (_, es)) -> [(j, (n, lab)) | (j, lab) <- es])
       $ Map.assocs graph

assertClosed :: HasCallStack => Graph dir -> Graph dir
assertClosed g@(Graph graph) =
    let nodes = Map.keys graph
        nodes' = uniq . sort $ concat [map fst js | (_, js) <- Map.elems graph]
    in if nodes' `sublistOf` nodes
           then g
           else error (unlines ["assertClosed: not closed"
                               ,"graph = " ++ show g
                               ,"nodes  = " ++ show nodes
                               ,"nodes' = " ++ show nodes'])
  where
    sublistOf :: Eq a => [a] -> [a] -> Bool
    sublistOf [] _ = True
    sublistOf (x:xs) (y:ys)
      | x == y = sublistOf xs ys
      | otherwise = sublistOf (x:xs) ys
    sublistOf _ _ = False

while :: (a -> (Bool, a)) -> a -> a
while f x = let (c, y) = f x
            in if c then while f y else y

opposite :: forall dir. HasCallStack => (Graph dir -> Graph dir) -> Graph (Flip dir) -> Graph (Flip dir)
opposite f
  | Refl <- flipFlip @dir
  = oppositeGraph . assertClosed . f . oppositeGraph

referrentsTo :: Int -> Graph dir -> [Int]
referrentsTo n (Graph graph) = [i | (i, (_, es)) <- Map.assocs graph, n `elem` map fst es]

data Pattern i (dir :: Dir) = PNode i [Pattern i dir]
  deriving (Show)

findPattern :: HasCallStack => Graph dir -> Pattern String dir -> [Pattern Int dir]
findPattern = \g@(Graph graph) pat ->
    matchPatternAny g (Map.keys graph) pat

matchPatternAny :: Graph dir -> [Int] -> Pattern String dir -> [Pattern Int dir]
matchPatternAny graph nodes pat =
    [r | n <- nodes, r <- matchPattern graph n pat]

matchPatternAnyMultiple :: Graph dir -> [Int] -> [Pattern String dir] -> [[Pattern Int dir]]
matchPatternAnyMultiple _ _ [] = [[]]
matchPatternAnyMultiple graph nodes (pat:pats) = do
    result@(PNode i _) <- matchPatternAny graph nodes pat
    rest <- matchPatternAnyMultiple graph (filter (/= i) nodes) pats
    return (result : rest)

matchPattern :: HasCallStack => Graph dir -> Int -> Pattern String dir -> [Pattern Int dir]
matchPattern g@(Graph graph) node (PNode wantedName pats) = do
    let (name, edges) = graph ! node
    guard (name == wantedName)
    -- No backtracking, so we never undo a found match
    matches <- matchPatternAnyMultiple g (map fst edges) pats
    return (PNode node matches)

elideShape :: Graph dir -> Graph dir
elideShape (Graph graph) = Graph (Map.map (\(name, edges) -> (name, filter ((/= "#") . snd) edges)) graph)

compressVars :: Graph 'Fwd -> Graph 'Fwd
compressVars (Graph graph) =
    Graph (Map.fromList [(n, (name, es'))
                        | (n, (name, es)) <- Map.assocs graph
                        , name /= "Avar"
                        , let es' = concatMap (\(j, lab) -> map (fmap (concat . (lab :))) (nexts j)) es])
  where
    nexts :: Int -> [(Int, [String])]
    nexts n = do
        case Map.lookup n graph of
          Nothing -> []
          Just ("Avar", edges) -> do
              (i, lab) <- edges
              (j, labs) <- nexts i
              return (j, lab : labs)
          Just (_, _) -> return (n, [])

mergePairs :: HasCallStack => Graph 'Rev -> Graph 'Rev
mergePairs = while . (fmap assertClosed .) $ \g@(Graph graph) ->
    case [Graph (Map.delete j
                 . Map.adjust ((otheredges ++ jparedges') <$) i
                 $ graph)
         | PNode i [PNode j []] <- findPattern g (PNode "Apair" [PNode "Apair" []])
         , all (== i) (referrentsTo j g)
         , ([(_, label)], otheredges) <- [partition ((== j) . fst) (snd (graph ! i))]
         , let jparedges = snd (graph ! j)
               jparedges' = map (fmap (label ++)) jparedges] of
      graph' : _ -> (True, graph')
      _ -> (False, g)

main :: IO ()
main = do
    (srcfname, dstfname) <- getArgs >>= \case
        [s1, s2] -> return (s1, s2)
        _ -> die "Usage: ./graphdraw.hs <input.graph> <output.dot>\nThe .graph file should be from ACCELERATE_AD_GRAPH=input.graph ."
    source <- readFile srcfname
    graph <- case parse source of
               Right g -> return g
               Left err -> die (show err)
    -- print graph
    let graph' = opposite mergePairs . assertClosed . compressVars . assertClosed . elideShape $ graph
    -- print graph'
    writeFile dstfname (toDot graph')
