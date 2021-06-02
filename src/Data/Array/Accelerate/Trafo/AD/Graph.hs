{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module Data.Array.Accelerate.Trafo.AD.Graph (
  writeGraphToFile,
) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Some

import qualified Data.Array.Accelerate.AST as A
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Error
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.Representation.Array
import qualified Data.Array.Accelerate.Trafo.AD.Acc as AD
import qualified Data.Array.Accelerate.Trafo.AD.ADAcc as AD
import qualified Data.Array.Accelerate.Trafo.AD.Common as AD
import qualified Data.Array.Accelerate.Trafo.AD.Exp as AD


newtype Graph = Graph (Map Int (String, [(Int, String)]))
  deriving (Show)

instance Semigroup Graph where
    Graph a <> Graph b =
        Graph (Map.unionWith (\(s, l) (s', l') ->
                                if s == s' then (s, l <> l')
                                           else (s ++ " | " ++ s', l <> l'))
                             a b)

instance Monoid Graph where
    mempty = Graph mempty

writeGraphToFile :: FilePath -> A.ALeftHandSide args () aenv -> AD.OpenAcc aenv () () args' taenv t -> IO ()
writeGraphToFile fp lhs a =
    let Graph graph = accToGraph lhs a
    in writeFile fp $ unlines $
        ["node \"" ++ show i ++ "\" \"" ++ name ++ "\";"
        | (i, (name, _)) <- Map.assocs graph]
        ++
        ["edge \"" ++ show j ++ "\" -> \"" ++ show i ++ "\" \"" ++ label ++ "\";"
        | (i, (_, edges)) <- Map.assocs graph
        , (j, label) <- edges]

accToGraph :: A.ALeftHandSide args () aenv -> AD.OpenAcc aenv () () args' taenv t -> Graph
accToGraph lhs acc =
    let (_, labeled) = AD.evalIdGen $ AD.enlabelAccToplevel False lhs (AD.argumentTuple (lhsToTupR lhs)) (AD.generaliseArgs acc)
    in go AD.TEmpty labeled
  where
    -- Combine the graph elements for this particular element with the
    -- recursively generated graph for all the arguments.
    go :: AD.TagVal (AD.AAnyPartLabelN Int) aenv -> AD.OpenAcc aenv () Int args taenv t -> Graph
    go env a = graphFor env a <> case a of
        AD.Aconst _ _ -> mempty
        AD.Apair _ e1 e2 -> go env e1 <> go env e2
        AD.Anil _ -> mempty
        AD.Acond _ _ t e -> go env t <> go env e
        AD.Map _ _ e -> go env e
        AD.ZipWith _ _ e1 e2 -> go env e1 <> go env e2
        AD.Fold _ _ _ e -> go env e
        AD.Scan _ _ _ _ e -> go env e
        AD.Scan' _ _ _ _ e -> go env e
        AD.Backpermute _ _ _ e -> go env e
        AD.Permute _ _ def _ e -> go env def <> go env e
        AD.Sum _ e -> go env e
        AD.Generate _ _ _ -> mempty
        AD.Replicate _ _ _ e -> go env e
        AD.Slice _ _ e _ -> go env e
        AD.Reduce _ _ _ e -> go env e
        AD.Reshape _ _ e -> go env e
        AD.Aget _ _ e -> go env e
        AD.Acustom _ _ _ _ _ _ e -> go env e  -- This ignores the function arguments, considering them one unit
        AD.Alet lhs' rhs e -> go env rhs <> go (AD.lpushLHS_parts env (AD.alabelOf rhs) AD.TIHere lhs') e
        AD.Avar _ _ _ -> mempty
        AD.AfreeVar _ _ -> mempty
        AD.Aarg _ _ _ -> mempty

    graphFor :: AD.TagVal (AD.AAnyPartLabelN Int) aenv -> AD.OpenAcc aenv () Int args taenv t -> Graph
    graphFor _ AD.Alet{} = mempty
    graphFor env a =
        let lab = AD.labelLabel (AD.alabelOf a)
            edges = [case dep of
                       DepArg i -> (i, "")
                       DepIdx i -> (i, "!")
                       DepSh i -> (i, "#")
                    | dep <- accAdeps env a]
        in Graph (Map.singleton lab (accGraphNodeName a, edges))

data AccDep a = DepArg a | DepIdx a | DepSh a
  deriving (Functor)

expAdeps :: AD.OpenExp env aenv lab alab args tenv taenv t -> [AccDep (Some (AD.ADLabelN alab))]
expAdeps = expFoldNoCustom $ \case
    AD.Shape _ (AD.ARLab (AD.AnyPartLabel (AD.PartLabel lab _))) -> [DepSh (Some lab)]
    AD.Index _ (AD.ARLab (AD.AnyPartLabel (AD.PartLabel lab _))) _ _ -> [DepIdx (Some lab)]
    _ -> []

funAdeps :: AD.OpenFun env aenv lab alab args tenv taenv t -> [AccDep (Some (AD.ADLabelN alab))]
funAdeps (AD.Lam _ fun) = funAdeps fun
funAdeps (AD.Body ex) = expAdeps ex

accAdeps :: AD.TagVal (AD.AAnyPartLabelN Int) aenv -> AD.OpenAcc aenv lab Int args taenv t -> [AccDep Int]
accAdeps env = \case
    AD.Aconst _ _ -> []
    AD.Apair _ e1 e2 -> [alo e1, alo e2]
    AD.Anil _ -> []
    AD.Acond _ c t e -> expAdeps' c ++ [alo t, alo e]
    AD.Map _ (AD.ELPlain g) e -> funAdeps' g ++ [alo e]
    AD.Map _ _ _ -> error "accAdeps: ELSplit"
    AD.ZipWith _ (AD.ELPlain g) e1 e2 -> funAdeps' g ++ [alo e1, alo e2]
    AD.ZipWith _ _ _ _ -> error "accAdeps: ELSplit"
    AD.Fold _ g me0 e -> funAdeps' g ++ option (expAdeps' <$> me0) ++ [alo e]
    AD.Scan _ _ g me0 e -> funAdeps' g ++ option (expAdeps' <$> me0) ++ [alo e]
    AD.Scan' _ _ g e0 e -> funAdeps' g ++ expAdeps' e0 ++ [alo e]
    AD.Backpermute _ dim g e -> expAdeps' dim ++ funAdeps' g ++ [alo e]
    AD.Permute _ comb def pf e -> funAdeps' comb ++ [alo def] ++ funAdeps' pf ++ [alo e]
    AD.Sum _ e -> [alo e]
    AD.Generate _ e (AD.ELPlain g) -> expAdeps' e ++ funAdeps' g
    AD.Generate _ _ _ -> error "accAdeps: ELSplit"
    AD.Replicate _ _ sle e -> expAdeps' sle ++ [alo e]
    AD.Slice _ _ e sle -> [alo e] ++ expAdeps' sle
    AD.Reduce _ _ g e -> funAdeps' g ++ [alo e]
    AD.Reshape _ sle e -> expAdeps' sle ++ [alo e]
    AD.Aget _ _ e -> [alo e]
    AD.Acustom _ l1 f l2 l3 g e -> afunAdeps env (AD.FLLab l1 AD.FLEnd) f ++ afunAdeps env (AD.FLLab l2 (AD.FLLab l3 AD.FLEnd)) g ++ [alo e]
    AD.Alet _ _ _ -> error "accAdeps: undefined for Alet"
    AD.Avar _ (A.Var _ idx) _
      | AD.AnyPartLabel (AD.PartLabel l _) <- AD.prjT idx env
      -> [DepArg (AD.labelLabel l)]
    AD.AfreeVar _ _ -> []
    AD.Aarg _ _ _ -> []
  where
    expAdeps' :: AD.OpenExp env aenv lab alab args tenv taenv t -> [AccDep alab]
    expAdeps' = map (fmap $ \(Some l) -> AD.labelLabel l) . expAdeps

    funAdeps' :: AD.OpenFun env aenv lab alab args tenv taenv t -> [AccDep alab]
    funAdeps' = map (fmap $ \(Some l) -> AD.labelLabel l) . funAdeps

    alo :: AD.OpenAcc aenv lab alab args taenv t -> AccDep alab
    alo = DepArg . AD.labelLabel . AD.alabelOf

afunAdeps :: AD.TagVal (AD.AAnyPartLabelN Int) aenv -> AD.FunctionLabels AD.NodeLabel ArraysR Int t -> AD.OpenAfun aenv lab Int args taenv t -> [AccDep Int]
afunAdeps env' (AD.FLLab lab labs) (AD.Alam lhs fun) = afunAdeps (AD.lpushLHS_parts env' lab AD.TIHere lhs) labs fun
afunAdeps env' AD.FLEnd (AD.Abody acc) = accAdeps env' acc
afunAdeps _ AD.FLEnd AD.Alam{} = internalError "Too few labels to afunAdeps"
afunAdeps _ AD.FLLab{} AD.Abody{} = internalError "Too many labels to afunAdeps"

-- Fold over all subexpressions, but skip functions contained in an Ecustom.
expFoldNoCustom :: Monoid s
        => (forall env' t'. AD.OpenExp env' aenv lab alab args tenv taenv t' -> s)
        -> AD.OpenExp env aenv lab alab args tenv taenv t
        -> s
expFoldNoCustom f ex = f ex <> case ex of
    AD.Const _ _ -> mempty
    AD.PrimApp _ _ e -> expFoldNoCustom f e
    AD.PrimConst _ _ -> mempty
    AD.Pair _ e1 e2 -> expFoldNoCustom f e1 <> expFoldNoCustom f e2
    AD.Nil _ -> mempty
    AD.Cond _ e1 e2 e3 -> expFoldNoCustom f e1 <> expFoldNoCustom f e2 <> expFoldNoCustom f e3
    AD.Shape _ _ -> mempty
    AD.Index _ _ _ e -> expFoldNoCustom f e
    AD.ShapeSize _ _ e -> expFoldNoCustom f e
    AD.Get _ _ e -> expFoldNoCustom f e
    AD.Undef _ -> mempty
    AD.Ecustom _ _ _ _ _ _ e -> expFoldNoCustom f e
    AD.Let _ rhs e -> expFoldNoCustom f rhs <> expFoldNoCustom f e
    AD.Var _ _ _ -> mempty
    AD.FreeVar _ _ -> mempty
    AD.Arg _ _ _ -> mempty

accGraphNodeName :: AD.OpenAcc aenv lab alab args taenv t -> String
accGraphNodeName = \case
    AD.Aconst{} -> "Aconst"
    AD.Apair{} -> "Apair"
    AD.Anil{} -> "Anil"
    AD.Acond{} -> "Acond"
    AD.Map{} -> "Map"
    AD.ZipWith{} -> "ZipWith"
    AD.Fold{} -> "Fold"
    AD.Scan{} -> "Scan"
    AD.Scan'{} -> "Scan'"
    AD.Backpermute{} -> "Backpermute"
    AD.Permute{} -> "Permute"
    AD.Sum{} -> "Sum"
    AD.Generate{} -> "Generate"
    AD.Replicate{} -> "Replicate"
    AD.Slice{} -> "Slice"
    AD.Reduce{} -> "Reduce"
    AD.Reshape{} -> "Reshape"
    AD.Aget{} -> "Aget"
    AD.Acustom{} -> "Acustom"
    AD.Alet{} -> "Alet"
    AD.Avar{} -> "Avar"
    AD.AfreeVar{} -> "AfreeVar"
    AD.Aarg{} -> "Aarg"

option :: Monoid a => Maybe a -> a
option (Just x) = x
option Nothing = mempty
