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
import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import qualified Data.Array.Accelerate.Trafo.AD.Acc as AD
import qualified Data.Array.Accelerate.Trafo.AD.ADAcc as AD
import qualified Data.Array.Accelerate.Trafo.AD.ADExp as AD
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
    let labeled = AD.evalIdGen $ enlabelAccToplevel' lhs (AD.tupleIndices (lhsToTupR lhs)) (AD.generaliseArgs acc)
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
expAdeps = expFold $ \case
    AD.Shape _ (AD.ARLab (AD.AnyPartLabel (AD.PartLabel lab _))) -> [DepSh (Some lab)]
    AD.Index _ (AD.ARLab (AD.AnyPartLabel (AD.PartLabel lab _))) _ _ -> [DepIdx (Some lab)]
    _ -> []

funAdeps :: AD.OpenFun env aenv lab alab tenv taenv t -> [AccDep (Some (AD.ADLabelN alab))]
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
    AD.Alet _ _ _ -> error "accAdeps: undefined for Alet"
    AD.Avar _ (A.Var _ idx) _
      | AD.AnyPartLabel (AD.PartLabel l _) <- AD.prjT idx env
      -> [DepArg (AD.labelLabel l)]
    AD.AfreeVar _ _ -> []
    AD.Aarg _ _ _ -> []
  where
    expAdeps' :: AD.OpenExp env aenv lab alab args tenv taenv t -> [AccDep alab]
    expAdeps' = map (fmap $ \(Some l) -> AD.labelLabel l) . expAdeps

    funAdeps' :: AD.OpenFun env aenv lab alab tenv taenv t -> [AccDep alab]
    funAdeps' = map (fmap $ \(Some l) -> AD.labelLabel l) . funAdeps

    alo :: AD.OpenAcc aenv lab alab args taenv t -> AccDep alab
    alo = DepArg . AD.labelLabel . AD.alabelOf

expFold :: Monoid s
        => (forall env' t'. AD.OpenExp env' aenv lab alab args tenv taenv t' -> s)
        -> AD.OpenExp env aenv lab alab args tenv taenv t
        -> s
expFold f ex = f ex <> case ex of
    AD.Const _ _ -> mempty
    AD.PrimApp _ _ e -> expFold f e
    AD.PrimConst _ _ -> mempty
    AD.Pair _ e1 e2 -> expFold f e1 <> expFold f e2
    AD.Nil _ -> mempty
    AD.Cond _ e1 e2 e3 -> expFold f e1 <> expFold f e2 <> expFold f e3
    AD.Shape _ _ -> mempty
    AD.Index _ _ _ e -> expFold f e
    AD.ShapeSize _ _ e -> expFold f e
    AD.Get _ _ e -> expFold f e
    AD.Undef _ -> mempty
    AD.Let _ rhs e -> expFold f rhs <> expFold f e
    AD.Var _ _ _ -> mempty
    AD.FreeVar _ _ -> mempty
    AD.Arg _ _ _ -> mempty

accFold :: Monoid s
        => (forall aenv' args' t'. AD.OpenAcc aenv' lab alab args' taenv t' -> s)
        -> (forall env aenv' args' tenv t'. AD.OpenExp env aenv' lab alab args' tenv taenv t' -> s)
        -> (forall env aenv' tenv t'. AD.OpenFun env aenv' lab alab tenv taenv t' -> s)
        -> AD.OpenAcc aenv lab alab args taenv t
        -> s
accFold = \f fe ff e -> f e <> recurse (accFold f fe ff) fe ff e
  where
    recurse :: Monoid s
            => (forall aenv' args' t'. AD.OpenAcc aenv' lab alab args' taenv t' -> s)
            -> (forall env aenv' args' tenv t'. AD.OpenExp env aenv' lab alab args' tenv taenv t' -> s)
            -> (forall env aenv' tenv t'. AD.OpenFun env aenv' lab alab tenv taenv t' -> s)
            -> AD.OpenAcc aenv lab alab args taenv t
            -> s
    recurse _ _  _  (AD.Aconst _ _) = mempty
    recurse f _  _  (AD.Apair _ e1 e2) = f e1 <> f e2
    recurse _ _  _  (AD.Anil _) = mempty
    recurse f fe _  (AD.Acond _ c t e) = fe c <> f t <> f e
    recurse f _  ff (AD.Map _ (AD.ELPlain g) e) = ff g <> f e
    recurse _ _  _  (AD.Map _ _ _) = error "accFold: ELSplit"
    recurse f _  ff (AD.ZipWith _ (AD.ELPlain g) e1 e2) = ff g <> f e1 <> f e2
    recurse _ _  _  (AD.ZipWith _ _ _ _) = error "accFold: ELSplit"
    recurse f fe ff (AD.Fold _ g me0 e) = ff g <> option (fe <$> me0) <> f e
    recurse f fe ff (AD.Scan _ _ g me0 e) = ff g <> option (fe <$> me0) <> f e
    recurse f fe ff (AD.Scan' _ _ g e0 e) = ff g <> fe e0 <> f e
    recurse f fe ff (AD.Backpermute _ dim g e) = fe dim <> ff g <> f e
    recurse f _  ff (AD.Permute _ comb def pf e) = ff comb <> f def <> ff pf <> f e
    recurse f _  _  (AD.Sum _ e) = f e
    recurse _ fe ff (AD.Generate _ e (AD.ELPlain g)) = fe e <> ff g
    recurse _ _  _  (AD.Generate _ _ _) = error "accFold: ELSplit"
    recurse f fe _  (AD.Replicate _ _ sle e) = fe sle <> f e
    recurse f fe _  (AD.Slice _ _ e sle) = f e <> fe sle
    recurse f _  ff (AD.Reduce _ _ g e) = ff g <> f e
    recurse f fe _  (AD.Reshape _ sle e) = fe sle <> f e
    recurse f _  _  (AD.Aget _ _ e) = f e
    recurse f _  _  (AD.Alet _ rhs e) = f rhs <> f e
    recurse _ _  _  (AD.Avar _ _ _) = mempty
    recurse _ _  _  (AD.AfreeVar _ _) = mempty
    recurse _ _  _  (AD.Aarg _ _ _) = mempty

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
    AD.Alet{} -> "Alet"
    AD.Avar{} -> "Avar"
    AD.AfreeVar{} -> "AfreeVar"
    AD.Aarg{} -> "Aarg"

option :: Monoid a => Maybe a -> a
option (Just x) = x
option Nothing = mempty

-- Enlabels a program of the form 'Alet lhs rhs body', where 'rhs' has type
-- 'args' and the Alet has been broken out into its three components. In
-- addition to the full program, returns the label of the enlabeled rhs.
--
-- This does NOT split lambdas! This is the only difference with the similarly
-- named function in ADAcc.hs.
enlabelAccToplevel' :: A.ALeftHandSide args () aenv
                    -> TupR (AD.TupleIdx args) args
                    -> AD.OpenAcc aenv () () args taenv t
                    -> AD.IdGen (AD.OpenAcc () () Int args taenv t)
enlabelAccToplevel' lhs argindices body = do
    BoundArgs aenv buildf <- bindArgs AD.TEmpty lhs (lhsToTupR lhs) argindices
    body' <- enlabelAcc' aenv body
    return (buildf body')
  where
    enlabelAcc' :: AD.TagVal (AD.AAnyPartLabelN Int) aenv -> AD.OpenAcc aenv () () args taenv t -> AD.IdGen (AD.OpenAcc aenv () Int args taenv t)
    enlabelAcc' aenv prog = case prog of
        AD.Aconst lab x -> AD.Aconst <$> genLabNS lab <*> return x
        AD.Apair lab a1 a2 -> AD.Apair <$> genLabN lab <*> enlabelAcc' aenv a1 <*> enlabelAcc' aenv a2
        AD.Anil lab -> AD.Anil <$> genLabN lab
        AD.Acond lab ex a1 a2 -> AD.Acond <$> genLabN lab <*> return (snd (AD.labeliseExpA aenv ex)) <*> enlabelAcc' aenv a1 <*> enlabelAcc' aenv a2
        AD.Map lab (AD.ELPlain fun) a1 -> AD.Map <$> genLabNS lab <*> return (AD.ELPlain (snd (AD.labeliseFunA aenv fun))) <*> enlabelAcc' aenv a1
        AD.ZipWith lab (AD.ELPlain fun) a1 a2 -> AD.ZipWith <$> genLabNS lab <*> return (AD.ELPlain (snd (AD.labeliseFunA aenv fun))) <*> enlabelAcc' aenv a1 <*> enlabelAcc' aenv a2
        AD.Fold lab fun mex a1 -> AD.Fold <$> genLabNS lab <*> return (snd (AD.labeliseFunA aenv fun)) <*> return (snd . AD.labeliseExpA aenv <$> mex) <*> enlabelAcc' aenv a1
        AD.Sum lab a1 -> AD.Sum <$> genLabNS lab <*> enlabelAcc' aenv a1
        AD.Scan lab dir fun mex a1 -> AD.Scan <$> genLabNS lab <*> return dir <*> return (snd (AD.labeliseFunA aenv fun)) <*> return (snd . AD.labeliseExpA aenv <$> mex) <*> enlabelAcc' aenv a1
        AD.Scan' lab dir fun mex a1 -> AD.Scan' <$> genLabN lab <*> return dir <*> return (snd (AD.labeliseFunA aenv fun)) <*> return (snd (AD.labeliseExpA aenv mex)) <*> enlabelAcc' aenv a1
        AD.Generate lab ex (AD.ELPlain fun) -> AD.Generate <$> genLabNS lab <*> return (snd (AD.labeliseExpA aenv ex)) <*> return (AD.ELPlain (snd (AD.labeliseFunA aenv fun)))
        AD.Replicate lab slix ex a1 -> AD.Replicate <$> genLabNS lab <*> return slix <*> return (snd (AD.labeliseExpA aenv ex)) <*> enlabelAcc' aenv a1
        AD.Slice lab slix a1 ex -> AD.Slice <$> genLabNS lab <*> return slix <*> enlabelAcc' aenv a1 <*> return (snd (AD.labeliseExpA aenv ex))
        AD.Reduce lab slix fun a1 -> AD.Reduce <$> genLabNS lab <*> return slix <*> return (snd (AD.labeliseFunA aenv fun)) <*> enlabelAcc' aenv a1
        AD.Reshape lab ex a1 -> AD.Reshape <$> genLabNS lab <*> return (snd (AD.labeliseExpA aenv ex)) <*> enlabelAcc' aenv a1
        AD.Backpermute lab ex fun a1 -> AD.Backpermute <$> genLabNS lab <*> return (snd (AD.labeliseExpA aenv ex)) <*> return (snd (AD.labeliseFunA aenv fun)) <*> enlabelAcc' aenv a1
        AD.Permute lab fun1 a1 fun2 a2 -> AD.Permute <$> genLabNS lab <*> return (snd (AD.labeliseFunA aenv fun1)) <*> enlabelAcc' aenv a1 <*> return (snd (AD.labeliseFunA aenv fun2)) <*> enlabelAcc' aenv a2
        AD.Aget lab tidx a1 -> AD.Aget <$> genLabN lab <*> return tidx <*> enlabelAcc' aenv a1
        AD.Alet lhs' rhs a1 -> do
            rhs' <- enlabelAcc' aenv rhs
            AD.Alet lhs' <$> return rhs' <*> enlabelAcc' (AD.lpushLHS_parts aenv (AD.alabelOf rhs') AD.TIHere lhs') a1
        AD.Avar lab var@(A.Var _ idx) _
          | AD.AnyPartLabel pl <- AD.prjT idx aenv ->
              AD.Avar <$> genLabNS lab <*> return var <*> return pl
        AD.AfreeVar lab var -> AD.AfreeVar <$> genLabNS lab <*> return var
        AD.Aarg lab argsty tidx -> AD.Aarg <$> genLabNS lab <*> return argsty <*> return tidx
        AD.Map _ AD.ELSplit{} _ -> error "Unexpected split Map in enlabelAcc'"
        AD.ZipWith _ AD.ELSplit{} _ _ -> error "Unexpected split ZipWith in enlabelAcc'"
        AD.Generate _ _ AD.ELSplit{} -> error "Unexpected split Generate in enlabelAcc'"
      where
        genLabN :: AD.ADLabelN () t -> AD.IdGen (AD.ADLabelN Int t)
        genLabN = AD.genId' . AD.labelType

        genLabNS :: AD.ADLabelNS () t -> AD.IdGen (AD.ADLabelNS Int t)
        genLabNS = AD.genId' . AD.labelType

data BoundArgs aenv aenv2 args taenv =
    BoundArgs (AD.TagVal (AD.AAnyPartLabelN Int) aenv2)
              (forall t. AD.OpenAcc aenv2 () Int args taenv t
                      -> AD.OpenAcc aenv () Int args taenv t)

bindArgs :: AD.TagVal (AD.AAnyPartLabelN Int) aenv
         -> A.ALeftHandSide args aenv aenv2
         -> ArraysR bigargs
         -> TupR (AD.TupleIdx bigargs) args
         -> AD.IdGen (BoundArgs aenv aenv2 bigargs taenv)
bindArgs aenv (LeftHandSideWildcard _) _ _ =
    return (BoundArgs aenv id)
bindArgs aenv (LeftHandSideSingle ty@ArrayR{}) argsty (TupRsingle ti) = do
    lab' <- AD.genId' ty
    return $ BoundArgs (AD.TPush aenv (AD.AnyPartLabel (AD.PartLabel (AD.tupleLabel lab') AD.TIHere)))
                       (AD.Alet (LeftHandSideSingle ty) (AD.Aarg lab' argsty ti))
bindArgs _ _ _ (TupRsingle _) = error "bindArgs: non-argument in argument tuple"
bindArgs aenv (LeftHandSidePair lhs1 lhs2) argsty (TupRpair args1 args2) = do
    BoundArgs aenv1 f1 <- bindArgs aenv lhs1 argsty args1
    BoundArgs aenv2 f2 <- bindArgs aenv1 lhs2 argsty args2
    return (BoundArgs aenv2 (f1 . f2))
