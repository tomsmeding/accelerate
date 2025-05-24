{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}


------------ TODO REMOVE ------------
{-# OPTIONS -Wno-unused-imports #-}
module Data.Array.Accelerate.Trafo.AD where

import Data.Array.Accelerate.AD.Types
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Type
import Data.Primitive.Vec (Vec)

import Control.Monad.Identity
import Control.Monad.State
import Data.Functor.Const hiding (Const(..))
import Data.Functor.Const (Const, getConst)
import qualified Data.Functor.Const as Fun
import Data.Functor.Product hiding (Pair)
import qualified Data.Functor.Product as Fun
import Data.Type.Equality
import Data.Proxy
import GHC.TypeLits (KnownNat)


convertAcc :: OpenAcc aenv a -> OpenAcc aenv a
convertAcc = runIdentity . travPreOpenAcc (\f (OpenAcc acc) -> process <$> f acc)
  where
    process :: PreOpenAcc OpenAcc aenv a -> OpenAcc aenv a
    process (Avjp t1 t2 a b c) = transform t1 t2 a b c
    process acc = OpenAcc acc

convertAfun :: OpenAfun aenv a -> OpenAfun aenv a
convertAfun (Alam lhs a) = Alam lhs (convertAfun a)
convertAfun (Abody a) = Abody (convertAcc a)

transform
  :: ArraysR arrs1 -> ArraysR arrs2
  -> OpenAfun aenv (arrs1 -> arrs2)
  -> OpenAcc aenv arrs1
  -> OpenAcc aenv (Ctg arrs2)
  -> OpenAcc aenv (Ctg arrs1)
transform = error "transform"

data LetStack s aenv aenv' where
  LSLet :: LLHS (Const (Maybe Int)) s t aenv aenv1 -> OpenAcc aenv t -> LetStack s aenv1 aenv' -> LetStack s aenv aenv'
  LSCore :: LetStack s aenv aenv
  -- the '$' is mnemonic for "stack"
  (:++$) :: LetStack s aenv aenv' -> LetStack s aenv' aenv'' -> LetStack s aenv aenv''
  -- LSWeak :: aenv :> aenv2 -> LetStack s aenv aenv'
infixr 1 :++$

type ALetStack = LetStack ArrayR

weakenLetStack :: aenv :> aenv2 -> LetStack s aenv aenv'
               -> (forall aenv2'. LetStack s aenv2 aenv2' -> aenv' :> aenv2' -> r) -> r
weakenLetStack w (LSLet lhs rhs st) k =
  rebuildLLHS lhs $ \lhs' _ ->
  let rhs' = weaken w rhs in
  weakenLetStack (sinkWithLLHS lhs lhs' w) st $ \st' w' ->
    k (LSLet lhs' rhs' st') w'
weakenLetStack w LSCore k = k LSCore w
weakenLetStack w (st1 :++$ st2) k =
  weakenLetStack w st1 $ \st1' w1 ->
  weakenLetStack w1 st2 $ \st2' w2 ->
    k (st1' :++$ st2') w2

weakenWithLetStack :: LetStack s aenv aenv' -> aenv :> aenv'
weakenWithLetStack (LSLet lhs _ s) = weakenWithLetStack s .> weakenWithLLHS lhs
weakenWithLetStack LSCore = weakenId
weakenWithLetStack (s1 :++$ s2) = weakenWithLetStack s2 .> weakenWithLetStack s1

lsOnlyUnlabeled :: LetStack s aenv aenv' -> Bool
lsOnlyUnlabeled (LSLet lhs _ st) =
  case llhsLabels' lhs of
    [] -> lsOnlyUnlabeled st
    _ -> False
lsOnlyUnlabeled LSCore = True
lsOnlyUnlabeled (st1 :++$ st2) = lsOnlyUnlabeled st1 && lsOnlyUnlabeled st2

letBinds :: (forall t. s t -> ArrayR t) -> LetStack s aenv aenv' -> OpenAcc aenv' a -> OpenAcc aenv a
letBinds down (LSLet lhs rhs st) = aletL (mapLLHS id down lhs) rhs . letBinds down st
letBinds _    LSCore = id
letBinds down (s1 :++$ s2) = letBinds down s1 . letBinds down s2

letBindsExport :: ALetStack aenv aenv' -> OpenAcc aenv' a
               -> (forall tup. TupR ALabel tup -> OpenAcc aenv (a, tup) -> r)
               -> r
letBindsExport st core k =
  letBindsExport' st $ \labs build ->
    k labs (build $ \tup -> pairOA core (avarsIn OpenAcc tup))

letBindsExport' :: ALetStack aenv aenv'
                -> (forall tup. TupR ALabel tup -> (forall b. (ArrayVars aenv' tup -> OpenAcc aenv' b) -> OpenAcc aenv b) -> r)
                -> r
letBindsExport' (LSLet lhs rhs st) k =
  compressLLHS (\(Fun.Const l) t -> (`Label` t) <$> l) lhs $ \labs vars ->
  letBindsExport' st $ \labs2 build ->
    case labs of
      TupRunit ->
        k labs2 (aletL lhs rhs . build)
      _ ->
        k (TupRpair labs labs2)
          (\mk -> aletL lhs rhs $
                  build $ \tup ->
                    mk $ TupRpair (weakenVars (weakenWithLetStack st) vars)
                                  tup)
letBindsExport' LSCore k = k TupRunit (\mk -> mk TupRunit)
letBindsExport' (s1 :++$ s2) k =
  letBindsExport' s1 $ \labs1 build1 ->
  letBindsExport' s2 $ \labs2 build2 ->
    k (TupRpair labs1 labs2)
      (\mk -> build1 $ \tup1 ->
              build2 $ \tup2 ->
                mk (TupRpair (weakenVars (weakenWithLetStack s2) tup1)
                             tup2))

buildPrimal
  :: LabAcc aenv a
  -> (forall aenv'. ALetStack aenv aenv' -> OpenAcc aenv' a -> r) -> r
buildPrimal (LabAcc Nothing acc) k = buildPrimalPre acc k
buildPrimal (LabAcc (Just labs) acc) k =
  buildPrimalPre acc $ \s1 acc' ->
  declareVarsL labs $ \lhs _ vars ->
    k (s1 :++$ LSLet (mapLLHS (\(Fun.Const l) -> Fun.Const (Just l)) id lhs) acc' LSCore)
      (avarsIn OpenAcc (vars weakenId))

buildPrimalPre
  :: PreOpenAcc LabAcc aenv a
  -> (forall aenv'. ALetStack aenv aenv' -> OpenAcc aenv' a -> r) -> r
buildPrimalPre topacc k = case topacc of
  Alet lhs rhs body ->
    buildPrimal rhs $ \s1 rhs' ->
    rebuildLHSCPS lhs $ \lhs' _ ->
    let wForS2 = sinkWithLHS lhs lhs' (weakenWithLetStack s1) in
    buildPrimal body $ \s2 body' ->
      -- If the body has no primal stores, we can bind the RHS results in a
      -- small-scope let. Otherwise, we bind the RHS in the let stack.
      -- TODO: we could apply the same treatment to s1.
      if lsOnlyUnlabeled s2
        then k s1 (alet lhs' rhs' (weaken wForS2 (letBinds id s2 body')))
        else weakenLetStack wForS2 s2 $ \s2' ws2 ->
               k (s1 :++$ LSLet (toLLHS' (Fun.Const Nothing) lhs') rhs' s2')
                 (weaken ws2 body')

  Avar var ->
    k LSCore (OpenAcc (Avar var))

  Apair a b ->
    buildPrimal2 a b $ \s a' b' ->
      k s (pairOA a' b')

  Anil ->
    k LSCore (OpenAcc Anil)

  Atrace msg a b ->
    buildPrimal2 a b $ \s a' b' ->
      k s (OpenAcc (Atrace msg a' b'))

  Apply repr (Alam lhs (Abody body)) rhs ->
    buildPrimal rhs $ \s1 rhs' ->
    rebuildLHSCPS lhs $ \lhs' _ ->
    buildPrimal body $ \s2 body' ->
    weakenLetStack (sinkWithLHS lhs lhs' (weakenWithLetStack s1)) s2 $ \s2' ws2 ->
    letBindsExport s2' (weaken ws2 body') $ \exportLabs body2 ->
    let exportTy = mapTupR labelTy exportLabs in
    let labsFull = TupRpair (mapTupR (Label Nothing) repr)
                            (mapTupR (\(Label l t) -> Label (Just l) t) exportLabs) in
    declareVarsL labsFull $ \lhsFull _ varsFull ->
      k (s1 :++$ LSLet lhsFull (OpenAcc (Apply (TupRpair repr exportTy) (Alam lhs' (Abody body2)) rhs')) LSCore)
        (avarsIn OpenAcc (fst (splitTupRpair (varsFull weakenId))))

  Aforeign{} ->
    internalError "foreign calls not supported in AD"

  -- Acond p a1 a2 ->
  --   Acond p <$> rec a1 <*> rec a2

  _ -> _

buildPrimal2
  :: LabAcc aenv a
  -> LabAcc aenv b
  -> (forall aenv'. ALetStack aenv aenv' -> OpenAcc aenv' a -> OpenAcc aenv' b -> r) -> r
buildPrimal2 a b k =
  buildPrimal a $ \s1 a' ->
  buildPrimal b $ \s2 b' ->
  weakenLetStack (weakenWithLetStack s1) s2 $ \s2' ws2 ->
    k (s1 :++$ s2')
      (weaken (weakenWithLetStack s2') a')
      (weaken ws2 b')

splitPairAcc
  :: OpenAcc aenv (a, b)
  -> (forall aenv'. ALetStack aenv aenv' -> OpenAcc aenv' a -> OpenAcc aenv' b -> r) -> r
splitPairAcc (OpenAcc (Apair a b)) k = k LSCore a b
splitPairAcc acc k =
  let (tA, tB) = splitTupRpair (arraysR acc) in
  declareVarsCPS (TupRpair tA tB) $ \lhs _ mkvars ->
  let (vars1, vars2) = splitTupRpair (mkvars weakenId) in
    k (LSLet (toLLHS' (Fun.Const Nothing) lhs) acc LSCore)
      (avarsIn OpenAcc vars1) (avarsIn OpenAcc vars2)

letIfNecessary :: OpenAcc aenv a -> (forall aenv'. ALetStack aenv aenv' -> ArrayVars aenv' a -> r) -> r
letIfNecessary acc k = case extractAccVars acc of
  Just vars -> k LSCore vars
  Nothing ->
    declareVarsCPS (arraysR acc) $ \lhs _ vars ->
      k (LSLet (toLLHS' (Fun.Const Nothing) lhs) acc LSCore) (vars weakenId)

alet :: ALeftHandSide a aenv aenv' -> OpenAcc aenv a -> OpenAcc aenv' b -> OpenAcc aenv b
alet lhs rhs body = case extractAccVars rhs of
  Just vars -> weaken (substituteLHS lhs vars) body
  Nothing -> OpenAcc (Alet lhs rhs body)

aletL :: LLHS l ArrayR a aenv aenv' -> OpenAcc aenv a -> OpenAcc aenv' b -> OpenAcc aenv b
aletL = alet . fromLLHS

pairOA :: OpenAcc aenv a -> OpenAcc aenv b -> OpenAcc aenv (a, b)
pairOA a b = OpenAcc (Apair a b)

data Label l s t = Label
  { labelLab :: l
  , labelTy :: s t }
type ALabel = Label Int ArrayR
type AMLabel = Label (Maybe Int) ArrayR

data LabAcc aenv a = LabAcc (Maybe (TupR ALabel a)) (PreOpenAcc LabAcc aenv a)

instance HasArraysR LabAcc where
  arraysR (LabAcc _ acc) = arraysR acc

labelsOf :: LabAcc aenv a -> Maybe (TupR ALabel a)
labelsOf (LabAcc mlabs _) = mlabs

labelAcc :: OpenAcc aenv a -> LabAcc aenv a
labelAcc = flip evalState 0 . travPreOpenAcc (\f (OpenAcc acc) -> process =<< f acc)
  where
    process :: PreOpenAcc LabAcc aenv a -> State Int (LabAcc aenv a)
    process acc = do
      labs <- traverseTupR (\ty -> state (\i -> (Label i ty, i+1))) (arraysR acc)
      pure (LabAcc (Just labs) acc)

travPreOpenAcc
  :: forall f g m aenv a.
     Applicative m
  => (forall aenv' a'. (PreOpenAcc f aenv' a' -> m (PreOpenAcc g aenv' a')) -> f aenv' a' -> m (g aenv' a'))
  -> f aenv a -> m (g aenv a)
travPreOpenAcc transf = transf $ \case
  Alet lhs bnd body        -> Alet lhs <$> rec bnd <*> rec body
  Avar var                 -> pure $ Avar var
  Apair as bs              -> Apair <$> rec as <*> rec bs
  Anil                     -> pure Anil
  Atrace msg as bs         -> Atrace msg <$> rec as <*> rec bs
  Apply repr afun acc      -> Apply repr <$> recAfun afun <*> rec acc
  Aforeign repr asm afun a -> Aforeign repr asm <$> recAfun afun <*> rec a
  Acond p a1 a2            -> Acond p <$> rec a1 <*> rec a2
  Awhile p f a             -> Awhile <$> recAfun p <*> recAfun f <*> rec a
  Use repr arr             -> pure $ Use repr arr
  Unit tp x                -> pure $ Unit tp x
  Reshape shr sh a         -> Reshape shr sh <$> rec a
  Generate repr sh f       -> pure $ Generate repr sh f
  Transform repr sh p f a  -> Transform repr sh p f <$> rec a
  Replicate slice sh a     -> Replicate slice sh <$> rec a
  Slice slice a sh         -> Slice slice <$> rec a <*> pure sh
  Map tp f a               -> Map tp f <$> rec a
  ZipWith tp f a1 a2       -> ZipWith tp f <$> rec a1 <*> rec a2
  Fold f z a               -> Fold f z <$> rec a
  FoldSeg i f z a s        -> FoldSeg i f z <$> rec a <*> rec s
  Scan d f z a             -> Scan d f z <$> rec a
  Scan' d f z a            -> Scan' d f z <$> rec a
  Permute f d a            -> Permute f <$> rec d <*> rec a
  Backpermute shr sh f a   -> Backpermute shr sh f <$> rec a
  Stencil sr tp f b a      -> Stencil sr tp f b <$> rec a
  Stencil2 sr1 sr2 tp f b1 a1 b2 a2 -> Stencil2 sr1 sr2 tp f b1 <$> rec a1 <*> pure b2 <*> rec a2
  Avjp t1 t2 a b c         -> Avjp t1 t2 <$> recAfun a <*> rec b <*> rec c
  where
    rec :: f aenv' a' -> m (g aenv' a')
    rec = travPreOpenAcc transf

    recAfun :: PreOpenAfun f aenv' a' -> m (PreOpenAfun g aenv' a')
    recAfun (Alam lhs fun) = Alam lhs <$> recAfun fun
    recAfun (Abody acc) = Abody <$> rec acc

-- env' is a subset of env; the data type describes which entries are kept. The
-- @f@ values optionally allow subsetting of the entries too.
data Subenv' f env env' where
  SEYes :: Subenv' f env env' -> f t t' -> Subenv' f (env, t) (env', t')
  SENo :: Subenv' f env env' -> Subenv' f (env, t) env'
  SENone :: Subenv' f env ()

-- t' contains only some of the values from t
data Sparse t t' where
  SPYes :: Sparse t t
  SPNo :: Sparse t ()
  SPPair :: Sparse t1 t1' -> Sparse t2 t2' -> Sparse (t1, t2) (t1', t2')

type Subenv = Subenv' (:~:)  -- normal sub-environment
type SSubenv = Subenv' Sparse  -- sparse sub-environment

subenvPopLHS
  :: IsArrayInstr arr => SSubenv (Ctg env') denv -> ELeftHandSide t env env'
  -> (forall denv' t'. SSubenv (Ctg env) denv'
                    -> Sparse (Ctg t) t'
                    -> (forall e. PreOpenExp arr e denv -> PreOpenExp arr e (denv', t'))
                    -> r)
  -> r
subenvPopLHS (SEYes sub SPYes) LeftHandSideSingle{} k = k sub SPYes id
subenvPopLHS (SEYes sub SPNo) LeftHandSideSingle{} k = k sub SPNo id
subenvPopLHS (SEYes _   SPPair{}) LeftHandSideSingle{} _ = error "impossible"
subenvPopLHS (SENo sub) LeftHandSideSingle{} k = k sub SPNo (`Pair` Nil)
subenvPopLHS SENone LeftHandSideSingle{} k = k SENone SPNo (\_ -> Pair Nil Nil)
subenvPopLHS sub LeftHandSideWildcard{} k = k sub SPNo (`Pair` Nil)
subenvPopLHS sub (LeftHandSidePair lhs1 lhs2) k =
  subenvPopLHS sub lhs2 $ \sub2 sp2 split2 ->
  subenvPopLHS sub2 lhs1 $ \sub1 sp1 split1 ->
    k sub1 (SPPair sp1 sp2)
      (\e -> splitLet (split2 e) $ \_ wrap2 eD1 e2 ->
             wrap2 $
             splitLet (split1 eD1) $ \w wrap1 eD e1 ->
             wrap1 $
               Pair eD (Pair e1 (weakenE w e2)))

subenvPlus
  :: IsArrayInstr arr
  => TupR SCtgE env
  -> (forall t t1 t2 e.
          TupR SCtgE t
       -> f t t1 -> PreOpenExp arr e t1
       -> f t t2 -> PreOpenExp arr e t2
       -> (forall t3. f t t3 -> PreOpenExp arr e t3 -> r)
       -> r)
  -> Subenv' f env env1 -> PreOpenExp arr env' env1
  -> Subenv' f env env2 -> PreOpenExp arr env' env2
  -> (forall env3. Subenv' f env env3 -> PreOpenExp arr env' env3 -> r) -> r
subenvPlus ctgty f (SEYes sub1 x) e1 (SEYes sub2 y) e2 k =
  let (ctgty1, ctgty2) = splitTupRpair ctgty in
  splitLet e1 $ \w1 wrap1 e1E e1T ->
  splitLet (weakenE w1 e2) $ \w2 wrap2 e2E e2T ->
  subenvPlus ctgty1 f sub1 (weakenE w2 e1E) sub2 e2E $ \sub3 e3E ->
  f ctgty2 x (weakenE w2 e1T) y e2T $ \z e3T ->
  k (SEYes sub3 z) (wrap1 $ wrap2 $ Pair e3E e3T)
subenvPlus ctgty f (SEYes sub1 x) e1 (SENo sub2) e2 k =
  splitLet e1 $ \w1 wrap1 e1E e1T ->
  subenvPlus (fst (splitTupRpair ctgty)) f sub1 e1E sub2 (weakenE w1 e2) $ \sub3 e3 ->
    k (SEYes sub3 x) (wrap1 $ Pair e3 e1T)
subenvPlus ctgty f (SENo sub1) e1 (SEYes sub2 y) e2 k =
  splitLet e2 $ \w2 wrap2 e2E e2T ->
  subenvPlus (fst (splitTupRpair ctgty)) f sub1 (weakenE w2 e1) sub2 e2E $ \sub3 e3 ->
    k (SEYes sub3 y) (wrap2 $ Pair e3 e2T)
subenvPlus ctgty f (SENo sub1) e1 (SENo sub2) e2 k =
  subenvPlus (fst (splitTupRpair ctgty)) f sub1 e1 sub2 e2 $ \sub3 e3 ->
    k (SENo sub3) e3
subenvPlus _ _ SENone _ sub2 e2 k = k sub2 e2
subenvPlus _ _ sub1 e1 SENone _ k = k sub1 e1

sparsePlus
  :: IsArrayInstr arr
  => TupR SCtgE t
  -> Sparse t t1 -> PreOpenExp arr env t1
  -> Sparse t t2 -> PreOpenExp arr env t2
  -> (forall t3. Sparse t t3 -> PreOpenExp arr env t3 -> r)
  -> r
sparsePlus ctgty (SPPair s11 s12) e1 (SPPair s21 s22) e2 k =
  let (ctgty1, ctgty2) = splitTupRpair ctgty in
  splitLet e1 $ \w1 wrap1 e11 e12 ->
  splitLet (weakenE w1 e2) $ \w2 wrap2 e21 e22 ->
  sparsePlus ctgty1 s11 (weakenE w2 e11) s21 e21 $ \s31 e31 ->
  sparsePlus ctgty2 s12 (weakenE w2 e12) s22 e22 $ \s32 e32 ->
    k (SPPair s31 s32) (wrap1 $ wrap2 $ Pair e31 e32)
sparsePlus ctgty SPYes e1 (SPPair s21 s22) e2 k = sparsePlus ctgty (SPPair SPYes SPYes) e1 (SPPair s21 s22) e2 k
sparsePlus ctgty (SPPair s11 s12) e1 SPYes e2 k = sparsePlus ctgty (SPPair s11 s12) e1 (SPPair SPYes SPYes) e2 k

sparsePlus ctgty SPYes e1 SPYes e2 k = k SPYes (densePlus ctgty e1 e2)
sparsePlus _     SPNo _ SPNo _ k = k SPNo Nil
sparsePlus _     s1 e1 SPNo _ k = k s1 e1
sparsePlus _     SPNo _ s2 e2 k = k s2 e2

densePlus :: IsArrayInstr arr => TupR SCtgE t -> PreOpenExp arr env t -> PreOpenExp arr env t -> PreOpenExp arr env t
densePlus TupRunit _ _ = Nil
densePlus (TupRsingle (SCEFloat t)) e1 e2 = PrimApp (PrimAdd (FloatingNumType t)) (Pair e1 e2)
densePlus (TupRsingle (SCEVector _ _)) _ _ = error "AD: vectors not yet supported"
densePlus (TupRpair a b) e1 e2 =
  splitLet e1 $ \w1 wrap1 e1a e1b ->
  splitLet (weakenE w1 e2) $ \w2 wrap2 e2a e2b ->
  wrap1 $ wrap2 $
    Pair (densePlus a (weakenE w2 e1a) e2a) (densePlus b (weakenE w2 e1b) e2b)

onehotSubenv
  :: Idx env a
  -> (forall denv. SSubenv (Ctg env) denv -> (PreOpenExp arr env' (Ctg a) -> PreOpenExp arr env' denv) -> r)
  -> r
onehotSubenv ZeroIdx k = k (SEYes SENone SPYes) (Nil `Pair`)
onehotSubenv (SuccIdx idx) k = onehotSubenv idx $ \sub f -> k (SENo sub) f

chadExp
  :: IsArrayInstr arr
  => TypeR env
  -> PreOpenExp arr env a
  -> (forall tape.
          PreOpenExp arr env (a, tape)  -- primal
       -> (forall env' sctg r'.
               ExpVars env' tape  -- reconstruction of the tape
            -> Sparse (Ctg a) sctg  -- incoming cotangent structure
            -> PreOpenExp arr env' sctg  -- incoming cotangent
            -> (forall denv.
                    SSubenv (Ctg env) denv  -- outgoing environment cotangent structure
                 -> PreOpenExp arr env' denv  -- outgoing environment cotangent
                 -> r')
            -> r')
       -> r)
  -> r
chadExp envtyp topexp k = case topexp of
  Let lhs rhs body ->
    chadExp envtyp rhs $ \rhs1 rhsk2 ->
    chadExp (extendLHSenvType envtyp lhs) body $ \body1 bodyk2 ->
    let primal =
          splitLet rhs1 $ \wwrap1 wrap1 rhs1p rhs1t ->
          wrap1 $
          rebuildLHSCPS lhs $ \lhs' wlhs' ->
          Let lhs' rhs1p $
          splitLet (weakenE (sinkWithLHS lhs lhs' wwrap1) body1) $ \wwrap2 wrap2 body1p body1t ->
          wrap2 $
            Pair body1p
                 (Pair (weakenE (wwrap2 .> wlhs') rhs1t) body1t)
    in
    k primal $ \tapevars bodyctgsparsity bodyctg k' ->
    let (tapevars1, tapevars2) = splitTupRpair tapevars in
    bodyk2 tapevars2 bodyctgsparsity bodyctg $ \bodyretse bodyenvctg ->
    subenvPopLHS bodyretse lhs $ \bodyupse rhsctgsparsity split ->
    splitLet (split bodyenvctg) $ \w wrap envctg1 rhsctg ->
    rhsk2 (weakenVars w tapevars1) rhsctgsparsity rhsctg $ \rhsupse rhsenvctg ->
    subenvPlus (ctgTypeE envtyp) sparsePlus bodyupse envctg1 rhsupse rhsenvctg $ \upse envctg ->
    k' upse (wrap envctg)

  Evar var ->
    k (Pair (Evar var) Nil) $ \_ sparsity ctg k' ->
    case sparsity of
      SPYes -> onehotSubenv (varIdx var) $ \sub f -> k' sub (f ctg)
      SPNo -> k' SENone Nil
      SPPair _ _ -> error "impossible"

  Foreign{} ->
    internalError "foreign calls not supported in AD"

  Pair eA eB ->
    chadExp envtyp eA $ \eA1 eAk2 ->
    chadExp envtyp eB $ \eB1 eBk2 ->
    let primal =
          splitLet eA1 $ \wwrap1 wrap1 eA1p eA1t ->
          splitLet (weakenE wwrap1 eB1) $ \wwrap2 wrap2 eB1p eB1t ->
          wrap1 $ wrap2 $
            Pair (Pair (weakenE wwrap2 eA1p) eB1p)
                 (Pair (weakenE wwrap2 eA1t) eB1t)
    in
    k primal $ \tapevars (ctgsparsity :: Sparse (a, b) c) ctg k' ->
    let ctgsparsity' :: Sparse (a, b) c
        ctgsparsity' = case ctgsparsity of
                         SPNo -> SPNo
                         SPPair s1 s2 -> SPPair s1 s2
                         SPYes -> SPPair SPYes SPYes
    in
    case ctgsparsity' of
      SPNo -> k' SENone Nil
      SPPair sparsity1 sparsity2 ->
        splitLet ctg $ \w wrap ctg1 ctg2 ->
        eAk2 (weakenVars w (fst (splitTupRpair tapevars))) sparsity1 ctg1 $ \se1 envctg1 ->
        eBk2 (weakenVars w (snd (splitTupRpair tapevars))) sparsity2 ctg2 $ \se2 envctg2 ->
        subenvPlus (ctgTypeE envtyp) sparsePlus se1 envctg1 se2 envctg2 $ \upse envctg ->
          k' upse (wrap envctg)
      SPYes -> error "impossible"

  Nil -> k (Pair Nil Nil) (\_ _ _ k' -> k' SENone Nil)

  _ -> _

splitLet
  :: IsArrayInstr arr
  => PreOpenExp arr env (a, b)
  -> (forall env'. env :> env'
                -> (forall c. PreOpenExp arr env' c -> PreOpenExp arr env c)
                -> PreOpenExp arr env' a
                -> PreOpenExp arr env' b
                -> r)
  -> r
splitLet (Pair e1 e2) k = k weakenId id e1 e2
splitLet e k =
  declareVarsCPS (expType e) $ \lhs w vars ->
  let (vars1, vars2) = splitTupRpair (vars weakenId) in
    k w (Let lhs e) (returnExpVars vars1) (returnExpVars vars2)

-- travPreOpenExp
--   :: forall m arr env a.
--      Applicative m
--   => (forall arr' env' a'.
--             (PreOpenExp arr' env' a' -> m (PreOpenExp arr' env' a'))
--          -> (forall b1 b2. arr' (b1 -> b2) -> PreOpenExp arr' env' b1 -> m (PreOpenExp arr' env' b2))
--          -> PreOpenExp arr' env' a' -> m (PreOpenExp arr' env' a'))
--   -> (forall env' a' b'. arr (a' -> b') -> PreOpenExp arr env' a' -> m (PreOpenExp arr env' b'))
--   -> PreOpenExp arr env a -> m (PreOpenExp arr env a)
-- travPreOpenExp transf transAI = transf trav transAI
--   where
--     trav = \case
--       Let lhs bnd body  -> Let lhs <$> rec bnd <*> rec body
--       Evar var -> pure $ Evar var
--       Foreign repr asm fun a -> Foreign repr asm <$> recFunNAI fun <*> rec a

--     rec :: PreOpenExp arr env' a' -> m (PreOpenExp arr env' a')
--     rec = travPreOpenExp transf transAI

--     recFun :: PreOpenFun arr env' a' -> m (PreOpenFun arr env' a')
--     recFun (Lam lhs fun) = Lam lhs <$> recFun fun
--     recFun (Body acc) = Body <$> travPreOpenExp transf transAI acc

--     recFunNAI :: PreOpenFun NoArrayInstr env' a' -> m (PreOpenFun NoArrayInstr env' a')
--     recFunNAI (Lam lhs fun) = Lam lhs <$> recFunNAI fun
--     recFunNAI (Body acc) = Body <$> travPreOpenExp transf (\case {}) acc

-- recursePreOpenAcc
--   :: forall f g m aenv aenv' a.
--      (Applicative m, HasArraysR f)
--   => aenv :> aenv'
--   -> (forall args a'. PreOpenAfun' f aenv args a' -> m (PreOpenAfun' g aenv' args a'))
--   -> PreOpenAcc f aenv a -> m (PreOpenAcc g aenv' a)
-- recursePreOpenAcc w transf = \case
--   Alet lhs bnd body        -> liftA2 (\bnd' (Alam' lhs' (Abody' body')) -> Alet lhs' bnd' body')
--                                      (transf0 bnd)
--                                      (transf (Alam' lhs (Abody' body)))
--   Avar var                 -> pure $ Avar (weaken w var)
--   Apair as bs              -> Apair <$> transf0 as <*> transf0 bs
--   Anil                     -> pure Anil
--   Atrace msg as bs         -> Atrace msg <$> transf0 as <*> transf0 bs
--   Apply repr afun acc      -> Apply repr <$> recAfun afun <*> transf0 acc
--   Aforeign repr asm afun a -> Aforeign repr asm <$> recAfun afun <*> transf0 a
--   Acond p a1 a2            -> Acond p <$> transf0 a1 <*> transf0 a2
--   Awhile p f a             -> Awhile <$> recAfun p <*> recAfun f <*> transf0 a
--   Use repr arr             -> pure $ Use repr arr
--   Unit tp x                -> pure $ Unit tp x
--   Reshape shr sh a         -> Reshape shr sh <$> transf0 a
--   Generate repr sh f       -> pure $ Generate repr sh f
--   Transform repr sh p f a  -> Transform repr sh p f <$> transf0 a
--   Replicate slice sh a     -> Replicate slice sh <$> transf0 a
--   Slice slice a sh         -> Slice slice <$> transf0 a <*> pure sh
--   Map tp f a               -> Map tp f <$> transf0 a
--   ZipWith tp f a1 a2       -> ZipWith tp f <$> transf0 a1 <*> transf0 a2
--   Fold f z a               -> Fold f z <$> transf0 a
--   FoldSeg i f z a s        -> FoldSeg i f z <$> transf0 a <*> transf0 s
--   Scan d f z a             -> Scan d f z <$> transf0 a
--   Scan' d f z a            -> Scan' d f z <$> transf0 a
--   Permute f d a            -> Permute f <$> transf0 d <*> transf0 a
--   Backpermute shr sh f a   -> Backpermute shr sh f <$> transf0 a
--   Stencil sr tp f b a      -> Stencil sr tp f b <$> transf0 a
--   Stencil2 sr1 sr2 tp f b1 a1 b2 a2 -> Stencil2 sr1 sr2 tp f b1 <$> transf0 a1 <*> pure b2 <*> transf0 a2
--   Avjp t1 t2 a b c         -> Avjp t1 t2 <$> recAfun a <*> transf0 b <*> transf0 c
--   where
--     transf0 :: HasArraysR f => f aenv a' -> m (g aenv' a')
--     transf0 acc = (\(Abody' acc') -> acc') <$> transf (Abody' acc)

-- data PreOpenAfun' acc aenv args t where
--   Abody' :: acc aenv t -> PreOpenAfun' acc aenv '[] t
--   Alam' :: ALeftHandSide s aenv aenv' -> PreOpenAfun' acc aenv' args t -> PreOpenAfun' acc aenv (s ': args) t

data SCtgA t where
  SCAArray :: ShapeR sh -> SCtgE t -> SCtgA (Array sh t)
  SCANil :: SCtgA ()
  SCAPair :: SCtgA a -> SCtgA b -> SCtgA (a, b)

data SCtgE t where
  SCEFloat :: FloatingType t -> SCtgE t
  SCEVector :: KnownNat n => Int -> FloatingType t -> SCtgE (Vec n t)

instance Distributes SCtgE where
  reprIsSingle (SCEFloat t) = reprIsSingle (SingleScalarType (NumSingleType (FloatingNumType t)))
  reprIsSingle (SCEVector n t) = reprIsSingle (VectorScalarType (VectorType n (NumSingleType (FloatingNumType t))))
  pairImpossible (SCEFloat t) = pairImpossible (SingleScalarType (NumSingleType (FloatingNumType t)))
  unitImpossible (SCEFloat t) = unitImpossible (SingleScalarType (NumSingleType (FloatingNumType t)))

ctgTypeE :: TypeR t -> TupR SCtgE (Ctg t)
ctgTypeE = \case
  TupRunit -> TupRunit
  TupRpair t1 t2 -> TupRpair (ctgTypeE t1) (ctgTypeE t2)
  TupRsingle (SingleScalarType s) -> case s of
    NumSingleType (IntegralNumType t) -> goInt (Proxy @0) t TupRunit
    NumSingleType (FloatingNumType t@TypeHalf) -> TupRsingle (SCEFloat t)
    NumSingleType (FloatingNumType t@TypeFloat) -> TupRsingle (SCEFloat t)
    NumSingleType (FloatingNumType t@TypeDouble) -> TupRsingle (SCEFloat t)
  TupRsingle (VectorScalarType v) -> case v of
    (VectorType _ (NumSingleType (IntegralNumType t)) :: VectorType (Vec n a)) -> goInt (Proxy @n) t TupRunit
    VectorType n (NumSingleType (FloatingNumType t@TypeHalf)) -> TupRsingle (SCEVector n t)
    VectorType n (NumSingleType (FloatingNumType t@TypeFloat)) -> TupRsingle (SCEVector n t)
    VectorType n (NumSingleType (FloatingNumType t@TypeDouble)) -> TupRsingle (SCEVector n t)
  where
    goInt :: Proxy n -> IntegralType t -> ((Ctg t ~ (), Ctg (Vec n t) ~ ()) => r) -> r
    goInt _ TypeInt k = k
    goInt _ TypeInt8 k = k
    goInt _ TypeInt16 k = k
    goInt _ TypeInt32 k = k
    goInt _ TypeInt64 k = k
    goInt _ TypeWord k = k
    goInt _ TypeWord8 k = k
    goInt _ TypeWord16 k = k
    goInt _ TypeWord32 k = k
    goInt _ TypeWord64 k = k

declareVarsCPS :: TupR s t
               -> (forall env'. LeftHandSide s t env env'
                             -> env :> env'
                             -> (forall env''. env' :> env'' -> Vars s env'' t)
                             -> r)
               -> r
declareVarsCPS tup k
  | DeclareVars lhs w vars <- declareVars tup
  = k lhs w vars

rebuildLHSCPS
  :: LeftHandSide s t env env'
  -> (forall env1'. LeftHandSide s t env1 env1'
                 -> env1 :> env1'
                 -> r)
  -> r
rebuildLHSCPS lhs k
  | Exists lhs' <- rebuildLHS lhs
  = k lhs' (weakenWithLHS lhs')

extendLHSenvType :: TupR s env -> LeftHandSide s t env env' -> TupR s env'
extendLHSenvType t (LeftHandSideSingle s) = TupRpair t (TupRsingle s)
extendLHSenvType t LeftHandSideWildcard{} = t
extendLHSenvType t (LeftHandSidePair lhs1 lhs2) = extendLHSenvType (extendLHSenvType t lhs1) lhs2

data LLHS l s t env env' where
  LLHSSingle :: l t -> s t -> LLHS l s t env (env, t)
  LLHSWild :: TupR s t -> LLHS l s t env env
  LLHSPair :: LLHS l s t1 env1 env2 -> LLHS l s t2 env2 env3 -> LLHS l s (t1, t2) env1 env3

fromLLHS :: LLHS l s t env env' -> LeftHandSide s t env env'
fromLLHS (LLHSSingle _ t) = LeftHandSideSingle t
fromLLHS (LLHSWild t) = LeftHandSideWildcard t
fromLLHS (LLHSPair lhs1 lhs2) = LeftHandSidePair (fromLLHS lhs1) (fromLLHS lhs2)

declareVarsL :: TupR (Label l s) t
             -> (forall env'. LLHS (Const l) s t env env'
                           -> env :> env'
                           -> (forall env''. env' :> env'' -> Vars s env'' t)
                           -> r)
             -> r
declareVarsL TupRunit k =
  k (LLHSWild TupRunit) weakenId (\_ -> TupRunit)
declareVarsL (TupRsingle (Label l t)) k =
  k (LLHSSingle (Fun.Const l) t) (weakenSucc' weakenId) (\w -> TupRsingle (Var t (w >:> ZeroIdx)))
declareVarsL (TupRpair labs1 labs2) k =
  declareVarsL labs1 $ \lhs1 w1 vars1 ->
  declareVarsL labs2 $ \lhs2 w2 vars2 ->
    k (LLHSPair lhs1 lhs2) (w2 .> w1) (\w -> TupRpair (vars1 (w .> weakenWithLLHS lhs2)) (vars2 w))

toLLHS :: (Distributes l', Distributes s) => (forall a. l' a -> l a) -> TupR l' t -> LeftHandSide s t env env' -> LLHS l s t env env'
toLLHS f (TupRsingle l) (LeftHandSideSingle t) = LLHSSingle (f l) t
toLLHS _ _ (LeftHandSideWildcard t) = LLHSWild t
toLLHS f (TupRpair labs1 labs2) (LeftHandSidePair lhs1 lhs2) = LLHSPair (toLLHS f labs1 lhs1) (toLLHS f labs2 lhs2)
toLLHS _ TupRunit (LeftHandSideSingle t) = unitImpossible t
toLLHS _ (TupRsingle l) LeftHandSidePair{} = pairImpossible l
toLLHS _ TupRpair{} (LeftHandSideSingle t) = pairImpossible t

toLLHS' :: (forall a. l a) -> LeftHandSide s t env env' -> LLHS l s t env env'
toLLHS' lab (LeftHandSideSingle t) = LLHSSingle lab t
toLLHS' _   (LeftHandSideWildcard t) = LLHSWild t
toLLHS' lab (LeftHandSidePair lhs1 lhs2) = LLHSPair (toLLHS' lab lhs1) (toLLHS' lab lhs2)

rebuildLLHS
  :: LLHS l s t env env'
  -> (forall env1'. LLHS l s t env1 env1'
                 -> env1 :> env1'
                 -> r)
  -> r
rebuildLLHS (LLHSSingle l t) k = k (LLHSSingle l t) (weakenSucc' weakenId)
rebuildLLHS (LLHSWild t) k = k (LLHSWild t) weakenId
rebuildLLHS (LLHSPair lhs1 lhs2) k =
  rebuildLLHS lhs1 $ \lhs1' w1 ->
  rebuildLLHS lhs2 $ \lhs2' w2 ->
    k (LLHSPair lhs1' lhs2') (w2 .> w1)

weakenWithLLHS :: LLHS l s t env env' -> env :> env'
weakenWithLLHS LLHSSingle{} = weakenSucc' weakenId
weakenWithLLHS LLHSWild{} = weakenId
weakenWithLLHS (LLHSPair lhs1 lhs2) = weakenWithLLHS lhs2 .> weakenWithLLHS lhs1

sinkWithLLHS
  :: LLHS l s t env1 env1'
  -> LLHS l s t env2 env2'
  -> env1 :> env2
  -> env1' :> env2'
sinkWithLLHS LLHSSingle{} LLHSSingle{} = sink
sinkWithLLHS LLHSWild{} LLHSWild{} = id
sinkWithLLHS (LLHSPair lhs1 lhs2) (LLHSPair lhs1' lhs2') = sinkWithLLHS lhs2 lhs2' . sinkWithLLHS lhs1 lhs1'
sinkWithLLHS _ _ = error "sinkWithLLHS: LHSes do not have equal structure"

mapLLHS :: (forall a. l a -> l' a) -> (forall a. s a -> s' a) -> LLHS l s t env env' -> LLHS l' s' t env env'
mapLLHS f g (LLHSSingle l t) = LLHSSingle (f l) (g t)
mapLLHS _ g (LLHSWild t) = LLHSWild (mapTupR g t)
mapLLHS f g (LLHSPair lhs1 lhs2) = LLHSPair (mapLLHS f g lhs1) (mapLLHS f g lhs2)

llhsLabels :: LLHS (Const (Maybe l)) s t env env' -> TupR (Product (Const (Maybe l)) s) t
llhsLabels (LLHSSingle l t) = TupRsingle (Fun.Pair l t)
llhsLabels (LLHSWild t) = mapTupR (Fun.Pair (Fun.Const Nothing)) t
llhsLabels (LLHSPair lhs1 lhs2) = llhsLabels lhs1 `TupRpair` llhsLabels lhs2

llhsLabels' :: LLHS (Const (Maybe l)) s t env env' -> [l]
llhsLabels' (LLHSSingle (Fun.Const (Just l)) _) = [l]
llhsLabels' (LLHSSingle (Fun.Const Nothing) _) = []
llhsLabels' LLHSWild{} = []
llhsLabels' (LLHSPair lhs1 lhs2) = llhsLabels' lhs1 ++ llhsLabels' lhs2

compressLLHS
  :: (forall a. l a -> s a -> Maybe (l' a))
  -> LLHS l s t env env'
  -> (forall t'. TupR l' t' -> Vars s env' t' -> r) -> r
compressLLHS f (LLHSSingle l t) k =
  case f l t of
    Just l' -> k (TupRsingle l') (TupRsingle (Var t ZeroIdx))
    Nothing -> k TupRunit TupRunit
compressLLHS _ LLHSWild{} k = k TupRunit TupRunit
compressLLHS f (LLHSPair lhs1 lhs2) k =
  compressLLHS f lhs1 $ \labs1 vars1 ->
  compressLLHS f lhs2 $ \labs2 vars2 ->
    case (labs1, labs2) of
      (TupRunit, TupRunit) -> k TupRunit TupRunit
      (TupRunit, _) -> k labs2 vars2
      (_, TupRunit) -> k labs1 (weakenVars (weakenWithLLHS lhs2) vars1)
      (_, _) -> k (TupRpair labs1 labs2) (TupRpair (weakenVars (weakenWithLLHS lhs2) vars1) vars2)

data Maybe1 f a = Just1 (f a) | Nothing1
  deriving (Show)

llhsToTupR :: LLHS l s t env env' -> TupR (Product (Maybe1 l) s) t
llhsToTupR (LLHSSingle l t) = TupRsingle (Fun.Pair (Just1 l) t)
llhsToTupR (LLHSWild t) = mapTupR (Fun.Pair Nothing1) t
llhsToTupR (LLHSPair lhs1 lhs2) = llhsToTupR lhs1 `TupRpair` llhsToTupR lhs2

-- Naming consistency please
evars :: ExpVars env a -> PreOpenExp arr env a
evars = returnExpVars
