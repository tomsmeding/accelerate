{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Data.Array.Accelerate.Interpreter.Simple2 where

import           Data.List (foldl')
import qualified Data.Text.IO as T
import           Formatting
import           GHC.Stack
import           System.IO (stderr, hFlush)
import           System.IO.Unsafe (unsafePerformIO)

import           Data.Array.Accelerate.AST
import           Data.Array.Accelerate.AST.Environment
import           Data.Array.Accelerate.AST.Var
import           Data.Array.Accelerate.Error
import qualified Data.Array.Accelerate.Smart as Smart
import qualified Data.Array.Accelerate.Sugar.Array as Sugar
import qualified Data.Array.Accelerate.Representation.Array as R
import qualified Data.Array.Accelerate.Representation.Shape as R
import qualified Data.Array.Accelerate.Representation.Slice as R
import           Data.Array.Accelerate.Representation.Type
import qualified Data.Array.Accelerate.Trafo.Sharing as Sharing
import           Data.Array.Accelerate.Type (scalarType)


{-# NOINLINE run #-}
run :: (HasCallStack, Sugar.Arrays arrs) => Smart.Acc arrs -> arrs
run prog = Sugar.toArr . snd $ unsafePerformIO $ eval Empty (Sharing.convertAcc prog)

eval :: Val aenv -> OpenAcc aenv a -> IO (R.ArraysR a, a)
eval aenv (OpenAcc topacc) = case topacc of
  Alet lhs rhs body -> do
    (_, x) <- eval aenv rhs
    eval (aenv `push` (lhs, x)) body

  Avar (Var ty idx) -> pure (TupRsingle ty, prj idx aenv)

  Apair a b -> do
    (ty1, x) <- eval aenv a
    (ty2, y) <- eval aenv b
    pure (TupRpair ty1 ty2, (x, y))

  Anil -> pure (TupRunit, ())

  Apply _ (Alam lhs (Abody body)) arg -> do
    (_, x) <- eval aenv arg
    eval (aenv `push` (lhs, x)) body
  Apply _ (Abody a) _ -> R.arraysRFunctionImpossible (arraysR a)
  Apply ty (Alam _ Alam{}) _ -> R.arraysRFunctionImpossible ty

  Aforeign _ _ (Alam lhs (Abody body)) arg -> do
    (_, x) <- eval aenv arg
    eval (Empty `push` (lhs, x)) body
  Aforeign _ _ (Abody a) _ -> R.arraysRFunctionImpossible (arraysR a)
  Aforeign ty _ (Alam _ Alam{}) _ -> R.arraysRFunctionImpossible ty

  Acond e a b
    | evalE aenv Empty e == 1 -> eval aenv a
    | otherwise               -> eval aenv b

  Awhile (Alam clhs (Abody cond)) (Alam blhs (Abody body)) arg -> do
    let loop ty x = do
          (_, c) <- eval (aenv `push` (clhs, x)) cond
          if R.linearIndexArray (TupRsingle scalarType) c 0 == 1
            then uncurry loop =<< eval (aenv `push` (blhs, x)) body
            else pure (ty, x)
    uncurry loop =<< eval aenv arg

  Atrace msg arg a -> do
    atraceOp msg . snd =<< eval aenv arg
    eval aenv a

  Use ty arr -> pure (TupRsingle ty, arr)

  Unit ty e ->
    let aty = R.ArrayR R.ShapeRz ty
    in pure (TupRsingle aty, R.fromList aty () [evalE aenv Empty e])

  Reshape shty she a -> do
    (TupRsingle (R.ArrayR shty' ty), x) <- eval aenv a
    pure (TupRsingle (R.ArrayR shty ty), R.reshape shty (evalE aenv Empty she) shty' x)

  Generate aty she (Lam lhs (Body body)) ->
    pure (TupRsingle aty
         ,R.fromFunction aty (evalE aenv Empty she) $ \idx ->
            evalE aenv (Empty `push` (lhs, idx)) body)

  Transform atyOut sheOut (Lam idxlhs (Body idxbody)) (Lam maplhs (Body mapbody)) a -> do
    (TupRsingle aty, arr) <- eval aenv a
    pure (TupRsingle atyOut
         ,R.fromFunction atyOut (evalE aenv Empty sheOut) $ \idx ->
           let x = (aty, arr) R.! evalE aenv (Empty `push` (idxlhs, idx)) idxbody
           in evalE aenv (Empty `push` (maplhs, x)) mapbody)

  Replicate slixty slixe a -> do
    (TupRsingle aty@(R.ArrayR _ ty), arr) <- eval aenv a
    let atyOut = R.ArrayR (R.sliceDomainR slixty) ty
        slix = evalE aenv Empty slixe
    pure (TupRsingle atyOut
         ,R.fromFunction atyOut (R.sliceDomain slixty slix (R.shape arr)) $ \idx ->
            (aty, arr) R.! R.sliceShape slixty idx)

  Slice slixty a slixe -> do
    (TupRsingle aty@(R.ArrayR _ ty), arr) <- eval aenv a
    let atyOut = R.ArrayR (R.sliceShapeR slixty) ty
        slix = evalE aenv Empty slixe
    pure (TupRsingle atyOut
         ,R.fromFunction atyOut (R.sliceShape slixty (R.shape arr)) $ \idx ->
            (aty, arr) R.! R.sliceDomain slixty slix idx)

  Map tyOut (Lam lhs (Body body)) a -> do
    (TupRsingle (R.ArrayR shty ty), arr) <- eval aenv a
    let atyOut = R.ArrayR shty tyOut
    res <- R.fromFunctionLinearM atyOut (R.shape arr) $ \idx ->
             pure $ evalE aenv (Empty `push` (lhs, (ty, arr) R.!! idx)) body
    pure (TupRsingle atyOut, res)

  ZipWith tyOut (Lam lhs1 (Lam lhs2 (Body body))) a b -> do
    (TupRsingle aty1@(R.ArrayR shty _), arr1) <- eval aenv a
    (TupRsingle aty2, arr2) <- eval aenv b
    let atyOut = R.ArrayR shty tyOut
    pure (TupRsingle atyOut
         ,R.fromFunction atyOut (R.intersect shty (R.shape arr1) (R.shape arr2)) $ \idx ->
             evalE aenv (Empty `push` (lhs1, (aty1, arr1) R.! idx)
                               `push` (lhs2, (aty2, arr2) R.! idx))
                        body)

  Fold (Lam lhs1 (Lam lhs2 (Body body))) mdefe a -> do
    (TupRsingle aty@(R.ArrayR (R.ShapeRsnoc shty) ty), arr) <- eval aenv a
    let (sh, n) = R.shape arr
    pure $ case mdefe of
      Just defe ->
        let x0 = evalE aenv Empty defe 
        in (TupRsingle (R.ArrayR shty ty)
           ,R.fromFunction (R.ArrayR shty ty) sh $ \idx ->
              foldl' (\x y -> evalE aenv (Empty `push` (lhs1, x) `push` (lhs2, y)) body) x0
                     [(aty, arr) R.! (idx, i) | i <- [0 .. n - 1]])
      Nothing ->
        boundsCheck "empty array" (n > 0) $
          (TupRsingle (R.ArrayR shty ty)
          ,R.fromFunction (R.ArrayR shty ty) sh $ \idx ->
             foldl' (\x y -> evalE aenv (Empty `push` (lhs1, x) `push` (lhs2, y)) body)
                    ((aty, arr) R.! (idx, 0))
                    [(aty, arr) R.! (idx, i) | i <- [1 .. n - 1]])

  _ -> _

evalE :: Val aenv -> Val env -> OpenExp env aenv a -> a
evalE aenv env = \case
  _ -> _

atraceOp :: Message as -> as -> IO ()
atraceOp (Message fun _ msg) as = do
  let str = fun as
  if null str
     then T.hPutStrLn stderr msg
     else hprint stderr (stext % ": " % string % "\n") msg str
  hFlush stderr

zeroIdx :: R.ShapeR sh -> sh
zeroIdx R.ShapeRz = ()
zeroIdx (R.ShapeRsnoc shty) = (zeroIdx shty, 0)
