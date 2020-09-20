{-# LANGUAGE GADTs #-}
module Data.Array.Accelerate.Trafo.AD.Pretty (prettyPrint) where

import qualified Data.Array.Accelerate.AST.Var as A
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Trafo.AD.Acc
import Data.Array.Accelerate.Trafo.AD.Common
import Data.Array.Accelerate.Trafo.AD.Exp
import Data.List (intercalate)


data Layout = LPrefix String Layout        -- Prefix to top line of layout block
            | LBlock [Layout]              -- Block of left-aligned layouts
            | LSeq Layout [Layout]         -- (sep,lts); if all lts are single-line, then separated by sep, else LBlock ignoring sep
            | LMaybeHanging Layout Layout  -- (main,sub); if sub is single-line, then LSeq " ", else LBlock with indent before sub
  deriving (Show)

class Pretty a where
    buildLayout :: a -> Layout

prettyPrint :: Pretty a => a -> String
prettyPrint = format . buildLayout

format :: Layout -> String
format = go 0
  where
    go :: Int -> Layout -> String
    go d (LPrefix str layout) = str ++ go (d + length str) layout
    go _ (LBlock []) = ""
    go d (LBlock (layout : layouts)) =
        go d layout ++ concat ['\n' : replicate d ' ' ++ go d l | l <- layouts]
    go d (LSeq sep layouts)
      | Just strs <- mapM fromSingleLine layouts =
          case fromSingleLine sep of
            Just sepstr -> intercalate sepstr strs
            Nothing -> error "Pretty: Non-single-line separator in LSeq"
      | otherwise =
          go d (LBlock layouts)
    go d (LMaybeHanging main sub)
      | Just str <- fromSingleLine sub = go d (lseq' [main, string str])
      | otherwise = go d (hanging main sub)

fromSingleLine :: Layout -> Maybe String
fromSingleLine (LPrefix str l) = (str ++) <$> fromSingleLine l
fromSingleLine (LBlock []) = Just ""
fromSingleLine (LBlock [l]) = fromSingleLine l
fromSingleLine (LBlock _) = Nothing
fromSingleLine (LSeq sep ls) = intercalate <$> fromSingleLine sep <*> mapM fromSingleLine ls
fromSingleLine (LMaybeHanging main sub) =
    (++) <$> fromSingleLine main <*> ((' ' :) <$> fromSingleLine sub)

hanging :: Layout -> Layout -> Layout
hanging main sub = LBlock [main, LPrefix "  " sub]

string :: String -> Layout
string str = lprefix str (LBlock [])

lprefix :: String -> Layout -> Layout
lprefix = LPrefix

lblock :: [Layout] -> Layout
lblock = LBlock . flattenBlocks
  where
    flattenBlocks [] = []
    flattenBlocks (LBlock ls : ls') = flattenBlocks (ls ++ ls')
    flattenBlocks (l : ls) = l : flattenBlocks ls

lseq :: Layout -> [Layout] -> Layout
lseq = LSeq

lseq' :: [Layout] -> Layout
lseq' = lseq (string " ")

parenthesise :: Bool -> Layout -> Layout
parenthesise True layout = lprefix "(" (insertAtEnd ")" layout)
parenthesise False layout = layout

insertAtEnd :: String -> Layout -> Layout
insertAtEnd str (LPrefix str' (LBlock [])) = LPrefix (str' ++ str) (LBlock [])
insertAtEnd str (LPrefix str' layout) = LPrefix str' (insertAtEnd str layout)
insertAtEnd str (LBlock []) = string str
insertAtEnd str (LBlock ls) = LBlock (init ls ++ [insertAtEnd str (last ls)])
insertAtEnd str (LSeq sep ls) = LSeq sep (init ls ++ [insertAtEnd str (last ls)])
insertAtEnd str (LMaybeHanging main sub) = LMaybeHanging main (insertAtEnd str sub)

tuple :: [Layout] -> Layout
tuple [] = string "()"
tuple layouts@(l:ls)
  | Just strs <- mapM fromSingleLine layouts = string ("(" ++ intercalate ", " strs ++ ")")
  | otherwise = insertAtEnd ")" $ lblock (lprefix "(" l : map (lprefix ",") ls)

instance (Show lab, Show alab) => Pretty (OpenExp env aenv lab alab args t) where
    buildLayout = layoutExp (ShowEnv show show 0 [] []) 0

instance (Show lab, Show alab) => Pretty (OpenAcc aenv lab alab args t) where
    buildLayout = layoutAcc (ShowEnv show show 0 () []) 0

layoutExp :: EShowEnv lab alab -> Int -> OpenExp env aenv lab alab args t -> Layout
layoutExp _ _ (Const ty x) = string (showScalar ty x)
layoutExp se d (PrimApp _ f (Pair _ e1 e2)) | isInfixOp f =
    let prec = precedence f
        ops = prettyPrimFun Infix f
    in parenthesise (d > prec) $ lseq'
          [layoutExp se (prec+1) e1, string ops
          ,layoutExp se (prec+1) e2]
layoutExp se d (PrimApp _ f e) =
    let prec = precedence f
        ops = prettyPrimFun Prefix f
    in parenthesise (d > prec) $
          lseq' [string ops, layoutExp se (prec+1) e]
layoutExp se _ (Pair _ e1 e2) =
    tuple [layoutExp se 0 e1, layoutExp se 0 e2]
layoutExp _ _ Nil =
    string "()"
layoutExp se d (Cond _ c t e) =
    parenthesise (d > 10) $
        lprefix "cond "
            (lseq' [layoutExp se 11 c
                   ,layoutExp se 11 t
                   ,layoutExp se 11 e])
layoutExp se d (Shape (Left (A.Var _ idx))) =
    parenthesise (d > 10) $
        lprefix "shape "
            (case drop (idxToInt idx) (seAenv se) of
                descr : _ -> string descr
                [] -> error $ "Avar out of aenv range in layoutExp: " ++
                              show (idxToInt idx) ++ " in " ++ show (seAenv se))
layoutExp se d (Shape (Right lab)) =
    parenthesise (d > 10) $
        string $ "shape (L" ++ seAlabf se (labelLabel lab) ++ " :: " ++ show (labelType lab) ++ ")"
layoutExp se d (Index (Left (A.Var _ idx)) e) =
    parenthesise (d > 10) $ lseq'
        [case drop (idxToInt idx) (seAenv se) of
            descr : _ -> string descr
            [] -> error $ "Avar out of aenv range in layoutExp: " ++
                          show (idxToInt idx) ++ " in " ++ show (seAenv se)
        ,string "!", layoutExp se 11 e]
layoutExp se d (Index (Right lab) e) =
    parenthesise (d > 10) $ lseq'
        [string ('L' : seAlabf se (labelLabel lab) ++ " :: " ++ show (labelType lab))
        ,string "!", layoutExp se 11 e]
layoutExp se d (ShapeSize _ e) =
    parenthesise (d > 10) $
        lprefix "shapeSize " (layoutExp se 11 e)
layoutExp se d (Get _ ti e) = parenthesise (d > 10) $
    lprefix (tiPrefix ti) (layoutExp se 11 e)
  where
    tiPrefix :: TupleIdx t t' -> String
    tiPrefix = (++ " ") . intercalate "." . reverse . tiPrefix'

    tiPrefix' :: TupleIdx t t' -> [String]
    tiPrefix' TIHere = []
    tiPrefix' (TILeft ti') = "fst" : tiPrefix' ti'
    tiPrefix' (TIRight ti') = "snd" : tiPrefix' ti'
layoutExp se d (Let lhs rhs body) = parenthesise (d > 0) $
    let (descr, descrs, seed') = namifyLHS (seSeed se) lhs
        env' = descrs ++ seEnv se
    in lblock [LMaybeHanging (string ("let " ++ descr ++ " ="))
                             (layoutExp (se { seSeed = seed' }) 0 rhs)
              ,case body of
                   Let _ _ _ -> layoutExp (se { seSeed = seed', seEnv = env' }) 0 body
                   _ -> lprefix "in " (layoutExp (se { seSeed = seed', seEnv = env' }) 0 body)]
layoutExp _ d (Arg ty idx) = parenthesise (d > 0) $
    string ('A' : show (idxToInt idx) ++ " :: " ++ show ty)
layoutExp se _ (Var (A.Var _ idx)) =
    case drop (idxToInt idx) (seEnv se) of
        descr : _ -> string descr
        [] -> error $ "Var out of env range in layoutExp: " ++
                      show (idxToInt idx) ++ " in " ++ show (seEnv se)
layoutExp se d (Label lab) = parenthesise (d > 0) $
    string ('L' : seLabf se (labelLabel lab) ++ " :: " ++ show (labelType lab))

layoutAcc :: AShowEnv lab alab -> Int -> OpenAcc env lab alab args t -> Layout
layoutAcc _ _ (Aconst ty x) =
    string (showArray (showString . showTupR' showScalar (arrayRtype ty)) ty x)
layoutAcc se _ (Apair _ e1 e2) =
    tuple [layoutAcc se 0 e1, layoutAcc se 0 e2]
layoutAcc _ _ Anil =
    string "()"
layoutAcc se d (Acond _ c t e) =
    parenthesise (d > 10) $
        lprefix "acond "
            (lseq' [layoutExp (se { seEnv = [] }) 11 c
                   ,layoutAcc se 11 t
                   ,layoutAcc se 11 e])
layoutAcc se d (Map _ f e) =
    parenthesise (d > 10) $
        lprefix "map "
            (lseq' [layoutLambda (se { seEnv = [] }) 11 f
                   ,layoutAcc se 11 e])
layoutAcc se d (ZipWith _ f e1 e2) =
    parenthesise (d > 10) $
        lprefix "zipWith "
            (lseq' [layoutLambda (se { seEnv = [] }) 11 f
                   ,layoutAcc se 11 e1
                   ,layoutAcc se 11 e2])
layoutAcc se d (Fold _ f me0 e) =
    parenthesise (d > 10) $
        lprefix (maybe "fold1 " (const "fold ") me0)
            (lseq' $ concat [[layoutLambda (se { seEnv = [] }) 11 f]
                            ,maybe [] (\e0 -> [layoutExp (se { seEnv = [] }) 11 e0]) me0
                            ,[layoutAcc se 11 e]])
layoutAcc se d (Sum _ e) =
    parenthesise (d > 10) $
        lprefix "sum " (layoutAcc se 11 e)
layoutAcc se d (Generate _ sh f) =
    parenthesise (d > 10) $
        lprefix "generate "
            (lseq' [layoutExp (se { seEnv = [] }) 11 sh
                   ,layoutLambda (se { seEnv = [] }) 11 f])
layoutAcc se d (Aget _ ti e) = parenthesise (d > 10) $
    lprefix (tiPrefix ti) (layoutAcc se 11 e)
  where
    tiPrefix :: TupleIdx t t' -> String
    tiPrefix = (++ " ") . intercalate "." . reverse . tiPrefix'

    tiPrefix' :: TupleIdx t t' -> [String]
    tiPrefix' TIHere = []
    tiPrefix' (TILeft ti') = "afst" : tiPrefix' ti'
    tiPrefix' (TIRight ti') = "asnd" : tiPrefix' ti'
layoutAcc se d (Alet lhs rhs body) = parenthesise (d > 0) $
    let (descr, descrs, seed') = namifyLHS (seSeed se) lhs
        env' = descrs ++ seAenv se
    in lblock [LMaybeHanging (string ("let " ++ descr ++ " ="))
                             (layoutAcc (se { seSeed = seed' }) 0 rhs)
              ,case body of
                   Alet _ _ _ -> layoutAcc (se { seSeed = seed', seAenv = env' }) 0 body
                   _ -> lprefix "in " (layoutAcc (se { seSeed = seed', seAenv = env' }) 0 body)]
layoutAcc _ d (Aarg ty idx) = parenthesise (d > 0) $
    string ('A' : show (idxToInt idx) ++ " :: " ++ show ty)
layoutAcc se _ (Avar (A.Var _ idx)) =
    case drop (idxToInt idx) (seAenv se) of
        descr : _ -> string descr
        [] -> error $ "Var out of env range in layoutAcc: " ++
                      show (idxToInt idx) ++ " in " ++ show (seEnv se)
layoutAcc se d (Alabel lab) = parenthesise (d > 0) $
    string ('L' : seAlabf se (labelLabel lab) ++ " :: " ++ show (labelType lab))

layoutFun :: EShowEnv lab alab -> Int -> OpenFun env aenv lab alab t -> Layout
layoutFun se d (Body expr) = layoutExp se d expr
layoutFun se d (Lam lhs fun) =
    let (descr, descrs, seed') = namifyLHS (seSeed se) lhs
        env' = descrs ++ seEnv se
    in parenthesise (d > 0) $
        LMaybeHanging (string ("\\" ++ descr ++ " ->"))
                      (layoutFun (se { seSeed = seed', seEnv = env' }) 0 fun)

layoutLambda :: EShowEnv lab alab -> Int -> ExpLambda1 aenv lab alab sh t1 t2 -> Layout
layoutLambda se d (Right fun) = layoutFun se d fun
layoutLambda _ _ (Left _) = string "{splitlambda}"
