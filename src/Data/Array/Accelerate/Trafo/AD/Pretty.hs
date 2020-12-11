{-# LANGUAGE GADTs #-}
module Data.Array.Accelerate.Trafo.AD.Pretty (prettyPrint) where

import qualified Data.Array.Accelerate.AST as A
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

tuple :: String -> [Layout] -> Layout
tuple suffix [] = string ("()" ++ suffix)
tuple suffix layouts@(l:ls)
  | Just strs <- mapM fromSingleLine layouts = string ("(" ++ intercalate ", " strs ++ ")" ++ suffix)
  | otherwise = insertAtEnd (")" ++ suffix) $ lblock (lprefix "(" l : map (lprefix ",") ls)

instance (Show lab, Show alab) => Pretty (OpenExp env aenv lab alab args tenv t) where
    buildLayout = layoutExp (ShowEnv show show 0 [] []) 0

instance (Show lab, Show alab) => Pretty (OpenAcc aenv lab alab args t) where
    buildLayout = layoutAcc (ShowEnv show show 0 () []) 0

layoutExp :: EShowEnv lab alab -> Int -> OpenExp env aenv lab alab args tenv t -> Layout
layoutExp se _ (Const lab x) =
    string (showScalar (labelType lab) x ++ showLabelSuffix' se lab)
layoutExp se d (PrimApp lab f (Pair _ e1 e2))
  | isInfixOp f, "" <- showLabelSuffix se lab "" =
      let prec = precedence f
          ops = prettyPrimFun Infix f
      in parenthesise (d > prec) $ lseq'
            [layoutExp se (prec+1) e1, string ops
            ,layoutExp se (prec+1) e2]
layoutExp se d (PrimApp lab f e) =
    let prec = precedence f
        ops = prettyPrimFun Prefix f
    in parenthesise (d > prec) $
          lseq' [string (ops ++ showLabelSuffix' se lab), layoutExp se (prec+1) e]
layoutExp se _ (PrimConst lab c) = string (show c ++ showLabelSuffix' se lab)
layoutExp se _ (Pair lab e1 e2) =
    tuple (showLabelSuffix' se lab) [layoutExp se 0 e1, layoutExp se 0 e2]
layoutExp se _ (Nil lab) =
    string ("()" ++ showLabelSuffix' se lab)
layoutExp se d (Cond lab c t e) =
    parenthesise (d > 10) $
        lprefix ("cond" ++ showLabelSuffix' se lab ++ " ")
            (lseq' [layoutExp se 11 c
                   ,layoutExp se 11 t
                   ,layoutExp se 11 e])
layoutExp se d (Shape lab (Left (A.Var _ idx))) =
    parenthesise (d > 10) $
        lprefix ("shape " ++ showLabelSuffix' se lab ++ " ")
            (case drop (idxToInt idx) (seAenv se) of
                descr : _ -> string descr
                [] -> string ("tA_UP" ++ show (1 + idxToInt idx - length (seAenv se))))
layoutExp se d (Shape lab (Right alab)) =
    parenthesise (d > 10) $
        string $ "shape" ++ showLabelSuffix' se lab ++ " (L" ++
                 seAlabf se (labelLabel alab) ++ " :: " ++ show (labelType alab) ++ ")"
layoutExp se d (Index lab subj execLab e) =
    parenthesise (d > 10) $ lseq'
        [case subj of
           Left (A.Var _ idx) ->
              case drop (idxToInt idx) (seAenv se) of
                  descr : _ -> string descr
                  [] -> string ("tA_UP" ++ show (1 + idxToInt idx - length (seAenv se)))
           Right alab ->
              string ('L' : seAlabf se (labelLabel alab) ++ " :: " ++ show (labelType alab))
        ,string ("!" ++ showLabelSuffix' se lab ++
                    (case showLabelSuffix' se execLab of
                       "" -> ""
                       str -> "[exec=" ++ str ++ "]"))
        ,layoutExp se 11 e ]
layoutExp se d (ShapeSize lab _ e) =
    parenthesise (d > 10) $
        lprefix ("shapeSize" ++ showLabelSuffix' se lab ++ " ") (layoutExp se 11 e)
layoutExp se d (Get lab ti e) = parenthesise (d > 10) $
    lprefix (tiPrefixExp ti ++ showLabelSuffix' se lab ++ " ") (layoutExp se 11 e)
layoutExp se _ (Undef lab) = string ("undef" ++ showLabelSuffix' se lab)
layoutExp se d (Let lhs rhs body) = parenthesise (d > 0) $
    let (descr, descrs, seed') = namifyLHS (seSeed se) lhs
        env' = descrs ++ seEnv se
    in lblock [LMaybeHanging (string ("let " ++ descr ++ " ="))
                             (layoutExp (se { seSeed = seed' }) 0 rhs)
              ,case body of
                   Let _ _ _ -> layoutExp (se { seSeed = seed', seEnv = env' }) 0 body
                   _ -> lprefix "in " (layoutExp (se { seSeed = seed', seEnv = env' }) 0 body)]
layoutExp se _ (Var lab (A.Var _ idx) (PartLabel referLab referPart)) =
    let varstr
          | descr : _ <- drop (idxToInt idx) (seEnv se) = descr
          | otherwise = "tE_UP" ++ show (1 + idxToInt idx - length (seEnv se))
    in case showLabelSuffix se referLab "" of
         "" -> string varstr
         referLabStr ->
             string ("(" ++ varstr ++ "->" ++ tiPrefixExp referPart ++ " " ++
                        referLabStr ++ ")" ++ showLabelSuffix' se lab)
layoutExp se d (FreeVar lab (A.Var ty idx)) = parenthesise (d > 0) $
    string ("tFREE" ++ show (1 + idxToInt idx) ++ showLabelSuffix' se lab ++ " :: " ++ show ty)
layoutExp se d (Arg lab _ tidx) = parenthesise (d > 0) $
    string ('A' : compactTupleIdx tidx ++ showLabelSuffix' se lab ++ " :: " ++ show (labelType lab))

layoutAcc :: AShowEnv lab alab -> Int -> OpenAcc env lab alab args t -> Layout
layoutAcc se _ (Aconst lab@DLabel { labelType = ty } x) =
    string (showArray (showString . showTupR' showScalar (arrayRtype ty)) ty x ++
                ashowLabelSuffix' se lab)
layoutAcc se _ (Apair lab e1 e2) =
    tuple (ashowLabelSuffix' se lab) [layoutAcc se 0 e1, layoutAcc se 0 e2]
layoutAcc se _ (Anil lab) =
    string ("()" ++ ashowLabelSuffix' se lab)
layoutAcc se d (Acond lab c t e) =
    parenthesise (d > 10) $
        lprefix ("acond" ++ ashowLabelSuffix' se lab ++ " ")
            (lseq' [layoutExp (se { seEnv = [] }) 11 c
                   ,layoutAcc se 11 t
                   ,layoutAcc se 11 e])
layoutAcc se d (Map lab f e) =
    parenthesise (d > 10) $
        lprefix ("map" ++ ashowLabelSuffix' se lab ++ " ")
            (lseq' [layoutLambda (se { seEnv = [] }) 11 f
                   ,layoutAcc se 11 e])
layoutAcc se d (ZipWith lab f e1 e2) =
    parenthesise (d > 10) $
        lprefix ("zipWith" ++ ashowLabelSuffix' se lab ++ " ")
            (lseq' [layoutLambda (se { seEnv = [] }) 11 f
                   ,layoutAcc se 11 e1
                   ,layoutAcc se 11 e2])
layoutAcc se d (Fold lab f me0 e) =
    parenthesise (d > 10) $
        lprefix (maybe "fold1" (const "fold") me0 ++ ashowLabelSuffix' se lab ++ " ")
            (lseq' $ concat [[layoutFun (se { seEnv = [] }) 11 f]
                            ,maybe [] (\e0 -> [layoutExp (se { seEnv = [] }) 11 e0]) me0
                            ,[layoutAcc se 11 e]])
layoutAcc se d (Scan lab dir f me0 e) =
    parenthesise (d > 10) $
        lprefix ("scan" ++ (case dir of A.LeftToRight -> "l" ; A.RightToLeft -> "r") ++ maybe "1" (const "") me0 ++
                     ashowLabelSuffix' se lab ++ " ")
            (lseq' $ concat [[layoutFun (se { seEnv = [] }) 11 f]
                            ,maybe [] (\e0 -> [layoutExp (se { seEnv = [] }) 11 e0]) me0
                            ,[layoutAcc se 11 e]])
layoutAcc se d (Scan' lab dir f e0 e) =
    parenthesise (d > 10) $
        lprefix ("scan" ++ (case dir of A.LeftToRight -> "l" ; A.RightToLeft -> "r") ++ "'" ++
                     ashowLabelSuffix' se lab ++ " ")
            (lseq' [layoutFun (se { seEnv = [] }) 11 f
                   ,layoutExp (se { seEnv = [] }) 11 e0
                   ,layoutAcc se 11 e])
layoutAcc se d (Backpermute lab dim f e) =
    parenthesise (d > 10) $
        lprefix ("backpermute" ++ ashowLabelSuffix' se lab ++ " ")
            (lseq' [layoutExp (se { seEnv = [] }) 11 dim
                   ,layoutFun (se { seEnv = [] }) 11 f
                   ,layoutAcc se 11 e])
layoutAcc se d (Permute lab cf def pf e) =
    parenthesise (d > 10) $
        lprefix ("permute" ++ ashowLabelSuffix' se lab ++ " ")
            (lseq' [layoutFun (se { seEnv = [] }) 11 cf
                   ,layoutAcc se 11 def
                   ,layoutFun (se { seEnv = [] }) 11 pf
                   ,layoutAcc se 11 e])
layoutAcc se d (Sum lab e) =
    parenthesise (d > 10) $
        lprefix ("sum" ++ ashowLabelSuffix' se lab ++ " ")
            (layoutAcc se 11 e)
layoutAcc se d (Generate lab sh f) =
    parenthesise (d > 10) $
        lprefix ("generate" ++ ashowLabelSuffix' se lab ++ " ")
            (lseq' [layoutExp (se { seEnv = [] }) 11 sh
                   ,layoutLambda (se { seEnv = [] }) 11 f])
layoutAcc se d (Replicate lab _ she e) =
    parenthesise (d > 10) $
        lprefix ("replicate" ++ ashowLabelSuffix' se lab ++ " ")
            (lseq' [layoutExp (se { seEnv = [] }) 11 she
                   ,layoutAcc se 11 e])
layoutAcc se d (Slice lab _ e she) =
    parenthesise (d > 10) $
        lprefix ("slice" ++ ashowLabelSuffix' se lab ++ " ")
            (lseq' [layoutAcc se 11 e
                   ,layoutExp (se { seEnv = [] }) 11 she])
layoutAcc se d (Reduce lab slt f e) =
    parenthesise (d > 10) $
        lprefix ("reduce" ++ ashowLabelSuffix' se lab ++ " ")
            (lseq' [string (showRSpec slt)
                   ,layoutFun (se { seEnv = [] }) 11 f
                   ,layoutAcc se 11 e])
layoutAcc se d (Reshape lab she e) =
    parenthesise (d > 10) $
        lprefix ("reshape" ++ ashowLabelSuffix' se lab ++ " ")
            (lseq' [layoutExp (se { seEnv = [] }) 11 she
                   ,layoutAcc se 11 e])
layoutAcc se d (Aget lab ti e) = parenthesise (d > 10) $
    lprefix (tiPrefixAcc ti ++ ashowLabelSuffix' se lab ++ " ") (layoutAcc se 11 e)
layoutAcc se d (Alet lhs rhs body) = parenthesise (d > 0) $
    let (descr, descrs, seed') = namifyLHS (seSeed se) lhs
        env' = descrs ++ seAenv se
    in lblock [LMaybeHanging (string ("let " ++ descr ++ " ="))
                             (layoutAcc (se { seSeed = seed' }) 0 rhs)
              ,case body of
                   Alet _ _ _ -> layoutAcc (se { seSeed = seed', seAenv = env' }) 0 body
                   _ -> lprefix "in " (layoutAcc (se { seSeed = seed', seAenv = env' }) 0 body)]
layoutAcc se _ (Avar lab (A.Var _ idx) referLab) =
    let varstr
          | descr : _ <- drop (idxToInt idx) (seAenv se) = descr
          | otherwise = "tA_UP" ++ show (1 + idxToInt idx - length (seAenv se))
    in case ashowLabelSuffix se referLab "" of
         "" -> string varstr
         referLabStr ->
             string ("(" ++ varstr ++ "->" ++ referLabStr ++ ")" ++ ashowLabelSuffix' se lab)
layoutAcc se d (Aarg lab idx) = parenthesise (d > 0) $
    string ('A' : show (idxToInt idx) ++ ashowLabelSuffix' se lab ++ " :: " ++ show (labelType lab))

layoutFun :: EShowEnv lab alab -> Int -> OpenFun env aenv lab alab tenv t -> Layout
layoutFun se d (Body expr) = layoutExp se d expr
layoutFun se d (Lam lhs fun) =
    let (descr, descrs, seed') = namifyLHS (seSeed se) lhs
        env' = descrs ++ seEnv se
    in parenthesise (d > 0) $
        LMaybeHanging (string ("\\" ++ descr ++ " ->"))
                      (layoutFun (se { seSeed = seed', seEnv = env' }) 0 fun)

layoutLambda :: EShowEnv lab alab -> Int -> ExpLambda1 aenv lab alab tenv sh t1 t2 -> Layout
layoutLambda se d (ELPlain fun) = layoutFun se d fun
layoutLambda _ _ ELSplit{} = string "{splitlambda}"

showRSpec :: ReduceSpec spec red full -> String
showRSpec RSpecNil = "()"
showRSpec (RSpecReduce spec) = "(" ++ showRSpec spec ++ ", [red])"
showRSpec (RSpecKeep spec) = "(" ++ showRSpec spec ++ ", [keep])"

showLabelSuffix' :: EShowEnv lab alab -> DLabel lty s lab t -> String
showLabelSuffix' se lab = showLabelSuffix se lab ""

ashowLabelSuffix' :: AShowEnv lab alab -> DLabel lty s alab t -> String
ashowLabelSuffix' se lab = ashowLabelSuffix se lab ""
