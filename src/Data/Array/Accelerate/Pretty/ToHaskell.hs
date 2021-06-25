{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
module Data.Array.Accelerate.Pretty.ToHaskell (
  showAsHaskell,
  showsAsHaskell,
  afterTrafo',
) where

import Control.Monad.State.Strict
import Data.List (intercalate)

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Error
import qualified Data.Array.Accelerate.Pretty.Print as PP
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import qualified Data.Array.Accelerate.Smart as Smart
import qualified Data.Array.Accelerate.Sugar.Array as Sugar
import qualified Data.Array.Accelerate.Trafo as Trafo
import qualified Data.Array.Accelerate.Trafo.UnDelayed as Trafo
import Data.Array.Accelerate.Type


-- Show an OpenAcc as a Haskell-parseable code fragment
-- ----------------------------------------------------

showAsHaskell :: OpenAcc aenv t -> String
showAsHaskell = ($ "") . showsAsHaskell

showsAsHaskell :: OpenAcc aenv t -> ShowS
showsAsHaskell = format . evalIdGen . layoutAO 0 Top

-- | Internalises and optimises the Accelerate program, then converts back from
-- the post-fusion delayed representation to a normal internal AST. This result
-- can then be shown using 'showsAsHaskell'.
afterTrafo' :: Smart.Acc a -> Acc (Sugar.ArraysR a)
afterTrafo' acc = Trafo.unDelayed $ Trafo.convertAcc acc


-- Layout DSL
-- ----------

data Layout = Prefix String [Layout]
  deriving (Show)

format :: Layout -> ShowS
format = \ly -> format' "" ly . showString "\n"
  where
    -- Assumes it is already indented with the indent string (spaces only!) on
    -- the current line.
    format' :: String -> Layout -> ShowS
    format' _ (Prefix s []) =
      showString s
    format' left (Prefix s (ly:lys)) =
      let left' = replicate (length s) ' ' ++ left
      in showString s . format' left' ly
         . foldr (.) id [showString ('\n' : left') . format' left' ly'
                        | ly' <- lys]

fromOneLine :: Layout -> Maybe String
fromOneLine (Prefix s []) = Just s
fromOneLine (Prefix s [l]) = (s ++) <$> fromOneLine l
fromOneLine (Prefix _ _) = Nothing

indent :: Layout -> Layout
indent ly = Prefix "  " [ly]

-- head
--   arg1
--   arg2
-- Puts on one line if all arguments are single-line.
hang :: String -> [Layout] -> Layout
hang hd args
  | Just args' <- traverse fromOneLine args
  = string (hd ++ concatMap (" " ++) args')
  | otherwise
  = vsep [string hd
         ,indent (vsep args)]

-- head arg1
--      arg2
-- Puts on one line if all arguments are single-line. Essentially a friendly
-- interface to Prefix.
posthang :: String -> [Layout] -> Layout
posthang hd args
  | Just args' <- traverse fromOneLine args
  = string (hd ++ concatMap (" " ++) args')
  | otherwise
  = Prefix (hd ++ " ") args

-- If both arguments are single-line, places them horizontally next to each
-- other. If one of them isn't, becomes vsep.
hsepvsep :: Layout -> Layout -> Layout
hsepvsep ly1 ly2
  | Just s1 <- fromOneLine ly1
  , Just s2 <- fromOneLine ly2
  = string (s1 ++ ' ' : s2)
  | otherwise
  = vsep [ly1, ly2]

vsep :: [Layout] -> Layout
vsep = Prefix ""

string :: String -> Layout
string s = Prefix s []

parenthesise :: Bool -> Layout -> Layout
parenthesise False l = l
parenthesise True l = Prefix "(" [insertAtEnd ")" l]

insertAtEnd :: String -> Layout -> Layout
insertAtEnd s (Prefix s' []) = Prefix (s' ++ s) []
insertAtEnd s (Prefix s' ls) = Prefix s' (init ls ++ [insertAtEnd s (last ls)])


-- Layouting functions
-- -------------------

layoutAO :: Int -> Env taenv aenv -> OpenAcc aenv t -> IdGen Layout
layoutAO p aenv (OpenAcc acc) = layoutA p aenv acc

layoutAF :: Int -> Env taenv aenv -> PreOpenAfun OpenAcc aenv t -> IdGen Layout
layoutAF p aenv (Abody a) = layoutAO p aenv a
layoutAF p aenv afun@Alam{} = do
  (argsString, body) <- go aenv afun
  return (parenthesise (p > 0) $
            hang ("\\" ++ argsString ++ " ->") [body])
  where
    go :: Env taenv aenv -> PreOpenAfun OpenAcc aenv t -> IdGen (String, Layout)
    go aenv' (Abody a) = ("",) <$> layoutAO 0 aenv' a
    go aenv' (Alam lhs afun') = do
      (aenv'', lhsString) <- layoutLHS 11 IdTypeA aenv' lhs
      (rest, body) <- go aenv'' afun'
      return (lhsString rest, body)

layoutA :: Int
        -> Env taenv aenv
        -> PreOpenAcc OpenAcc aenv t
        -> IdGen Layout
layoutA p aenv = \case
  Alet lhs rhs a -> parenthesise (p > 0) <$> do
    (bindings, body) <- layoutAlet aenv lhs rhs a
    return $ hsepvsep (Prefix "let " bindings)
                      (Prefix "in " [body])

  Avar var ->
    return (string (layoutVar "a" aenv var))

  Apair a1 a2 ->
    parenthesise (p > 10) <$>
      posthang "T2" <$>> [layoutAO 11 aenv a1
                         ,layoutAO 11 aenv a2]

  Anil -> parenthesise (p > 10) <$> do
    return (string "use ()")

  Apply _ _ _ -> internalError "showsAsHaskell: Don't know what to do with Apply"

  Aforeign _ _ _ _ -> internalError "showsAsHaskell: Foreign calls unsupported"

  Acond e a1 a2 ->
    parenthesise (p > 10) <$>
      hang "acond" <$>> [layoutE 11 FNormal aenv Top e
                        ,layoutAO 11 aenv a1
                        ,layoutAO 11 aenv a2]

  Awhile a1 a2 a3 ->
    parenthesise (p > 10) <$>
      hang "awhile" <$>> [layoutAF 11 aenv a1
                         ,layoutAF 11 aenv a2
                         ,layoutAO 11 aenv a3]

  -- TODO: this collapses 'atraceArray' down to 'atrace'
  Atrace (Message _ _ msg) a1 a2 ->
    parenthesise (p > 10) <$>
      hang "atrace" <$>> [return (string (show msg))
                         ,layoutAO 11 aenv a1
                         ,layoutAO 11 aenv a2]

  Use ty@(ArrayR shty eltty) arr@(Array sh _) ->
    let shapeStr = showShape shty sh
        showShapeType :: ShapeR sh -> String
        showShapeType ShapeRz = "Z"
        showShapeType (ShapeRsnoc sh') = showShapeType sh' ++ " :. Int"
        str = concat ["use (fromList "
                     ,if shapeStr == "Z" then shapeStr else "(" ++ shapeStr ++ ")"
                     ," "
                     ,case tupHasShow scalarHasShow eltty of
                        Has -> show (toList ty arr)
                     ," :: Array "
                     ,let s = showShapeType shty
                      in if s == "Z" then s else "(" ++ s ++ ")"
                     ," "
                     ,show eltty
                     ,")"]
    in return (parenthesise (p > 10) (string str))

  Unit _ e ->
    parenthesise (p > 10) <$>
      hang "unit" <$>> [layoutE 11 FNormal aenv Top e]

  Reshape _ e a1 ->
    parenthesise (p > 10) <$>
      hang "reshape" <$>> [layoutE 11 FIndex aenv Top e
                          ,layoutAO 11 aenv a1]

  Generate _ e ef ->
    parenthesise (p > 10) <$>
      hang "generate" <$>> [layoutE 11 FIndex aenv Top e
                           ,layoutEF 11 FIndex FNormal aenv Top ef]

  Transform _ e ef1 ef2 a1 ->
    parenthesise (p > 10) <$>
      hang "transform" <$>> [layoutE 11 FIndex aenv Top e
                            ,layoutEF 11 FIndex FIndex aenv Top ef1
                            ,layoutEF 11 FIndex FNormal aenv Top ef2
                            ,layoutAO 11 aenv a1]

  Replicate _ e a1 ->
    parenthesise (p > 10) <$>
      hang "replicate" <$>> [layoutE 11 FIndex aenv Top e
                            ,layoutAO 11 aenv a1]

  Slice _ a1 e ->
    parenthesise (p > 10) <$>
      hang "slice" <$>> [layoutAO 11 aenv a1
                        ,layoutE 11 FIndex aenv Top e]

  Map _ ef a1 ->
    parenthesise (p > 10) <$>
      hang "map" <$>> [layoutEF 11 FNormal FNormal aenv Top ef
                      ,layoutAO 11 aenv a1]

  ZipWith _ ef a1 a2 ->
    parenthesise (p > 10) <$>
      hang "zipWith" <$>> [layoutEF 11 FNormal FNormal aenv Top ef
                          ,layoutAO 11 aenv a1
                          ,layoutAO 11 aenv a2]

  Fold ef (Just e0) a1 ->
    parenthesise (p > 10) <$>
      hang "fold" <$>> [layoutEF 11 FNormal FNormal aenv Top ef
                       ,layoutE 11 FNormal aenv Top e0
                       ,layoutAO 11 aenv a1]

  Fold ef Nothing a1 ->
    parenthesise (p > 10) <$>
      hang "fold1" <$>> [layoutEF 11 FNormal FNormal aenv Top ef
                        ,layoutAO 11 aenv a1]

  FoldSeg _ _ _ _ _ -> internalError "I'm lazy"

  Scan dir ef me0 a1 ->
    let name = "scan" ++ (case dir of LeftToRight -> "l"
                                      RightToLeft -> "r")
                      ++ (case me0 of Just _ -> ""
                                      Nothing -> "1")
    in parenthesise (p > 10) <$>
         hang name <$>> concat [[layoutEF 11 FNormal FNormal aenv Top ef]
                               ,case me0 of Just e0 -> [layoutE 11 FNormal aenv Top e0]
                                            Nothing -> []
                               ,[layoutAO 11 aenv a1]]

  Scan' dir ef e0 a1 ->
    let name = "scan" ++ (case dir of LeftToRight -> "l"
                                      RightToLeft -> "r")
                      ++ "'"
    in parenthesise (p > 10) <$>
         hang name <$>> [layoutEF 11 FNormal FNormal aenv Top ef
                        ,layoutE 11 FNormal aenv Top e0
                        ,layoutAO 11 aenv a1]

  Permute ef1 a1 ef2 a2 ->
    parenthesise (p > 10) <$>
      hang "permute" <$>> [layoutEF 11 FNormal FNormal aenv Top ef1
                          ,layoutAO 11 aenv a1
                          ,layoutEF 11 FIndex (FMaybe FIndex) aenv Top ef2
                          ,layoutAO 11 aenv a2]

  Backpermute _ e ef a1 ->
    parenthesise (p > 10) <$>
      hang "backpermute" <$>> [layoutE 11 FIndex aenv Top e
                              ,layoutEF 11 FIndex FIndex aenv Top ef
                              ,layoutAO 11 aenv a1]

  Stencil _ _ _ _ _ -> internalError "I'm lazy"
  Stencil2 _ _ _ _ _ _ _ _ -> internalError "I'm lazy"

  Avjp _ _ af a1 a2 ->
    parenthesise (p > 10) <$>
      hang "avjp" <$>> [layoutAF 11 aenv af
                       ,layoutAO 11 aenv a1
                       ,layoutAO 11 aenv a2]

  AcustomDeriv _ af ag a1 ->
    parenthesise (p > 10) <$>
      hang "acustomDeriv" <$>> [layoutAF 11 aenv af
                               ,layoutAF 11 aenv ag
                               ,layoutAO 11 aenv a1]

-- FIndexArg only has an effect on Nil nodes, which get printed as 'constant All' instead.
data Form = FNormal | FIndex | FIndexArg | FMaybe Form
  deriving (Show)

layoutE :: forall taenv aenv tenv env t.
           Int -> Form -> Env taenv aenv -> Env tenv env -> OpenExp env aenv t -> IdGen Layout
layoutE p form aenv env = \case
  Let lhs rhs a -> parenthesise (p > 0) <$> do
    (bindings, body) <- layoutLet aenv env form lhs rhs a
    return $ hsepvsep (Prefix "let " bindings)
                      (Prefix "in " [body])

  Evar var@(Var ty _) ->
    toForm p form (TupRsingle ty) $ \_ ->
      return (string (layoutVar "x" env var))

  Foreign _ _ _ _ -> internalError "showsAsHaskell: Foreign calls unsupported"

  pair@(Pair a1 a2) ->
    case form of
      FNormal ->
        parenthesise (p > 10) <$>
          posthang "T2" <$>> [layoutE 11 FNormal aenv env a1
                             ,layoutE 11 FNormal aenv env a2]

      FIndex -> do
        let collect :: OpenExp env aenv a -> IdGen (Maybe [Layout])
            collect Nil = return (Just [])
            collect (Pair e1 e2) =
              collect e1 >>= \case
                Nothing -> return Nothing
                Just lys -> do
                  ly <- layoutE 11 FIndexArg aenv env e2
                  return (Just (ly : lys))
            collect _ = return Nothing

        collect pair >>= \case
          Just lys ->
            return $
              parenthesise (p > 10) $
                posthang ("I" ++ show (length lys)) (reverse lys)
          Nothing ->  -- if collection fails, give up and layout as normal
            layoutE p FNormal aenv env pair

      FIndexArg -> layoutE 11 FNormal aenv env pair  -- don't know

      FMaybe form' -> case (a1, a2) of
        (Const (SingleScalarType (NumSingleType (IntegralNumType TypeWord8))) 1,
         Pair Nil value) ->
          parenthesise (p > 10) <$>
            posthang "Just_" <$>> [layoutE 11 form' aenv env value]

        (Const (SingleScalarType (NumSingleType (IntegralNumType TypeWord8))) 0,
         _) ->
          return (string "Nothing_")

        _ ->
          -- if recognition of the Maybe construction fails, give up and layout
          -- as normal
          toForm p form (expType pair) $ \p' ->
            layoutE p' FNormal aenv env pair

  Nil ->
    case form of
      FNormal -> parenthesise (p > 10) <$> return (string "constant ()")
      FIndex -> return (string "Z_")
      FIndexArg -> parenthesise (p > 10) <$> return (string "constant All")
      FMaybe _ -> internalError "showsAsHaskell: Nil doesn't make sense as a Maybe"

  VecPack _ _ -> internalError "I'm lazy"
  VecUnpack _ _ -> internalError "I'm lazy"

  expr@(IndexSlice _ a1 a2) ->
    fromIndexToForm p form (expType expr) $ \p' ->
      parenthesise (p' > 10) <$>
        hang "indexSlice" <$>> [layoutE 11 FIndex aenv env a1
                               ,layoutE 11 FIndex aenv env a2]

  expr@(IndexFull _ a1 a2) ->
    fromIndexToForm p form (expType expr) $ \p' ->
      parenthesise (p' > 10) <$>
        hang "indexFull" <$>> [layoutE 11 FIndex aenv env a1
                              ,layoutE 11 FIndex aenv env a2]

  ToIndex _ _ _ -> internalError "I'm lazy"
  FromIndex _ _ _ -> internalError "I'm lazy"
  Case _ _ _ -> internalError "I'm lazy"

  Cond e a1 a2 ->
    parenthesise (p > 10) <$>
      hang "cond" <$>> [layoutE 11 FNormal aenv env e
                       ,layoutE 11 form aenv env a1
                       ,layoutE 11 form aenv env a2]

  While a1 a2 a3 ->
    toForm p form (expType a3) $ \p' ->
      parenthesise (p' > 10) <$>
        hang "while" <$>> [layoutEF 11 FNormal FNormal aenv env a1
                          ,layoutEF 11 FNormal FNormal aenv env a2
                          ,layoutE 11 FNormal aenv env a3]

  Const ty x
    | Has <- scalarHasShow ty
    -> toForm p form (TupRsingle ty) $ \p' ->
         return $ parenthesise (p' > 0) $
           string (show x ++ " :: " ++ showExpTy (TupRsingle ty))

  expr@(PrimConst pc) ->
    toForm p form (expType expr) $ \p' -> return $
      case pc of
        PrimMinBound ty -> parenthesise (p' > 0) $ string ("minBound :: Exp " ++ show ty)
        PrimMaxBound ty -> parenthesise (p' > 0) $ string ("maxBound :: Exp " ++ show ty)
        PrimPi ty       -> parenthesise (p' > 0) $ string ("pi :: Exp" ++ show ty)

  expr@(PrimApp primfun arg) ->
    toForm p form (expType expr) $ \p' ->
      let op = PP.primOperator primfun
          name = show (PP.opName op)
      in case PP.opFixity op of
           PP.App
             | isTwoArgOp primfun ->
                 parenthesise (p' > 10) <$>
                   case arg of
                     Pair arg1 arg2 ->
                       posthang name <$>> [layoutE 11 FNormal aenv env arg1
                                          ,layoutE 11 FNormal aenv env arg2]
                     _ ->
                       posthang ("uncurry " ++ name) <$>>
                         [layoutE 11 FNormal aenv env arg]
             | otherwise ->
                 parenthesise (p' > 10) <$>
                   posthang name <$>> [layoutE 11 FNormal aenv env arg]

           PP.Infix ->
             let prec = PP.opPrecedence op
             in case arg of
                  Pair arg1 arg2 -> do
                    ly1 <- layoutE (prec+1) FNormal aenv env arg1
                    ly2 <- layoutE (prec+1) FNormal aenv env arg2
                    case (fromOneLine ly1, fromOneLine ly2) of
                      (Just s1, Just s2) ->
                        return $ parenthesise (p' > prec) $
                          string (s1 ++ " " ++ name ++ " " ++ s2)
                      _ ->
                        -- Need to re-layout arguments, now with application precedence
                        parenthesise (p' > prec) <$>
                          posthang ("(" ++ name ++ ")") <$>>
                            [layoutE 11 FNormal aenv env arg1
                            ,layoutE 11 FNormal aenv env arg2]
                  _ ->
                    parenthesise (p' > 10) <$>
                      posthang ("uncurry (" ++ name ++ ")") <$>>
                        [layoutE 11 FNormal aenv env arg]

           PP.Prefix -> do
             ly <- layoutE 11 FNormal aenv env arg
             case fromOneLine ly of
               Just s ->
                 return $ parenthesise (p' > 10) $ string (name ++ s)
               Nothing ->
                 return $ parenthesise (p' > 10) $
                   posthang ("(" ++ name ++ ")") [ly]

  expr@(Index avar arg) ->
    toForm p form (expType expr) $ \p' -> do
      let prec = 9
      ly <- layoutE prec FIndex aenv env arg
      case fromOneLine ly of
        Just s ->
          return $ parenthesise (p' > prec) $
            string (layoutVar "a" aenv avar ++ " ! " ++ s)
        Nothing ->
          -- Need to re-layout RHS, now with application precedence
          parenthesise (p' > 10) <$>
            posthang "(!)" <$>> [return (string (layoutVar "a" aenv avar))
                                ,layoutE 11 FNormal aenv env arg]

  expr@(LinearIndex avar arg) ->
    toForm p form (expType expr) $ \p' -> do
      let prec = 9
      ly <- layoutE prec FNormal aenv env arg
      case fromOneLine ly of
        Just s ->
          return $ parenthesise (p' > prec) $
            string (layoutVar "a" aenv avar ++ " !! " ++ s)
        Nothing ->
          -- Need to re-layout RHS, now with application precedence
          parenthesise (p' > 10) <$>
            posthang "(!!)" <$>> [return (string (layoutVar "a" aenv avar))
                                 ,layoutE prec FNormal aenv env arg]

  expr@(Shape avar) ->
    fromIndexToForm p form (expType expr) $ \p' ->
      return $ parenthesise (p' > 10) $
        hang "shape" [string (layoutVar "a" aenv avar)]

  expr@(ShapeSize _ arg) ->
    toForm p form (expType expr) $ \p' ->
      parenthesise (p' > 10) <$>
        hang "shapeSize" <$>> [layoutE 11 FNormal aenv env arg]

  Evjp ty _ a1 a2 a3 ->
    toForm p form ty $ \p' ->
      parenthesise (p' > 10) <$>
        hang "evjp" <$>> [layoutEF 11 FNormal FNormal aenv env a1
                         ,layoutE 11 FNormal aenv env a2
                         ,layoutE 11 FNormal aenv env a3]

  EcustomDeriv ty a1 a2 a3 ->
    toForm p form ty $ \p' ->
      parenthesise (p' > 10) <$>
        hang "ecustomDeriv" <$>> [layoutEF 11 FNormal FNormal aenv env a1
                                 ,layoutEF 11 FNormal FNormal aenv env a2
                                 ,layoutE 11 FNormal aenv env a3]

  Undef ty ->
    toForm p form (TupRsingle ty) $ \p' ->
      return $ parenthesise (p' > 0) $
        string ("undef :: " ++ showExpTy (TupRsingle ty))

  Coerce _ _ _ -> internalError "I'm lazy"

fromIndexToForm :: Int -> Form -> TypeR a -> (Int -> IdGen Layout) -> IdGen Layout
fromIndexToForm p FIndex _ layoutf = layoutf p
fromIndexToForm p form ty layoutf =
  case collectIndexWidth ty of
    Nothing -> toForm p form ty layoutf
    Just n -> do
      names <- replicateM n genNameE
      let tupstr c = c : show n ++ concatMap (' ' :) names
      layout <- layoutf 0
      toForm p form ty $ \p' ->
        return $ parenthesise (p' > 0) $
          hsepvsep (Prefix "let " [hang (tupstr 'I' ++ " =") [layout]])
                   (string ("in " ++ nestedPairs 0 (\p2 -> showParen (p2 > 10) (showString "constant ()") "") names ""))

-- Takes layout for expression with given type in FNormal, produces layout
-- for the same expression in the given form.
toForm :: Int -> Form -> TypeR a -> (Int -> IdGen Layout) -> IdGen Layout
toForm p FNormal _ layoutf = layoutf p
toForm p FIndex ty layoutf =
  case collectIndexWidth ty of
    Nothing -> layoutf p  -- type doesn't look like an index, give up
    Just n -> do
      names <- replicateM n genNameE
      let tupstr c = c : show n ++ concatMap (' ' :) names
      layout <- layoutf 0
      return $ parenthesise (p > 0) $
        hsepvsep (Prefix "let " [hang (nestedPairs 0 (const "_") names " =") [layout]])
                 (string ("in " ++ tupstr 'I'))
toForm p FIndexArg ty layoutf = toForm p FNormal ty layoutf
toForm _ (FMaybe _) _ layoutf =
  internalError ("I'm lazy: " ++ show (evalIdGen (layoutf 11)))

nestedPairs :: Int -> (Int -> String) -> [String] -> ShowS
nestedPairs topp nilcore topnames = go topp (reverse topnames)
  where
    go :: Int -> [String] -> ShowS
    go p [] = showString (nilcore p)
    go p (v:vs) = 
      showParen (p > 10) $
        showString "T2 " . go 11 vs . showString (' ' : v)

collectIndexWidth :: TypeR a -> Maybe Int
collectIndexWidth TupRunit = Just 0
collectIndexWidth (TupRpair t1 _) = succ <$> collectIndexWidth t1
collectIndexWidth _ = Nothing

showExpTy :: TypeR t -> String
showExpTy ty =
  let s = show ty
  in if ' ' `elem` s && take 1 s /= "("
         then "Exp (" ++ s ++ ")"
         else "Exp " ++ s

layoutEF :: Int -> Form -> Form -> Env taenv aenv -> Env tenv env -> OpenFun env aenv t -> IdGen Layout
layoutEF p _ formOut aenv env (Body a) = layoutE p formOut aenv env a
layoutEF p formIn formOut aenv env fun@Lam{} = do
  (argsString, body) <- go aenv env fun
  return (parenthesise (p > 0) $
            hang ("\\" ++ intercalate " " argsString ++ " ->") [body])
  where
    go :: Env taenv aenv -> Env tenv env -> OpenFun env aenv t -> IdGen ([String], Layout)
    go aenv' env' (Body a) = ([],) <$> layoutE 0 formOut aenv' env' a
    go aenv' env' (Lam lhs fun') = do
      (env'', lhsString) <- case formIn of
        FNormal   -> layoutLHS 11 IdTypeE env' lhs
        FIndexArg -> layoutLHS 11 IdTypeE env' lhs
        FIndex -> layoutLHSIndex 11 IdTypeE env' lhs
        FMaybe _ -> internalError "showsAsHaskell: Maybe arguments unsupported"
      (rest, body) <- go aenv' env'' fun'
      return (lhsString "" : rest, body)

layoutAlet :: Env taenv aenv1
           -> ALeftHandSide bnd aenv1 aenv2
           -> OpenAcc aenv1 t1
           -> OpenAcc aenv2 t2
           -> IdGen ([Layout], Layout)
layoutAlet aenv lhs rhs a = do
  (aenv', lhsString) <- layoutLHS 0 IdTypeA aenv lhs
  l2 <- layoutAO 0 aenv rhs
  let binding = hang (lhsString " =") [l2]
  case a of
    OpenAcc (Alet lhs' rhs' a') -> do
      (bindings, body) <- layoutAlet aenv' lhs' rhs' a'
      return (binding : bindings, body)
    _ -> do
      body <- layoutAO 0 aenv' a
      return ([binding], body)

layoutLet :: Env taenv aenv
          -> Env tenv env1
          -> Form
          -> ELeftHandSide bnd env1 env2
          -> OpenExp env1 aenv t1
          -> OpenExp env2 aenv t2
          -> IdGen ([Layout], Layout)
layoutLet aenv env form lhs rhs a = do
  (env', lhsString) <- layoutLHS 0 IdTypeE env lhs
  l2 <- layoutE 0 FNormal aenv env rhs
  let binding = hang (lhsString " =") [l2]
  case a of
    Let lhs' rhs' a' -> do
      (bindings, body) <- layoutLet aenv env' form lhs' rhs' a'
      return (binding : bindings, body)
    _ -> do
      body <- layoutE 0 form aenv env' a
      return ([binding], body)

layoutLHS :: Int -> IdType -> Env tenv env -> LeftHandSide s t env env' -> IdGen (Env tenv env', ShowS)
layoutLHS p idType env = \case
  LeftHandSideWildcard _ -> return (env, showString "_")
  LeftHandSideSingle _ -> do
    name <- genName idType
    return (Push env name, showString name)
  LeftHandSidePair lhs1 lhs2 -> do
    (env1, s1) <- layoutLHS 11 idType env lhs1
    (env2, s2) <- layoutLHS 11 idType env1 lhs2
    return (env2, showParen (p > 10) $ showString "T2 " . s1 . showString " " . s2)

-- If recognition of an index-like LHS fails, a normal LHS is layouted.
layoutLHSIndex :: (forall t'. Show (s t')) => Int -> IdType -> Env tenv env -> LeftHandSide s t env env' -> IdGen (Env tenv env', ShowS)
layoutLHSIndex p idType = \env lhs ->
  collect env lhs >>= \case
    Nothing -> fmap (fmap (showString ("{- @@@ " ++ showLHS lhs ++ " -}") .)) $ layoutLHS p idType env lhs
    Just (env', []) -> do
      return (env', showString "Z_")
    Just (env', names) -> do
      let res = showParen (p > 10) $ showString $
                  "I" ++ show (length names) ++ " " ++
                  intercalate " " (reverse names)
      return (env', res)
  where
    -- Returns names in the I[n] binder in reverse order (in the snoc list order).
    collect :: Env tenv env -> LeftHandSide s t env env' -> IdGen (Maybe (Env tenv env', [String]))
    collect env (LeftHandSideWildcard TupRunit) = return (Just (env, []))
    collect env (LeftHandSideWildcard (TupRpair ty _)) =  -- if a non-trivial prefix of the dimensions is ignored, still generate a nice I<n> pattern
      fmap (fmap ("_" :)) <$> collect env (LeftHandSideWildcard ty)
    collect env (LeftHandSidePair lhs1 (LeftHandSideWildcard _)) =
      fmap (fmap ("_" :)) <$> collect env lhs1
    collect env (LeftHandSidePair lhs1 (LeftHandSideSingle _)) =
      collect env lhs1 >>= \case
        Nothing -> return Nothing
        Just (env', names) -> do
          name <- genName idType
          return (Just (Push env' name, name : names))
    collect _ _ = return Nothing

    showLHS :: (forall t'. Show (s t')) => LeftHandSide s t env env' -> String
    showLHS (LeftHandSideWildcard ty) = "W[" ++ showTupR show ty ++ "]"
    showLHS (LeftHandSideSingle ty) = show ty
    showLHS (LeftHandSidePair lhs1 lhs2) = "(" ++ showLHS lhs1 ++ "," ++ showLHS lhs2 ++ ")"

layoutVar :: String -> Env tenv env -> Var s env t -> String
layoutVar prefix env (Var _ idx) =
  case prj env idx of
    Left idx' -> prefix ++ "UP_" ++ show (idxToInt idx' + 1)
    Right name -> name


-- Variable environments used in layouting
-- ---------------------------------------

type Env = OpenTagEnv String

data OpenTagEnv t tenv env where
  Top :: OpenTagEnv t tenv tenv
  Push :: OpenTagEnv t tenv env -> t -> OpenTagEnv t tenv (env, a)

deriving instance Show t => Show (OpenTagEnv t tenv env)

prj :: OpenTagEnv t tenv env -> Idx env a -> Either (Idx tenv a) t
prj Top i = Left i
prj (Push _ x) ZeroIdx = Right x
prj (Push env _) (SuccIdx i) = prj env i


-- ID and name generation
-- ----------------------

newtype IdGen a = IdGen (State (Int, Int) a)
  deriving (Functor, Applicative, Monad, MonadState (Int, Int))

evalIdGen :: IdGen a -> a
evalIdGen (IdGen s) = evalState s (1, 1)

genIdA :: IdGen Int
genIdA = IdGen (state (\(sA, sE) -> (sA, (sA + 1, sE))))

genIdE :: IdGen Int
genIdE = IdGen (state (\(sA, sE) -> (sE, (sA, sE + 1))))

genNameA :: IdGen String
genNameA = ('a' :) . show <$> genIdA

genNameE :: IdGen String
genNameE = ('x' :) . show <$> genIdE

data IdType = IdTypeA | IdTypeE
  deriving (Show)

genName :: IdType -> IdGen String
genName IdTypeA = genNameA
genName IdTypeE = genNameE


-- Utility functions
-- -----------------

infixl 5 <$>>
(<$>>) :: (Applicative f, Traversable t) => (t a -> b) -> t (f a) -> f b
f <$>> l = f <$> sequenceA l

showTupR :: (forall t'. s t' -> String) -> TupR s t -> String
showTupR _ TupRunit       = "()"
showTupR s (TupRsingle t) = s t
showTupR s (TupRpair a b) = "(" ++ showTupR s a ++ "," ++ showTupR s b ++")"

data Has c a where
  Has :: c a => Has c a

tupHasShow :: (forall t'. s t' -> Has Show t') -> TupR s t -> Has Show t
tupHasShow _ TupRunit = Has
tupHasShow f (TupRsingle t) = f t
tupHasShow f (TupRpair t1 t2)
  | Has <- tupHasShow f t1
  , Has <- tupHasShow f t2
  = Has

scalarHasShow :: ScalarType t -> Has Show t
scalarHasShow (SingleScalarType (NumSingleType t)) = goN t
  where
    goN :: NumType t -> Has Show t
    goN (IntegralNumType a) = goI a
    goN (FloatingNumType a) = goF a

    goI :: IntegralType t -> Has Show t
    goI TypeInt = Has
    goI TypeInt8 = Has
    goI TypeInt16 = Has
    goI TypeInt32 = Has
    goI TypeInt64 = Has
    goI TypeWord = Has
    goI TypeWord8 = Has
    goI TypeWord16 = Has
    goI TypeWord32 = Has
    goI TypeWord64 = Has

    goF :: FloatingType t -> Has Show t
    goF TypeHalf = Has
    goF TypeFloat = Has
    goF TypeDouble = Has
scalarHasShow (VectorScalarType _) =
  internalError "showsAsHaskell: Can't handle vector types"

isTwoArgOp :: PrimFun a -> Bool
isTwoArgOp PrimAdd{}                = True
isTwoArgOp PrimSub{}                = True
isTwoArgOp PrimMul{}                = True
isTwoArgOp PrimNeg{}                = True
isTwoArgOp PrimAbs{}                = False
isTwoArgOp PrimSig{}                = False
isTwoArgOp PrimQuot{}               = True
isTwoArgOp PrimRem{}                = True
isTwoArgOp PrimQuotRem{}            = True
isTwoArgOp PrimIDiv{}               = True
isTwoArgOp PrimMod{}                = True
isTwoArgOp PrimDivMod{}             = True
isTwoArgOp PrimBAnd{}               = True
isTwoArgOp PrimBOr{}                = True
isTwoArgOp PrimBXor{}               = True
isTwoArgOp PrimBNot{}               = False
isTwoArgOp PrimBShiftL{}            = True
isTwoArgOp PrimBShiftR{}            = True
isTwoArgOp PrimBRotateL{}           = True
isTwoArgOp PrimBRotateR{}           = True
isTwoArgOp PrimPopCount{}           = False
isTwoArgOp PrimCountLeadingZeros{}  = False
isTwoArgOp PrimCountTrailingZeros{} = False
isTwoArgOp PrimFDiv{}               = True
isTwoArgOp PrimRecip{}              = False
isTwoArgOp PrimSin{}                = False
isTwoArgOp PrimCos{}                = False
isTwoArgOp PrimTan{}                = False
isTwoArgOp PrimAsin{}               = False
isTwoArgOp PrimAcos{}               = False
isTwoArgOp PrimAtan{}               = False
isTwoArgOp PrimSinh{}               = False
isTwoArgOp PrimCosh{}               = False
isTwoArgOp PrimTanh{}               = False
isTwoArgOp PrimAsinh{}              = False
isTwoArgOp PrimAcosh{}              = False
isTwoArgOp PrimAtanh{}              = False
isTwoArgOp PrimExpFloating{}        = False
isTwoArgOp PrimSqrt{}               = False
isTwoArgOp PrimLog{}                = False
isTwoArgOp PrimFPow{}               = True
isTwoArgOp PrimLogBase{}            = True
isTwoArgOp PrimTruncate{}           = False
isTwoArgOp PrimRound{}              = False
isTwoArgOp PrimFloor{}              = False
isTwoArgOp PrimCeiling{}            = False
isTwoArgOp PrimAtan2{}              = True
isTwoArgOp PrimIsNaN{}              = False
isTwoArgOp PrimIsInfinite{}         = False
isTwoArgOp PrimLt{}                 = True
isTwoArgOp PrimGt{}                 = True
isTwoArgOp PrimLtEq{}               = True
isTwoArgOp PrimGtEq{}               = True
isTwoArgOp PrimEq{}                 = True
isTwoArgOp PrimNEq{}                = True
isTwoArgOp PrimMax{}                = True
isTwoArgOp PrimMin{}                = True
isTwoArgOp PrimLAnd                 = True
isTwoArgOp PrimLOr                  = True
isTwoArgOp PrimLNot                 = False
isTwoArgOp PrimFromIntegral{}       = False
isTwoArgOp PrimToFloating{}         = False
