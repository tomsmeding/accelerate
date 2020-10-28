{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-| Configuration provider for the AD transformation. The used source is environment variables. -}
module Data.Array.Accelerate.Trafo.AD.Config (
  ConfigVar(..),
  getConfigVar
) where

import qualified Data.Dependent.Map as DMap
import Data.Dependent.Map (DMap)
import Data.Dependent.Sum (DSum(..))
import Data.Functor.Identity (Identity(..))
import Data.GADT.Compare (GEq(..), GCompare(..), GOrdering(..))
import Data.Maybe (catMaybes)
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(Refl))
import Text.Read (readMaybe)
import System.Environment (getEnvironment)
import System.IO.Unsafe (unsafePerformIO)


-- DECLARATION OF THE CONFIG VARIABLES
-- -----------------------------------

data ConfigVar a where
  SmallFunSize :: ConfigVar Int

instance GEq ConfigVar where
  geq SmallFunSize SmallFunSize = Just Refl

instance GCompare ConfigVar where
  gcompare SmallFunSize SmallFunSize = GEQ

parseVar :: String -> Maybe SomeConfigVar
parseVar "SMALLFUNSIZE" = Just (SomeConfigVar SmallFunSize)
parseVar _ = Nothing

varDescr :: ConfigVar a -> String
varDescr SmallFunSize = "small expression function size bound"

defaultValue :: ConfigVar a -> a
defaultValue SmallFunSize = 20

configVarPrefix :: String
configVarPrefix = "ACCELERATE_AD_"


-- IMPLEMENTATION MACHINERY
-- ------------------------

-- | The @ConfigVarType a@ context is irrelevant for users of this function;
-- passing it a concrete 'ConfigVar' value will always work.
getConfigVar :: ConfigVarType a => ConfigVar a -> a
getConfigVar var
  | Just (Identity value) <- DMap.lookup var parsedEnvironment = value
  | otherwise = defaultValue var

data SomeConfigVar = forall a. ConfigVarType a => SomeConfigVar (ConfigVar a)

class Show a => ConfigVarType a where
  parseType :: String -> Maybe a
  typeDescr :: Proxy a -> String

instance ConfigVarType Int where
  parseType = readMaybe
  typeDescr _ = "integer"

parse :: forall a. ConfigVarType a => String -> ConfigVar a -> String -> Either String a
parse origkey var value
  | Just res <- parseType value = Right res
  | otherwise =
      Left $ "Cannot parse the environment variable " ++ origkey ++ ", the " ++
               varDescr var ++ ", as an " ++ typeDescr (Proxy @a) ++
               " (it has been given the value '" ++ value ++ "')."

data ParsedEnvVar = forall a. ConfigVarType a => ParsedEnvVar (ConfigVar a) a

parseEnvVar :: String -> String -> String -> Either String ParsedEnvVar
parseEnvVar key origkey = case parseVar key of
  Just (SomeConfigVar var) -> fmap (ParsedEnvVar var) . parse origkey var
  _ -> const . Left $ "Unrecognised environment variable '" ++ origkey ++ "'"

parsedEnvironment :: DMap ConfigVar Identity
parsedEnvironment =
  DMap.fromList $ catMaybes
    [case parseEnvVar key' key value of
       Right (ParsedEnvVar var value') ->
         let diagnostic = unsafePerformIO $ putStrLn $ "Accelerate AD config: " ++ varDescr var ++ " = " ++ show value'
         in Just (var :=> Identity (diagnostic `seq` value'))
       Left err -> unsafePerformIO (putStrLn $ "Accelerate: " ++ err)
                      `seq` Nothing
    | (key, value) <- unsafePerformIO getEnvironment
    , take (length configVarPrefix) key == configVarPrefix
    , let key' = drop (length configVarPrefix) key]
