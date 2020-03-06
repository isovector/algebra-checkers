{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PackageImports        #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module Ok where

import Control.Monad.Trans.State
import Data.Char
import Data.Traversable
import Control.Arrow
import Data.Function
import Debug.Trace
import Control.Monad
import Data.Monoid
import Test.QuickCheck.Checkers
import Test.QuickCheck.Classes
import Test.QuickCheck
import Data.List (nub)
import qualified Data.Set as S
import Data.Word
import "template-haskell" Language.Haskell.TH
import Data.Generics.Schemes
import Data.Generics.Aliases
import qualified Data.Map as M
import "template-haskell" Language.Haskell.TH.Syntax
import Data.Data
import Data.Dynamic
import Data.Maybe
import qualified Control.Monad.Trans as T


data LawHand a = LawHand
  { lhDescriptor :: String
  , lhValue :: a
  } deriving Functor


newtype Law a = Law
  { runLaw :: StateT [Dynamic] Gen (LawHand a, LawHand a)
  } deriving Functor

biasedGenerate :: [a] -> Gen a -> Gen a
biasedGenerate [] gena = gena
biasedGenerate as gena =
  frequency
    [ (1, elements as)
    , (1, gena)
    ]

getDyns :: (Typeable a, Monad m) => StateT [Dynamic] m [a]
getDyns = fmap (mapMaybe fromDynamic) get

-- mapLaw
--     :: (Typeable a, Typeable b)
--     => (a -> b)
--     -> Law a
--     -> Law b
-- mapLaw f (Law a) = Law (fmap (fmap (mapLawHand f *** mapLawHand f)) a)


deModuleName :: Data a => a -> a
deModuleName = everywhere $ mkT $ \case
  n -> mkName $ nameBase n


getBinds :: Exp -> [Stmt]
getBinds = everything (++) $
  mkQ [] $ \case
    x@BindS{} -> [x]
    _ -> []


unboundVars :: Exp -> [Name]
unboundVars = everything (++) $
  mkQ [] $ \case
    UnboundVarE n -> [n]
    _ -> []


rebindVars :: M.Map Name Exp -> Exp -> Exp
rebindVars m = everywhere $ mkT $ \case
  UnboundVarE n -> m M.! n
  t -> t


law2 :: ExpQ -> ExpQ
law2 = (law =<<)


law :: Exp -> ExpQ
law (InfixE (Just exp1) (VarE eq) (Just exp2)) | eq == '(==) = do
  let vars = nub $ unboundVars exp1 ++ unboundVars exp2

  names <- for vars $ newName . nameBase
  z <-
    fmap (foldMap getBinds) $ for names $ \name ->
      [e| do $(varP name) <- T.lift . flip biasedGenerate arbitrary =<< getDyns; pure () |]
  let mapping = M.fromList $ zip vars $ fmap VarE names
      printfd = M.fromList $ zip vars $ fmap (UnboundVarE . mkName . ('%':) . show) [1..]
      printfargs = listE $ flip fmap names $ \name -> [e|show $(varE name)|]
      printfit = lift . pprint . deModuleName . rebindVars printfd

  save <- [e|
    modify ($(listE $ fmap (appE [e|toDyn|] . varE) names) ++)
    |]

  res <- [e|
    pure
    ( LawHand
        (printf $(printfit exp1) $(printfargs))
        $(pure $ rebindVars mapping exp1)

    , LawHand
        (printf $(printfit exp2) $(printfargs))
        $(pure $ rebindVars mapping exp2)
    )|]
  [e| Law $ $(pure $ DoE $ z ++ fmap NoBindS [ save, res ]) |]


------------------------------------------------------------------------------
-- | A bare-boned implementation of printf. This function will replace tokens
-- of the form @"%n"@ in the first string with @args !! n@.
--
-- This will only work for indexes up to 9.
--
-- For example:
--
-- >>> printf "hello %1 %2% %3 %1" ["world", "50"]
-- "hello world 50% %3 world"
printf :: String -> [String] -> String
printf str args = splitArgs str
  where
    splitArgs :: String -> String
    splitArgs s =
      case break (== '%') s of
        (as, "") -> as
        (as, _ : b : bs)
          | isDigit b
          , let d = read [b] - 1
          , d < length args
            -> as ++ (args !! d) ++ splitArgs bs
        (as, _ : bs) ->  as ++ "%" ++ splitArgs bs

