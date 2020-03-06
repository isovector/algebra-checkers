{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}

module Test.QuickCheck.Checkers.Algebra.TH where

import qualified Control.Monad.Trans as T
import           Control.Monad.Trans.State
import           Data.Char
import           Data.Data (Data)
import           Data.Dynamic
import           Data.Generics.Aliases
import           Data.Generics.Schemes
import           Data.List (nub)
import qualified Data.Map as M
import           Data.Maybe
import           Data.Traversable
import           Language.Haskell.TH
import           Language.Haskell.TH.Orphans ()
import           Language.Haskell.TH.Syntax
import           Test.QuickCheck
import           Test.QuickCheck.Checkers.Algebra.Types



biasedGenerate :: [a] -> Gen a -> Gen a
biasedGenerate [] gena = gena
biasedGenerate as gena =
  frequency
    [ (1, elements as)
    , (1, gena)
    ]


getDyns :: (Typeable a, Monad m) => StateT [Dynamic] m [a]
getDyns = fmap (mapMaybe fromDynamic) get


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

mkMap :: [Name] -> [a] -> (a -> b) -> M.Map Name b
mkMap vars as f = M.fromList . zip vars $ fmap f as


law :: ExpQ -> ExpQ
law = (lawImpl =<<)


lawImpl :: Exp -> ExpQ
lawImpl (InfixE (Just exp1) (VarE eq) (Just exp2)) | eq == '(==) = do
  let vars = nub $ unboundVars exp1 ++ unboundVars exp2

  names <- for vars $ newName . nameBase
  z <-
    fmap (foldMap getBinds) $ for names $ \name ->
      [e|
        do
          $(varP name) <- T.lift . flip biasedGenerate arbitrary =<< getDyns
          pure ()
          |]
  let mapping = mkMap vars names VarE
      printArgs = listE $ flip fmap names $ \name -> [e|show $(varE name)|]
      printExpr
        = lift
        . pprint
        . deModuleName
        . rebindVars
          ( mkMap vars [1..] $
              UnboundVarE . mkName . ('%':) . show @Int
          )

  save <- [e|
    modify ($(listE $ fmap (appE [e|toDyn|] . varE) names) ++)
    |]

  res <- [e|
    pure
    ( LawHand
        (printf $(printExpr exp1) $(printArgs))
        $(pure $ rebindVars mapping exp1)

    , LawHand
        (printf $(printExpr exp2) $(printArgs))
        $(pure $ rebindVars mapping exp2)
    )|]
  [e|
    Law $(lift $ length vars)
        $(pure $ DoE $ z ++ fmap NoBindS [ save, res ])
        $(lift exp1)
        $(lift exp2)
    |]
lawImpl _ =
  error "lawImpl must be called with an expression of the form [e| foo a b c == bar a d e |]"

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

