{-# LANGUAGE LambdaCase #-}

module App where

import           App.Parser
import           App.Sections
import           App.Types
import           Data.Foldable
import qualified Data.Map as M


buildStuffMap :: [Decl a] -> StuffMap a
buildStuffMap = foldMap $ \case
  LawD       t
    -> StuffMap mempty [t] mempty mempty mempty mempty mempty
  FunModelD  t
    -> StuffMap mempty mempty [t] mempty mempty mempty mempty
  TypeModelD (t@(TypeModel n _ _))
    -> StuffMap mempty mempty mempty (M.singleton n t) mempty mempty mempty
  d@(TypeSigD t)
    -> StuffMap mempty mempty mempty mempty [d] [t] mempty
  EmptyTypeD n
    -> StuffMap mempty mempty mempty mempty mempty mempty [n]
  t -> StuffMap mempty mempty mempty mempty [t] mempty mempty


addImport :: a -> StuffMap a -> StuffMap a
addImport im sm =
  let (header, rest) = span (not . isOpening) $ smOther sm
   in sm { smOther = mconcat [ header, [Opening, Import im], drop 1 rest ] }


addHeader :: a -> StuffMap a -> StuffMap a
addHeader a sm =
  sm { smHeader = a : smHeader sm }


isOpening :: Decl a -> Bool
isOpening Opening = True
isOpening _       = False


app :: [Decl String] -> String
app
  = dumpStuffMap
  . addHeader "{-# LANGUAGE TemplateHaskell #-}"
  . addHeader "{-# LANGUAGE DeriveGeneric #-}"
  . addHeader "{-# LANGUAGE TypeFamilies #-}"
  . addHeader "{-# OPTIONS_GHC -fno-warn-unused-imports #-}"
  . addImport "Test.QuickCheck"
  . addImport "Test.QuickCheck.Checkers (Model (..), EqProp (..))"
  . addImport "GHC.Generics (Generic)"
  . addImport "AlgebraCheckers (theoremsOf, law)"
  . addImport "AlgebraCheckers.Tools (ModeledBy)"
  . addImport "AlgebraCheckers.Modeling (modelsFor, unmodel)"
  . buildStuffMap


main :: IO ()
main
  = traverse_ (putStrLn . app)
  . parseAndSubst
    =<< readFile "/home/sandy/prj/algebra-checkers/test/App.hs"

