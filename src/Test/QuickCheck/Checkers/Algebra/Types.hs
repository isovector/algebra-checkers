{-# LANGUAGE DeriveFunctor #-}

module Test.QuickCheck.Checkers.Algebra.Types where

import Control.Monad.Trans.State
import Data.Dynamic
import Language.Haskell.TH
import Test.QuickCheck

data Law' = Law'
  { lawName :: String
  , law'LhsExp :: Exp
  , law'RhsExp :: Exp
  }
  deriving (Eq, Ord, Show)

data LawHand a = LawHand
  { lhDescriptor :: String
  , lhValue :: a
  } deriving Functor


data Law a = Law
  { lawParams :: Int
  , runLaw :: StateT [Dynamic] Gen (LawHand a, LawHand a)
  , lawLhsExp :: Exp
  , lawRhsExp :: Exp
  } deriving Functor

