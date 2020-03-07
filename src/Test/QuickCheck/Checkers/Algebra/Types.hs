{-# LANGUAGE DeriveFunctor #-}

module Test.QuickCheck.Checkers.Algebra.Types where

import Language.Haskell.TH

data Law = Law
  { lawName :: String
  , lawLhsExp :: Exp
  , lawRhsExp :: Exp
  }
  deriving (Eq, Ord, Show)

data SubExp = SubExp
  { seExp  :: Exp
  , seSubId :: Int
  } deriving (Eq, Ord, Show)

