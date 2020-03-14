{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}

module Test.QuickCheck.Checkers.Algebra.Types where

import Data.Data
import Test.QuickCheck.Checkers.Algebra.Unification
import Language.Haskell.TH

data Law a = Law
  { lawData :: a
  , lawLhsExp :: Exp
  , lawRhsExp :: Exp
  }
  deriving (Ord, Show, Data, Typeable)

instance Eq a => Eq (Law a) where
  Law d a a' == Law d' b b' =
    and
      [ equalUpToAlpha a b && equalUpToAlpha a' b'
      , d == d'
      ]

type NamedLaw = Law String
type Theorem  = Law TheoremSource

data Arity = Binary | Prefix Int
  deriving (Eq, Ord, Show)

data ContradictionReason
  = UnboundMatchableVars [Name]
  | UnequalValues
  | UnknownConstructors [Name]
  deriving (Eq, Ord, Show)

data TheoremSource
  = LawDefn String
  | Interaction String String
  deriving (Eq, Ord, Show)

