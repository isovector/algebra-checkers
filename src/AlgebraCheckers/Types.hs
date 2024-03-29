{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}

module AlgebraCheckers.Types where

import Data.Data
import AlgebraCheckers.Unification
import Language.Haskell.TH

data Law a = Law
  { lawData :: a
  , lawLhsExp :: Exp
  , lawRhsExp :: Exp
  }
  deriving (Ord, Show, Data, Typeable)

instance Eq a => Eq (Law a) where
  Law _ a a' == Law _ b b' =
    and
      [ equalUpToAlpha a b && equalUpToAlpha a' b'
      ]

data LawSort
  = LawName String
  | LawNotDodgy
  deriving (Eq, Ord, Show)

type NamedLaw = Law LawSort
type Theorem  = Law TheoremSource

data Arity = Binary | Prefix Int
  deriving (Eq, Ord, Show)

data TheoremProblem
  = Dodgy DodgyReason
  | Contradiction ContradictionReason
  deriving (Eq, Ord, Show)

isContradiction :: TheoremProblem -> Bool
isContradiction Contradiction{} = True
isContradiction _               = False

isDodgy :: TheoremProblem -> Bool
isDodgy Dodgy{} = True
isDodgy _       = False

data ContradictionReason
  = UnboundMatchableVars [Name]
  | UnequalValues
  | UnknownConstructors [Name]
  deriving (Eq, Ord, Show)

data DodgyReason
  = SelfRecursive
  deriving (Eq, Ord, Show)

data TheoremSource
  = LawDefn String
  | Interaction String String
  deriving (Eq, Ord, Show)

