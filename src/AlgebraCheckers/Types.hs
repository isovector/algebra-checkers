{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE UndecidableInstances #-}

module AlgebraCheckers.Types where

import Data.Data
import AlgebraCheckers.Unification
import Language.Haskell.TH

import Test.QuickCheck (Property)
import Test.QuickCheck.Checkers (EqProp (..))

class EqProp2 a where
  eq2 :: a -> a -> WrappedProperty a

instance EqProp a => EqProp2 a where
  eq2 a b = WrappedProperty $ a =-= b

newtype WrappedProperty a = WrappedProperty Property

data Law a = Law
  { lawData :: a
  , lawLhsExp :: Exp
  , lawRhsExp :: Exp
  }
  deriving (Ord, Show, Data, Typeable)

modifyLawData :: (a -> b) -> Law a -> Law b
modifyLawData f (Law a l r) = Law (f a) l r

instance Eq a => Eq (Law a) where
  Law _ a a' == Law _ b b' =
    and
      [ equalUpToAlpha a b && equalUpToAlpha a' b'
      ]

type Theorem  = Law TheoremSource
type CheckedTheorem = Law (TheoremSource, Maybe ContradictionReason)

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
  deriving (Eq, Ord, Show, Typeable, Data)

pattern (:->) :: Type -> Type -> Type
pattern t :-> ts <- AppT (AppT ArrowT t) ts
  where
    t :-> ts = AppT (AppT ArrowT t) ts

infixr 0 :->

