{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE UndecidableInstances       #-}

module AlgebraCheckers.Tools where

import Data.Group
import GHC.Generics
import Test.QuickCheck
import Test.QuickCheck.Checkers

newtype WithSemigroup a = WithSemigroup a
  deriving stock (Eq, Show, Generic)
  deriving newtype (Arbitrary, CoArbitrary, EqProp)

instance Semigroup (WithSemigroup a) where
  (<>) = undefined

instance Model a b => Model (WithSemigroup a) b where
  model (WithSemigroup a) = model a

newtype WithMonoid a = WithMonoid a
  deriving stock (Eq, Show, Generic)
  deriving newtype (Arbitrary, CoArbitrary, EqProp)
  deriving Semigroup via (WithSemigroup a)

instance Monoid (WithMonoid a) where
  mempty = undefined

instance Model a b => Model (WithMonoid a) b where
  model (WithMonoid a) = model a

newtype WithGroup a = WithGroup a
  deriving stock (Eq, Show, Generic)
  deriving newtype (Arbitrary, CoArbitrary, EqProp)
  deriving Semigroup via (WithSemigroup a)
  deriving Monoid via (WithMonoid a)

instance Group (WithGroup a) where
  invert = undefined

instance Model a b => Model (WithGroup a) b where
  model (WithGroup a) = model a

newtype WithOrd a = WithOrd a
  deriving stock (Eq, Show, Generic)
  deriving newtype (Arbitrary, CoArbitrary, EqProp)

instance Eq a => Ord (WithOrd a) where
  compare = undefined

instance Model a b => Model (WithOrd a) b where
  model (WithOrd a) = model a

data Undecided = Undecided
  deriving stock (Eq, Ord, Show, Read, Generic)
  deriving anyclass EqProp

instance Function a => Function (ModeledBy a)

instance Model Undecided Undecided where
  model = id
instance Arbitrary Undecided where
  arbitrary = pure Undecided
instance CoArbitrary Undecided where
  coarbitrary _ = id


newtype ModeledBy a = ModeledBy
  { modeledBy :: a
  } deriving newtype (Eq, Ord, Enum, Bounded, Read, Semigroup, Monoid, Group)
    deriving stock Generic

instance Show a => Show (ModeledBy a) where
  show (ModeledBy a) = show a

instance Arbitrary a => Arbitrary (ModeledBy a) where
  arbitrary = fmap ModeledBy arbitrary
  shrink = fmap ModeledBy . shrink . modeledBy

instance EqProp a => EqProp (ModeledBy a)

instance Model (ModeledBy a) a where
  model = modeledBy

instance CoArbitrary a => CoArbitrary (ModeledBy a) where
  coarbitrary (ModeledBy a) = coarbitrary a

instance {-# OVERLAPPING #-} Show (ModeledBy (a -> b)) where
  show _ = "<fun>"

