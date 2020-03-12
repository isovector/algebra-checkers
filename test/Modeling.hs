{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Modeling where

import Data.Functor.Compose
import Data.Typeable
import Data.Function
import Test.QuickCheck
import Test.QuickCheck.Checkers.Algebra.TH
import Test.QuickCheck.Checkers
import qualified Data.Set as S
import Data.Monoid

data Undecided = Undecided
  deriving (Eq, Ord, Show, Read)
instance Model Undecided Undecided where
  model = id
instance Arbitrary Undecided where
  arbitrary = pure Undecided
instance CoArbitrary Undecided where
  coarbitrary _ = id
instance EqProp Undecided where
  (=-=) = (===)

instance EqProp Any where
  (=-=) = (===)

newtype ModeledBy a = ModeledBy
  { modeledBy :: a
  } deriving newtype (Eq, Ord, Enum, Bounded, Read, Semigroup, Monoid)

instance Typeable a => Show (ModeledBy a) where
  show (ModeledBy a) = show $ typeOf a

instance Arbitrary a => Arbitrary (ModeledBy a) where
  arbitrary = fmap ModeledBy arbitrary

instance EqProp a => EqProp (ModeledBy a) where
  (=-=) = (=-=) `on` modeledBy

instance EqProp a => EqProp (S.Set a) where
  (=-=) = (=-=) `on` S.toList

instance Model (ModeledBy a) a where
  model = modeledBy

instance CoArbitrary a => CoArbitrary (ModeledBy a) where
  coarbitrary (ModeledBy a) = coarbitrary a


type Who        = ModeledBy Int
type Permission = Undecided
type Policy     = ModeledBy (Who -> S.Set Permission)
type Hierarchy  = [Undecided]
type ResourcePath = ModeledBy [ResourceName]
type ResourceName = ModeledBy String

instance (EqProp (f (g a))) => EqProp (Compose f g a) where
  Compose f =-= Compose g = f =-= g

instance (Semigroup (f (g a))) => Semigroup (Compose f g a) where
  Compose f <> Compose g = Compose (f <> g)

instance (Monoid (f (g a))) => Monoid (Compose f g a) where
  mempty = Compose mempty

get :: ResourcePath -> Hierarchy -> Maybe Policy
get _ _ = mempty

set :: ResourcePath -> Policy -> Hierarchy -> Hierarchy
set _ _ = id

test :: Who -> ResourcePath -> Hierarchy -> Permission -> Any
test _ _ _ _ = Any False

hierarchy :: ResourceName -> Policy -> Hierarchy -> Hierarchy
hierarchy _ _ = id

exact :: ResourceName -> ResourcePath
exact = ModeledBy . pure

instance Model a b => Model (Maybe a) (Maybe b) where
  model = fmap model

instance Model Any Any where
  model = id

instance (Ord b, Model a b) => Model (S.Set a) (S.Set b) where
  model = S.map model


laws :: [Property]
laws = $(theoremsOf' [| do
  homo @Monoid $ \h -> test w rp h p
  homo @Monoid $ \h -> get rp h
  homo @Monoid $ \h -> set rp p h
  law "jank/get" $ Just 5 == Nothing
  law "bad/get" $ Left x == Right (insert x x)
  law "spank/get" $ Spanky Nuts == Ten
  law "set/get" $ maybe h (flip (set rp) h) (get rp h) == h
  law "set/set" $ set rp p' (set rp p h) == set rp p' h
  law "get/set" $ get rp (set rp p h) == Just p
  law "get/exact-hierarchy" $
    get (exact rn) (hierarchy rn p c) == Just p
  law "test/exact-hierarchy" $
    test w (exact rn) (hierarchy rn p c) perm
      == Any (S.member perm (model p who))
  |])

main :: IO ()
main = quickCheck laws

