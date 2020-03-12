{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
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
{-# LANGUAGE ViewPatterns               #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Modeling where

import qualified Data.Map as M
import Data.Map (Map)
import GHC.Generics
import Data.Functor.Compose
import Data.Typeable
import Data.Function
import Test.QuickCheck
import Test.QuickCheck.Checkers.Algebra.TH
import Test.QuickCheck.Checkers
import qualified Data.Set as S
import Data.Monoid

data Undecided = Undecided
  deriving stock (Eq, Ord, Show, Read, Generic)
  deriving anyclass EqProp

instance Model Undecided Undecided where
  model = id
instance Arbitrary Undecided where
  arbitrary = pure Undecided
instance CoArbitrary Undecided where
  coarbitrary _ = id

newtype ModeledBy a = ModeledBy
  { modeledBy :: a
  } deriving newtype (Eq, Ord, Enum, Bounded, Read, Semigroup, Monoid)
    deriving stock Generic

instance Typeable a => Show (ModeledBy a) where
  show (ModeledBy a) = show $ typeOf a

instance Arbitrary a => Arbitrary (ModeledBy a) where
  arbitrary = fmap ModeledBy arbitrary

instance EqProp a => EqProp (ModeledBy a)

instance EqProp a => EqProp (S.Set a) where
  (=-=) = (=-=) `on` S.toList

instance Model (ModeledBy a) a where
  model = modeledBy

instance CoArbitrary a => CoArbitrary (ModeledBy a) where
  coarbitrary (ModeledBy a) = coarbitrary a


type Who        = ModeledBy Int
type Permission = ModeledBy Int
type Policy     = ModeledBy (Who -> S.Set Permission)
type Hierarchy  = ModeledBy (M.Map ResourceName HierarchyDeno)
type ResourcePath = ModeledBy [ResourceName]
type ResourceName = ModeledBy String

data HierarchyDeno = HierarchyDeno
  { hdenoPolicy   :: Policy
  , hdenoChildren :: Hierarchy
  } deriving (Show, Generic)

instance EqProp HierarchyDeno
instance Arbitrary HierarchyDeno where
  arbitrary = HierarchyDeno <$> arbitrary <*> sized (\n -> resize (max 0 $ div n 3 - 1) arbitrary)

instance (Semigroup (f (g a))) => Semigroup (Compose f g a) where
  Compose f <> Compose g = Compose (f <> g)

instance (Monoid (f (g a))) => Monoid (Compose f g a) where
  mempty = Compose mempty

get :: ResourcePath -> Hierarchy -> Maybe Policy
get (model -> []) _ = mempty
get (model -> [rn]) h = fmap hdenoPolicy $ M.lookup rn (model h)
get (model -> (rn : rp)) h = maybe mempty (get (ModeledBy rp) . hdenoChildren) $ M.lookup rn (model h)

set :: ResourcePath -> Policy -> Hierarchy -> Hierarchy
set rp p h =
  case model rp of
    [] -> h
    [rn] -> maybe h (\(HierarchyDeno _ c) -> hierarchy rn p c) $ M.lookup rn $ model h
    (rn:rp') -> maybe h (set (ModeledBy rp') p . hdenoChildren) $ M.lookup rn $ model h

test :: Who -> ResourcePath -> Hierarchy -> Permission -> Any
test w rp h p =
  case model rp of
    [rn] -> maybe mempty (\r -> Any $ S.member p $ model (hdenoPolicy r) w) $ M.lookup rn (model h)
    (rn:rp') -> maybe mempty (\h' -> test w (ModeledBy rp') (hdenoChildren h') p) $ M.lookup rn (model h)
    [] -> mempty


hierarchy :: ResourceName -> Policy -> Hierarchy -> Hierarchy
hierarchy rn p h = ModeledBy $ M.singleton rn $ HierarchyDeno p h

exact :: ResourceName -> ResourcePath
exact = ModeledBy . pure

instance Model a b => Model (Maybe a) (Maybe b) where
  model = fmap model

instance Model Any Any where
  model = id

instance (Ord b, Model a b) => Model (S.Set a) (S.Set b) where
  model = S.map model

instance (EqProp k, EqProp v) => EqProp (M.Map k v) where
  (=-=) = (=-=) `on` M.toList


laws :: [Property]
laws = $(theoremsOf' [| do
  homo @Monoid $ \h -> test w rp h p
  homo @Monoid $ \h -> get rp h
  homo @Monoid $ \h -> set rp p h
  law "set/get" $ maybe h (flip (set rp) h) (get rp h) == h
  law "set/set" $ set rp p' (set rp p h) == set rp p' h
  law "get/set" $ get rp (set rp p h) == (p <$ get rp h)
  law "get/exact-hierarchy" $
    get (exact rn) (hierarchy rn p c) == Just p
  law "test/exact-hierarchy" $
    test who (exact rn) (hierarchy rn p c) perm
      == Any (S.member perm (model p who))
  |])

main :: IO ()
main = quickCheck laws

