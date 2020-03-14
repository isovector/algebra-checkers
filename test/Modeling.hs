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

import Data.Foldable
import qualified Data.Map as M
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

instance Show a => Show (ModeledBy a) where
  show (ModeledBy a) = show a

instance (Typeable a, Typeable b) => Show (a -> b) where
  show _ =
    mconcat
      [ show $ typeOf @a undefined
      , " -> "
      , show $ typeOf @b undefined
      ]

instance Arbitrary a => Arbitrary (ModeledBy a) where
  arbitrary = fmap ModeledBy arbitrary

instance EqProp a => EqProp (ModeledBy a)

instance EqProp a => EqProp (S.Set a) where
  (=-=) = (=-=) `on` S.toList

instance Model (ModeledBy a) a where
  model = modeledBy

instance CoArbitrary a => CoArbitrary (ModeledBy a) where
  coarbitrary (ModeledBy a) = coarbitrary a


type Who          = ModeledBy Int
type Permission   = ModeledBy Int
type Policy       = ModeledBy (Who -> S.Set Permission)
type Hierarchy    = ModeledBy (M.Map ResourceName HierarchyDeno)
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
get rp h =
  case model rp of
    [] -> mempty
    [rn] -> fmap hdenoPolicy $ M.lookup rn (model h)
    (rn : rp') -> maybe mempty (get (ModeledBy rp') . hdenoChildren) $ M.lookup rn (model h)

-- TODO(sandy): there was a bug here where i forgot to keep the old hierarchy structure
-- nice catch!
--
-- there is another bug where we'd not update our children properly
set :: ResourcePath -> Policy -> Hierarchy -> Hierarchy
set rp p h =
  case model rp of
    [] -> h
    [rn] -> maybe h (\(HierarchyDeno _ c) -> hierarchy rn p c <> h) $ M.lookup rn $ model h
    (rn:rp') -> maybe h (\h' ->
      ModeledBy (M.singleton rn $ h' { hdenoChildren = set (ModeledBy rp') p $ hdenoChildren h' }) <> h)
              $ M.lookup rn
              $ model h

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


-- laws :: [Property]
-- laws = $(theoremsOf' [| do
--   undefined
--   |])

(?) :: (a -> b -> c) -> b -> a -> c
(?) = flip

-- main :: IO ()
-- main = traverse_ quickCheck laws

