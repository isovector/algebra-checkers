{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Modeling where

import           Data.Foldable
import           Data.Function
import           Data.Functor.Compose
import           Data.Group
import qualified Data.Map as M
import           Data.Monoid
import qualified Data.Set as S
import           GHC.Generics
import           Test.QuickCheck
import           Test.QuickCheck.Checkers
import           Test.QuickCheck.Checkers.Algebra.Patterns (law, homo)
import           Test.QuickCheck.Checkers.Algebra.TH
import           Unsafe.Coerce

-- import           Test.QuickCheck.Checkers.Algebra.Ppr
-- import           Test.QuickCheck.Checkers.Algebra.Suggestions


data Undecided = Undecided
  deriving stock (Eq, Ord, Show, Read, Generic)
  deriving anyclass EqProp

instance Function a => Function (ModeledBy a)

instance (Function a, Semigroup b) => Semigroup (Fun a b) where
  -- fn1 <> fn2 = _
  Fun (fnab1, b1, s1) fab1 <> Fun (fnab2, b2, s2) fab2 =
    Fun (function (const $ b1 <> b2), b1 <> b2, s1) (fab1 <> fab2)

instance (Function a, Monoid b) => Monoid (Fun a b) where
  mempty = Fun (function mempty, mempty, unsafeCoerce True) mempty

instance (Arbitrary a, Show a, EqProp b) => EqProp (Fun a b) where
  (=-=) = (=-=) `on` applyFun

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

-- instance (Typeable a, Typeable b) => Show (a -> b) where
--   show _ =
--     mconcat
--       [ show $ typeOf @a undefined
--       , " -> "
--       , show $ typeOf @b undefined
--       ]

instance Arbitrary a => Arbitrary (ModeledBy a) where
  arbitrary = fmap ModeledBy arbitrary
  shrink = fmap ModeledBy . shrink . modeledBy

instance EqProp a => EqProp (ModeledBy a)

instance EqProp a => EqProp (S.Set a) where
  (=-=) = (=-=) `on` S.toList

instance Model (ModeledBy a) a where
  model = modeledBy

instance CoArbitrary a => CoArbitrary (ModeledBy a) where
  coarbitrary (ModeledBy a) = coarbitrary a


type Who          = ModeledBy Int
type Permission   = ModeledBy Int
type Policy       = ModeledBy (Fun Who (S.Set Permission))
type Hierarchy    = ModeledBy (M.Map ResourceName HierarchyDeno)
type ResourcePath = ModeledBy [ResourceName]
type ResourceName = ModeledBy String

data HierarchyDeno = HierarchyDeno
  { hdenoPolicy   :: Policy
  , hdenoChildren :: Hierarchy
  } deriving (Show, Generic)

instance EqProp HierarchyDeno
instance Arbitrary HierarchyDeno where
  arbitrary = sized $ \case
    0 -> HierarchyDeno <$> arbitrary <*> pure mempty
    n -> HierarchyDeno <$> arbitrary <*> resize (n `div` 4) arbitrary
  shrink = genericShrink

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
    [rn] -> maybe mempty (\r -> Any $ S.member p $ applyFun (model (hdenoPolicy r)) w) $ M.lookup rn (model h)
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

-- $(fmap (error . unlines . fmap (render . pprSuggestion)) $
--   suggest' ['hierarchy, 'exact, 'test, 'set, 'get])


laws :: [Property]
laws = $(lawConf' [| do
  law "set/set"    $ set i x' (set i x s) == set i x' s
  law "set/get"    $ maybe h (flip (set i) h) (get i s) == h
  law "get/set"    $ get i (set i x h) == (x <$ get i h)
  homo @Monoid $ \h -> set i x h
  homo @Monoid $ \h -> get i h
  |])

(?) :: (a -> b -> c) -> b -> a -> c
(?) = flip

main :: IO ()
main = traverse_ quickCheck laws

