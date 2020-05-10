{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module Readme where

import AlgebraCheckers
import Test.QuickCheck
import Test.QuickCheck.Checkers


data Foo a
instance Semigroup (Foo a)
instance Monoid (Foo a)
instance Arbitrary (Foo a)
instance Show (Foo a)
instance EqProp (Foo a) where
  (=-=) = undefined

data Key
instance Arbitrary Key
instance Show Key
instance EqProp Key where
  (=-=) = undefined


get :: Key -> Foo Int -> Int
get = undefined

set :: Key -> Int -> Foo Int -> Foo Int
set = undefined

pure []
lawTests :: [Property]
lawTests = $(theoremsOf [e| do
  law "set/set"
      (set i x' (set i x s) == set i x' s)

  law "set/get"
      (set i (get i s) s == s)

  law "get/set"
      (get i (set i x s) == x)

  homo @Monoid
      (\s -> set i x s)

  |])

