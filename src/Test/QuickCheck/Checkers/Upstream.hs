{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Test.QuickCheck.Checkers.Upstream where

import           Test.QuickCheck
import           Test.QuickCheck.Checkers


instance Model b b' => Model (a -> b) (a -> b') where
  model f = model . f


denotationFor
    :: (Model b b', Arbitrary a, EqProp b', Show a)
    => (a -> b')
    -> (a -> b)
    -> TestBatch
denotationFor g f =
  ( "denotation"
  , [("eq", model . f =-= g)]
  )

