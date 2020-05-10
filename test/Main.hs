{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Main where

import qualified AppTest as AT
import Test.Hspec
import Test.QuickCheck
import Data.Foldable

main :: IO ()
main = hspec $ do
  describe "App" $ do
    it "should generate models" $ do
      AT.model_foo 5 `shouldBe` 6

    describe "generated model tests" $ do
      for_ AT.prop_model_laws $ \(name, prop) ->
        it name prop

    describe "Empty types" $ do
      it "should be generated" $ do
        AT.EmptyType `shouldBe` AT.EmptyType

      it "should have trivial arbitrary instances" $
        property $ \empty ->
          empty `shouldBe` AT.EmptyType

