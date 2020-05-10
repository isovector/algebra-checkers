{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Main where

import qualified AppTest as AT
import Test.Hspec
import Test.QuickCheck

main :: IO ()
main = hspec $ do
  describe "App" $ do
    it "should generate models" $
      property $ \n ->
        AT.model_foo n `shouldBe` (n + 1)

    describe "Empty types" $ do
      it "should be generated" $ do
        AT.EmptyType `shouldBe` AT.EmptyType

      it "should have trivial arbitrary instances" $
        property $ \empty ->
          empty `shouldBe` AT.EmptyType

