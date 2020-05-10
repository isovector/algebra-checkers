module Main where

import qualified AppTest as AT
import Test.Hspec

main :: IO ()
main = hspec $ do
  describe "App" $ do
    it "should generate models" $ do
      AT.model_foo 5 `shouldBe` 6

    it "should generate empty types" $ do
      show AT.EmptyType `shouldBe` "EmptyType"

