{-# LANGUAGE TypeFamilies              #-}
{-# OPTIONS_GHC -F -pgmF algebra-check #-}
{-# OPTIONS_GHC -ddump-splices         #-}

module App where

data Bar = Bar Int
  deriving (Show, Eq)

instance Model Bar where
  type ModelOf Bar = Int
  model (Bar i) = i


foo :: Bar -> Int
foo = undefined
{-# WARNING foo "generated" #-}
μ foo = model . uploadBar

uploadBar :: Bar -> Bar
uploadBar = undefined
μ uploadBar bar = unmodel $ model bar + 1


