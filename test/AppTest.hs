{-# OPTIONS_GHC -F -pgmF algebra-check #-}

module AppTest where

type Bar
μ Bar = Int

type EmptyType


foo :: Bar -> Int
foo = undefined
{-# WARNING foo "generated" #-}
μ foo = model . uploadBar

uploadBar :: Bar -> Bar
uploadBar = undefined
μ uploadBar bar = unmodel $ model bar + 1


