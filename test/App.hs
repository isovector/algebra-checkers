{-# LANGUAGE TypeFamilies              #-}
{-# OPTIONS_GHC -F -pgmF algebra-check #-}
{-# OPTIONS_GHC -ddump-splices         #-}

module App where

type Bar
μ Bar = Int


foo :: Bar -> Int
foo = undefined
{-# WARNING foo "generated" #-}
μ foo = model . uploadBar

uploadBar :: Bar -> Bar
uploadBar = undefined
μ uploadBar bar = unmodel $ model bar + 1


