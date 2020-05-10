{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# OPTIONS_GHC -ddump-splices #-}

module ModelsFor where

import AlgebraCheckers.Modeling
import Test.QuickCheck.Checkers

data Bar = Bar Int
instance Model Bar where
  type ModelOf Bar = Int
  model (Bar x) = x


pure []
modelsFor =<< [d|

  foo :: Bar -> Int
  foo = model . upload_bar

  upload_bar :: Bar -> Bar
  upload_bar bar = unmodel $ model bar + 1

  |]

