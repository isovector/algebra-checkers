{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE NumDecimals      #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fexternal-interpreter -prof -opti+RTS -opti-p #-}


module ListPresentation where

import Control.Monad
import Data.Foldable
import AlgebraCheckers.Presentation
import AlgebraCheckers
import AlgebraCheckers.TH
import Language.Haskell.TH
import Language.Haskell.TH.PprLib (vcat, text)
import qualified Language.Haskell.TH.PprLib as P
import           Debug.Trace


data Seq a = Nil | UnitCat a (Seq a)

nil :: Seq a
nil = undefined
unit :: a -> Seq a
unit = undefined
cat :: Seq a -> Seq a -> Seq a
cat = undefined
list :: Seq a -> [a]
list = undefined


pure []

do
  laws <- parseLaws <$> [e| do
    law "defn:Nil" $ Nil == nil
    law "defn:UnitCat" $ UnitCat x xs == cat (unit x) xs

    law "assoc" $ cat xs (cat ys zs) == cat (cat xs ys) zs
    law "lid" $ cat nil xs == xs
    law "rid" $ cat xs nil == xs
    law "empty" $ list nil == []
    law "homo" $ list (cat (unit x) xs) == x : list xs
    |]
  exps <- algebra ['cat] ''Seq
  -- exps <- pure @[] <$> mkExpr (VarE 'cat `AppE` (ConE 'Nil)) 1
  for_ exps $ \z@(_, e) -> do
    !res <- pure $ smarter (bothWays =<< laws) z
    traceM "----- DONE -----"

    reportWarning
      . show
      . maybe
          (text "couldn't solve: " P.<> ppr e)
          (vcat . fmap ppr . mappend [e])
      $ res
  pure []


cat (UnitCat (cat nil x_0) x_1) x_2
cat (UnitCat (cat x_0 nil) x_1) x_2
cat (UnitCat x_0 (cat nil x_1)) x_2
cat (UnitCat x_0 (cat x_1 nil)) x_2
cat (UnitCat x_0 x_1) (cat nil x_2)
cat (UnitCat x_0 x_1) (cat nil x_2)
cat (UnitCat x_0 x_1) (cat x_2 nil)
cat (UnitCat x_0 x_1) (cat x_2 nil)
cat (UnitCat x_0 x_1) x_2
cat (UnitCat x_0 x_1) x_2
cat (UnitCat x_0 x_1) x_2
cat (cat (UnitCat x_0 x_1) nil) x_2
cat (cat (UnitCat x_0 x_1) nil) x_2
cat (cat (UnitCat x_0 x_1) x_2) nil
cat (cat (UnitCat x_0 x_1) x_2) nil
cat (cat (UnitCat x_0 x_1)) nil x_2
cat (cat (UnitCat x_0) nil x_1) x_2
cat (cat (unit x_0) x_1) x_2
cat (cat UnitCat nil x_0 x_1) x_2
cat (cat nil (UnitCat x_0 x_1)) x_2
cat (cat nil (UnitCat x_0 x_1)) x_2
cat (cat nil (UnitCat x_0) x_1) x_2
cat (cat nil UnitCat x_0 x_1) x_2
cat (unit x_0) (cat x_1 x_2)
cat nil (cat (UnitCat x_0 x_1) x_2)
cat nil (cat (UnitCat x_0 x_1) x_2)
cat nil (cat (UnitCat x_0 x_1)) x_2
cat nil cat (UnitCat x_0 x_1) x_2
cat cat nil (UnitCat x_0 x_1) x_2
