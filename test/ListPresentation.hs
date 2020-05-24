{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}

module ListPresentation where

import Data.Foldable
import AlgebraCheckers.Presentation
import AlgebraCheckers
import AlgebraCheckers.TH
import Language.Haskell.TH
import Language.Haskell.TH.PprLib (vcat, text)
import qualified Language.Haskell.TH.PprLib as P


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
  defs <- parseLaws <$> [e| do
    law "defn:Nil" $ Nil == nil
    law "defn:UnitCat" $ UnitCat x xs == cat (unit x) xs

    law "empty" $ list nil == []
    law "homo" $ list (cat (unit x) xs) == x : list xs
    law "assoc" $ cat xs (cat ys zs) == cat (cat xs ys) zs
    law "lid" $ cat nil xs == xs
    law "rid" $ cat xs nil == xs
    |]
  laws <- parseLaws <$> [e| do
    law "defn:Nil" $ Nil == nil
    law "defn:UnitCat" $ UnitCat x xs == cat (unit x) xs

    law "assoc" $ cat xs (cat ys zs) == cat (cat xs ys) zs
    law "lid" $ cat nil xs == xs
    law "rid" $ cat xs nil == xs
    law "empty" $ list nil == []
    law "homo" $ list (cat (unit x) xs) == x : list xs
    |]
  exps <- algebra ['list, 'nil, 'cat] ''Seq
  -- exps <- pure @[] <$> mkExpr (VarE 'cat `AppE` (ConE 'Nil)) 1
  for_ exps $ \z@(_, e) ->
    reportWarning
      . show
      . maybe
          (text "couldn't solve: " P.<> ppr e)
          (vcat . fmap ppr . mappend [e])
      $ smarter (bothWays =<< defs) z
  pure []

