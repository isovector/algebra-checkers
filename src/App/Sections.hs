{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}

module App.Sections where

import           App.Cleaning
import           App.Types
import           Data.List
import qualified Data.Map as M
import           Data.String.Interpolate
import           Language.Haskell.TH (Name)


dumpModeledBy :: TypeModel String -> String
dumpModeledBy (TypeModel nm vars res) = [i|
type #{mkHead nm vars} = ModeledBy (#{sanitizeSpan res})
{-# WARNING #{nm} "This is a placeholder type." #-}
|]


dumpEmptyType :: String -> [String] -> String
dumpEmptyType nm vars = [i|
data #{mkHead nm vars} = #{nm}
  deriving (Eq, Show, Generic)
{-# WARNING #{nm} "This is a placeholder type." #-}

instance EqProp (#{mkHead nm vars}) where
  (=-=) = (===)

instance Arbitrary (#{mkHead nm vars}) where
  arbitrary = pure #{nm}
|]


dumpStuffMap :: StuffMap String -> String
dumpStuffMap sm = unlines
  [ unlines $ smHeader sm
  , foldMap passThrough $ smOther sm
  , foldMap (dumpEmptyAndModeledType (smTypeModels sm)) $ smEmptyTypes sm
  , emptySplice
  , dumpModels sm
  , dumpLaws $ smLaws sm
  ]


emptySplice :: String
emptySplice = "pure []"


dumpModels  :: StuffMap String -> String
dumpModels sm = [i|
---------- MODELS BEGIN HERE ----------
modelsFor =<< [d|
#{foldMap (mappend "  " . passThrough) $ fmap FunModelD (smFunModels sm) <> fmap TypeSigD (smSigs sm)}
  #{endQuote}
|]


dumpLaws :: [Law String] -> String
dumpLaws [] = mempty
dumpLaws laws = [i|
---------- LAWS BEGIN HERE ----------

(theoremsOf [e| do
#{foldMap dumpLaw laws}
  #{endQuote} >>= putQ) >> pure []

prop_laws :: [Property]
prop_laws = fmap snd $ $(do
  Just decs <- getQ
  pure decs)

prop_model_laws :: [(String, Property)]
prop_model_laws = $(do
  Just decs <- getQ
  Just nms <- getQ
  pure $ sloppyReplaceWithModelNames mkModelName nms decs
  )
|]


endQuote :: String
endQuote = "|]"


dumpLaw :: Law String -> String
dumpLaw (Law name lhs rhs) = [i|
  law "#{name}" $ (#{sanitizeSpan lhs}) == (#{sanitizeSpan rhs})
|]


dumpModeledFunctionNames :: [Name] -> String
dumpModeledFunctionNames = intercalate ", " . fmap (\n -> [i|mkName "#{n}"|])


mkHead :: String -> [String] -> String
mkHead nm = unwords . (nm :)


passThrough :: Decl String -> String
passThrough (TypeSigD (TypeSig z m))   = mconcat [z, " :: ", m]
passThrough LawD{}                     = mempty
passThrough (FunModelD (FunModel _ m)) = m
passThrough TypeModelD{}               = mempty
passThrough (Other m)                  = m
passThrough Opening                    = mempty
passThrough (Import m)                 = "import " ++ m ++ "\n"
passThrough EmptyTypeD{}               = mempty


dumpEmptyAndModeledType
    :: M.Map String (TypeModel String)
    -> EmptyType
    -> String
dumpEmptyAndModeledType m (EmptyType nm vars) =
  case M.lookup nm m of
    Just tm -> dumpModeledBy tm
    Nothing -> dumpEmptyType nm vars

