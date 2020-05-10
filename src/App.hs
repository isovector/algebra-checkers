{-# LANGUAGE LambdaCase #-}

module App where

import           AlgebraCheckers.Utils
import           App.Parser
import           App.Types
import           Data.Char
import           Data.Foldable
import qualified Data.Map as M
import           Language.Haskell.Lexer


buildStuffMap :: [Decl a] -> StuffMap a
buildStuffMap = foldMap $ \case
  LawD       t
    -> StuffMap mempty [t] mempty mempty mempty mempty mempty
  FunModelD  t
    -> StuffMap mempty mempty [t] mempty mempty mempty mempty
  TypeModelD (t@(TypeModel n _ _))
    -> StuffMap mempty mempty mempty (M.singleton n t) mempty mempty mempty
  d@(TypeSigD t)
    -> StuffMap mempty mempty mempty mempty [d] [t] mempty
  EmptyTypeD n
    -> StuffMap mempty mempty mempty mempty mempty mempty [n]
  t -> StuffMap mempty mempty mempty mempty [t] mempty mempty


addImport :: a -> StuffMap a -> StuffMap a
addImport im sm =
  let (header, rest) = span (not . isOpening) $ smOther sm
   in sm { smOther = mconcat [ header, [Opening, Import im], drop 1 rest ] }


addHeader :: a -> StuffMap a -> StuffMap a
addHeader a sm =
  sm { smHeader = a : smHeader sm }


isOpening :: Decl a -> Bool
isOpening Opening = True
isOpening _       = False


dumpModeledBy :: TypeModel String -> String
dumpModeledBy (TypeModel nm vars res) = unlines
  [ mconcat
    [ "type "
    , mkHead nm vars
    , " = "
    , "ModeledBy ("
    , sanitizeSpan res
    , ")"
    ]
  , mconcat
    [ "{-# WARNING "
    , nm
    , " \"This is a placeholder type.\" "
    , "#-}"
    ]
  ]


dumpEmptyType :: String -> [String] -> String
dumpEmptyType nm vars = unlines
  [ mconcat
      [ "data "
      , mkHead nm vars
      , " = "
      , nm
      ]
  , "  deriving (Eq, Show, Generic)"
  , mconcat
    [ "{-# WARNING "
    , nm
    , "\"This is a placeholder type.\""
    , " #-}"
    ]
  , mconcat
      [ "instance EqProp ("
      , mkHead nm vars
      , ") where"
      ]
  , "  (=-=) = (===)"
  , mconcat
      [ "instance Arbitrary ("
      , mkHead nm vars
      , ") where"
      ]
  , mconcat
      [ "  arbitrary = pure "
      , nm
      ]
  ]


dumpEmptyAndModeledType
    :: M.Map String (TypeModel String)
    -> EmptyType
    -> String
dumpEmptyAndModeledType m (EmptyType nm vars) =
  case M.lookup nm m of
    Just tm -> dumpModeledBy tm
    Nothing -> dumpEmptyType nm vars

mkHead :: String -> [String] -> String
mkHead nm vars = mconcat
  [ nm
  , " "
  , unwords vars
  ]


passThrough :: Decl String -> String
passThrough (TypeSigD (TypeSig z m))   = mconcat [z, " :: ", m]
passThrough LawD{}                     = mempty
passThrough (FunModelD (FunModel _ m)) = m
passThrough TypeModelD{}               = mempty
passThrough (Other m)                  = m
passThrough Opening                    = mempty
passThrough (Import m)                 = "import " ++ m ++ "\n"
passThrough EmptyTypeD{}               = mempty


dumpStuffMap :: StuffMap String -> String
dumpStuffMap sm = unlines
  [ unlines $ smHeader sm
  , foldMap passThrough $ smOther sm
  , foldMap (dumpEmptyAndModeledType (smTypeModels sm)) $ smEmptyTypes sm
  , "pure []"
  , ""
  , "---------- MODELS BEGIN HERE ----------"
  , "modelsFor =<< [d|"
  , foldMap (mappend "  " . passThrough) $ fmap FunModelD (smFunModels sm) <> fmap TypeSigD (smSigs sm)
  , "  |]"
  , ""
  , dumpLaws $ smLaws sm
  ]


dumpLaws :: [Law String] -> String
dumpLaws [] = mempty
dumpLaws laws = unlines
  [ "---------- LAWS BEGIN HERE ----------"
  , "prop_laws :: [Property]"
  , "prop_laws = $(theoremsOf [e| do"
  , foldMap dumpLaw laws
  , "|])"
  ]

trimTrailingSpace :: String -> String
trimTrailingSpace = dropEndWhile isSpace


dumpLaw :: Law String -> String
dumpLaw (Law name lhs rhs) =
  mconcat
    [ "law "
    , show name
    , " $ ("
    , sanitizeSpan lhs
    , ") == ("
    , sanitizeSpan rhs
    , ")\n"
    ]


sanitizeSpan :: String -> String
sanitizeSpan = trimTrailingSpace . removeComments


rmSpace2 :: [PosToken] -> [PosToken]
rmSpace2 = filter $ notWhite . fst

notWhite :: Token -> Bool
notWhite t = t/=Commentstart && t/=Comment &&
             t/=NestedComment


removeComments :: String -> String
removeComments = foldMap (snd . snd) . rmSpace2 . lexerPass0


app :: [Decl String] -> String
app
  = dumpStuffMap
  . addHeader "{-# LANGUAGE TemplateHaskell #-}"
  . addHeader "{-# LANGUAGE DeriveGeneric #-}"
  . addHeader "{-# OPTIONS_GHC -fno-warn-unused-imports #-}"
  . addImport "Test.QuickCheck"
  . addImport "Test.QuickCheck.Checkers (Model (..), EqProp (..))"
  . addImport "GHC.Generics (Generic)"
  . addImport "AlgebraCheckers (law)"
  . addImport "AlgebraCheckers.Tools (ModeledBy)"
  . addImport "AlgebraCheckers.TH (theoremsOf)"
  . addImport "AlgebraCheckers.Modeling (modelsFor, unmodel)"
  . buildStuffMap



main :: IO ()
main
  = traverse_ (putStrLn . app)
  . parseAndSubst
    =<< readFile "/home/sandy/prj/algebra-checkers/test/App.hs"

