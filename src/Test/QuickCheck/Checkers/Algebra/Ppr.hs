module Test.QuickCheck.Checkers.Algebra.Ppr
  ( module Test.QuickCheck.Checkers.Algebra.Ppr
  , Doc
  , render
  , sep
  , vcat
  , hsep
  , text
  ) where

import           Control.Monad
import qualified Language.Haskell.TH as Ppr (ppr)
import           Language.Haskell.TH hiding (ppr, Arity)
import           Language.Haskell.TH.PprLib (to_HPJ_Doc)
import           Prelude hiding (exp)
import           System.Console.ANSI
import           Test.QuickCheck.Checkers.Algebra.Types
import           Test.QuickCheck.Checkers.Algebra.Unification
import qualified Text.PrettyPrint.HughesPJ as Ppr
import           Text.PrettyPrint.HughesPJ hiding ((<>))


ppr :: Ppr a => a -> Doc
ppr = to_HPJ_Doc . Ppr.ppr

showTheoremSource :: TheoremSource -> Doc
showTheoremSource (LawDefn n) =
  text "definition of" <+> colorize lawColor (text $ show n)
showTheoremSource (Interaction a b) =
  hsep
    [ text "implied by"
    , colorize lawColor $ text $ show $ min a b
    , text "and"
    , colorize lawColor $ text $ show $ max a b
    ]

colorize :: Color -> Doc -> Doc
colorize c doc
       = zeroWidthText (setSGRCode [SetColor Foreground Vivid c])
  Ppr.<> doc
  Ppr.<> zeroWidthText (setSGRCode [SetDefaultColor Foreground])

deepColorize :: Color -> Doc -> Doc
deepColorize c doc
       = zeroWidthText (setSGRCode [SetColor Foreground Vivid c, SetConsoleIntensity BoldIntensity])
  Ppr.<> doc
  Ppr.<> zeroWidthText (setSGRCode [SetDefaultColor Foreground, SetConsoleIntensity NormalIntensity])

backcolorize :: Color -> Doc -> Doc
backcolorize c doc
       = zeroWidthText (setSGRCode [SetColor Background Dull c])
  Ppr.<> doc
  Ppr.<> zeroWidthText (setSGRCode [SetDefaultColor Background])

showSaneTheorem :: Theorem -> Doc
showSaneTheorem (Law n a b) = hang (text "•") 2 $
  sep
  [ hang (colorize exprColor $ ppr $ deModuleName a) 6
      . hang (text "=") 4
      . colorize exprColor
      . ppr
      $ deModuleName b
  , nest 2 $ parens $ showTheoremSource n
  ]

showContradictoryTheorem :: Theorem -> ContradictionReason -> Doc
showContradictoryTheorem (Law n a b) contradiction = hang (text "•") 2 $
  sep
  [ vcat
      [ backcolorize Red $ hang (ppr $ deModuleName a) 6
          . hang (text "=") 4
          . ppr
          $ deModuleName b
      , nest 2 $ pprContradiction contradiction
      ]
  , nest 2 $ parens $ showTheoremSource n
  ]

plural :: String -> String -> [a] -> Doc
plural one _ [_] = text one
plural _ many _  = text many

pprContradiction :: ContradictionReason -> Doc
pprContradiction (UnboundMatchableVars vars) =
  sep
    [ text "the"
    , plural "variable" "variables" vars
    , sep $ punctuate (char ',') $ fmap ppr vars
    , nest 4 $ sep
        [ plural "is" "are" vars
        , text "undetermined"
        ]
    ]
pprContradiction (UnknownConstructors vars) =
  sep
    [ text "the"
    , plural "constructor" "constructors" vars
    , sep $ punctuate (char ',') $ fmap ppr vars
    , nest 4 $ sep
        [ plural "does" "do" vars
        , text "not exist"
        ]
    ]
pprContradiction UnequalValues =
  text "unequal values"


exprColor :: Color
exprColor = Blue

lawColor :: Color
lawColor = Yellow

