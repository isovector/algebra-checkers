module AlgebraCheckers.Ppr
  ( module AlgebraCheckers.Ppr
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
import           AlgebraCheckers.Types
import           AlgebraCheckers.Unification
import qualified Text.PrettyPrint.HughesPJ as Ppr
import           Text.PrettyPrint.HughesPJ hiding ((<>))


ppr :: Ppr a => a -> Doc
ppr = to_HPJ_Doc . Ppr.ppr

showTheoremSource :: Bool -> TheoremSource -> Doc
showTheoremSource c (LawDefn n) =
  text "definition of" <+> colorize c lawColor (text $ show n)
showTheoremSource c (Interaction a b) =
  hsep
    [ text "implied by"
    , colorize c lawColor $ text $ show $ min a b
    , text "and"
    , colorize c lawColor $ text $ show $ max a b
    ]

colorize :: Bool -> Color -> Doc -> Doc
colorize False _ doc = doc
colorize True c doc
       = zeroWidthText (setSGRCode [SetColor Foreground Vivid c])
  Ppr.<> doc
  Ppr.<> zeroWidthText (setSGRCode [SetDefaultColor Foreground])

deepColorize :: Bool -> Color -> Doc -> Doc
deepColorize False _ doc = doc
deepColorize True c doc
       = zeroWidthText (setSGRCode [SetColor Foreground Vivid c, SetConsoleIntensity BoldIntensity])
  Ppr.<> doc
  Ppr.<> zeroWidthText (setSGRCode [SetDefaultColor Foreground, SetConsoleIntensity NormalIntensity])

backcolorize :: Bool -> Color -> Doc -> Doc
backcolorize False _ doc = doc
backcolorize True c doc
       = zeroWidthText (setSGRCode [SetColor Background Dull c])
  Ppr.<> doc
  Ppr.<> zeroWidthText (setSGRCode [SetDefaultColor Background])

showSaneTheorem :: Bool -> Theorem -> Doc
showSaneTheorem c (Law n a b) = hang (text "•") 2 $
  sep
  [ hang (colorize c exprColor $ ppr $ deModuleName a) 6
      . hang (text "=") 2
      . colorize c exprColor
      . ppr
      $ deModuleName b
  , nest 2 $ parens $ showTheoremSource c n
  ]

showContradictoryTheorem :: Bool -> Theorem -> TheoremProblem -> Doc
showContradictoryTheorem c (Law n a b) (Contradiction reason) = hang (text "•") 2 $
  sep
  [ vcat
      [ backcolorize c Red $ hang (ppr $ deModuleName a) 6
          . hang (text "=") 2
          . ppr
          $ deModuleName b
      , nest 2 $ pprContradiction reason
      ]
  , nest 2 $ parens $ showTheoremSource c n
  ]
showContradictoryTheorem c (Law n a b) (Dodgy reason) = hang (text "•") 2 $
  sep
  [ vcat
      [ hang (backcolorize c Black $ ppr $ deModuleName a) 6
          . hang (text "=") 2
          . backcolorize c Black
          . ppr
          $ deModuleName b
      , nest 2 $ pprDodgy reason
      ]
  , nest 2 $ parens $ showTheoremSource c n
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

pprDodgy :: DodgyReason -> Doc
pprDodgy SelfRecursive =
  text "not necessarily productive"


exprColor :: Color
exprColor = Blue

lawColor :: Color
lawColor = Yellow

