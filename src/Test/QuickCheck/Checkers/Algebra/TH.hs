{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE ViewPatterns     #-}

module Test.QuickCheck.Checkers.Algebra.TH where


import Control.Monad
import Data.List (nub)
import Data.Traversable
import Language.Haskell.TH hiding (ppr)
import qualified Language.Haskell.TH as Ppr (ppr)
import Language.Haskell.TH.PprLib (to_HPJ_Doc)
import System.Console.ANSI
import Test.QuickCheck hiding (collect)
import Test.QuickCheck.Checkers.Algebra.Types
import Test.QuickCheck.Checkers.Algebra.Unification
import Text.PrettyPrint.HughesPJ hiding ((<>))
import qualified Text.PrettyPrint.HughesPJ as Ppr


ppr :: Ppr a => a -> Doc
ppr = to_HPJ_Doc . Ppr.ppr


propTestEq :: Theorem -> ExpQ
propTestEq (Theorem _ exp1 exp2) = do
  let vars = nub $ unboundVars exp1 ++ unboundVars exp2
  names <- for vars $ newName . nameBase
  [e|
    property $(lamE (fmap varP names) [e|
      $(pure exp1) =-= $(pure exp2)
      |])
    |]

lawConf' :: ExpQ -> ExpQ
lawConf' = (lawConf =<<)

lawConf :: Exp -> ExpQ
lawConf = listE . fmap propTestEq . theorize . parseLaws

parseLaws :: Exp -> [Law]
parseLaws (DoE z) = fmap collect z
parseLaws _ = error "you must call parseLaws with a do block"

data TheoremSource
  = LawDefn String
  | Interaction String String
  deriving (Eq, Ord, Show)

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

lawColor :: Color
lawColor = Yellow


data Theorem = Theorem
  { theoremSort :: TheoremSource
  , theoremLhs  :: Exp
  , theoremRhs  :: Exp
  }

instance Eq Theorem where
  Theorem _ a a' == Theorem _ b b' =
    equalUpToAlpha a b && equalUpToAlpha a' b'

theorize :: [Law] -> [Theorem]
theorize laws =
  let law_defs = fmap (\(Law n a b) -> Theorem (LawDefn n) a b) laws
      theorems = do
         l1 <- laws
         l2 <- laws
         guard $ l1 /= l2
         (lhs, rhs) <- criticalPairs l1 l2
         pure $ Theorem (Interaction (lawName l1) (lawName l2)) lhs rhs
   in nub $ law_defs <> theorems


theoremsOf' :: ExpQ -> ExpQ
theoremsOf' = (theoremsOf =<<)


theoremsOf :: Exp -> ExpQ
theoremsOf z = do
  let theorems = theorize $ parseLaws z
  runIO $ do
    putStrLn ""
    putStrLn . render $ sep (text "Theorems:" : text "" : fmap showTheorem theorems)
    putStrLn ""
    putStrLn ""
  listE $ fmap propTestEq theorems


colorize :: Color -> Doc -> Doc
colorize c doc
       = zeroWidthText (setSGRCode [SetColor Foreground Vivid c])
  Ppr.<> doc
  Ppr.<> zeroWidthText (setSGRCode [SetDefaultColor Foreground])

backcolorize :: Color -> Doc -> Doc
backcolorize c doc
       = zeroWidthText (setSGRCode [SetColor Background Vivid c])
  Ppr.<> doc
  Ppr.<> zeroWidthText (setSGRCode [SetDefaultColor Background])


showTheorem :: Theorem -> Doc
showTheorem (Theorem n a b) = hang (text "•") 2 $
  sep
  [ hang (colorize exprColor $ ppr $ deModuleName a) 6
      $ hang (text "==") 4 $ (colorize exprColor $ ppr $ deModuleName b)
  , nest 2 $ parens $ showTheoremSource n
  ]

exprColor :: Color
exprColor = Blue


collect :: Stmt -> Law
collect (LawStmt lawname exp1 exp2) = Law lawname exp1 exp2
collect (LawDollar lawname exp1 exp2) = Law lawname exp1 exp2
collect _ = error
  "collect must be called with the form [e| law \"name\" (foo a b c == bar a d e) |]"

pattern LawStmt :: String -> Exp -> Exp -> Stmt
pattern LawStmt lawname exp1 exp2 <- NoBindS
  (      VarE ((==) 'law -> True)
  `AppE` LitE  (StringL lawname)
  `AppE` (InfixE (Just exp1)
                 (VarE ((==) '(==) -> True))
                 (Just exp2)
         )
  )

pattern LawDollar :: String -> Exp -> Exp -> Stmt
pattern LawDollar lawname exp1 exp2 <- NoBindS
  (InfixE
    (Just (  VarE ((==) 'law -> True)
      `AppE` LitE  (StringL lawname)))
    (VarE ((==) '($) -> True))
    (Just (InfixE (Just exp1)
                  (VarE ((==) '(==) -> True))
                  (Just exp2)
          )
    )
  )


law :: String -> Bool -> a
law = undefined

