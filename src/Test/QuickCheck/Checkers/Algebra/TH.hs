{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns     #-}

module Test.QuickCheck.Checkers.Algebra.TH where


-- import           Test.QuickCheck.Checkers (TestBatch)
import Data.Foldable
import           Control.Monad
import           Control.Monad.Trans.State
import           Data.Char
import           Data.Dynamic
import           Data.List (nub, intercalate)
import qualified Data.Map as M
import           Data.Maybe
import           Data.Traversable
import           Language.Haskell.TH
import           Test.QuickCheck hiding (collect)
import           Test.QuickCheck.Checkers.Algebra.Types
import           Test.QuickCheck.Checkers.Algebra.Unification



biasedGenerate :: [a] -> Gen a -> Gen a
biasedGenerate [] gena = gena
biasedGenerate as gena =
  frequency
    [ (1, elements as)
    , (1, gena)
    ]


getDyns :: (Typeable a, Monad m) => StateT [Dynamic] m [a]
getDyns = fmap (mapMaybe fromDynamic) get


mkMap :: [Name] -> [a] -> (a -> b) -> M.Map Name b
mkMap vars as f = M.fromList . zip vars $ fmap f as


propTestEq :: Exp -> Exp -> ExpQ
propTestEq exp1 exp2 = do
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
lawConf (DoE z) = do
  let laws = fmap collect z
      lhs_rhs_tests = fmap (\(Law' _ a b) -> propTestEq a b) laws
      critical_tests = do
        l1 <- laws
        l2 <- laws
        guard $ l1 /= l2
        (lhs, rhs) <- criticalPairs l1 l2
        pure $ propTestEq lhs rhs
      tests = lhs_rhs_tests ++ critical_tests
  listE tests
lawConf _ = error "you have to call lawConf with a do block"

data ImplSort
  = LawDefn String
  | Interaction String String
  deriving (Eq, Ord, Show)

showImplSort :: ImplSort -> String
showImplSort (LawDefn n) = "the definition of " ++ show n
showImplSort (Interaction a b) =
  mconcat
    [ "an interaction between "
    , show $ min a b
    , " and "
    , show $ max a b
    ]

data Implication = Implication
  { implSort :: ImplSort
  , implLhs :: Exp
  , implRhs :: Exp
  }

instance Eq Implication where
  Implication _ a a' == Implication _ b b' =
    equalUpToAlpha a b && equalUpToAlpha a' b'

implicationsOf' :: ExpQ -> ExpQ
implicationsOf' = (implicationsOf =<<)

implicationsOf :: Exp -> ExpQ
implicationsOf (DoE z) = do
  -- todo: base everything around the implication type
  let laws = fmap collect z
      law_impls = fmap (\(Law' n a b) -> Implication (LawDefn n) a b) laws
      implications = do
        l1 <- laws
        l2 <- laws
        guard $ l1 /= l2
        (lhs, rhs) <- criticalPairs l1 l2
        pure $ Implication (Interaction (lawName l1) (lawName l2)) lhs rhs
  for_ (nub $ law_impls <> implications) $ \(Implication n a b) -> do
    let vars = nub $ fmap nameBase $ unboundVars a ++ unboundVars b
    reportWarning $ mconcat
      [ "∀ "
      , intercalate " " vars
      , "\n      . "
      , pprint $ deModuleName a
      , "\n     == "
      , pprint $ deModuleName b
      , "\n arising from "
      , showImplSort n
      ]
  lawConf (DoE z)
implicationsOf _ = error "you have to call implicationsOf with a do block"


collect :: Stmt -> Law'
collect (LawStmt lawname exp1 exp2) = Law' lawname exp1 exp2
collect (LawDollar lawname exp1 exp2) = Law' lawname exp1 exp2
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


------------------------------------------------------------------------------
-- | A bare-boned implementation of printf. This function will replace tokens
-- of the form @"%n"@ in the first string with @args !! n@.
--
-- This will only work for indexes up to 9.
--
-- For example:
--
-- >>> printf "hello %1 %2% %3 %1" ["world", "50"]
-- "hello world 50% %3 world"
printf :: String -> [String] -> String
printf str args = splitArgs str
  where
    splitArgs :: String -> String
    splitArgs s =
      case break (== '%') s of
        (as, "") -> as
        (as, _ : b : bs)
          | isDigit b
          , let d = read [b] - 1
          , d < length args
            -> as ++ (args !! d) ++ splitArgs bs
        (as, _ : bs) ->  as ++ "%" ++ splitArgs bs

