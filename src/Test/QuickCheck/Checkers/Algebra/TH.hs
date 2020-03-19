{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

module Test.QuickCheck.Checkers.Algebra.TH where

import Control.Monad
import Data.Bool
import Data.List (nub, partition)
import Data.Traversable
import Language.Haskell.TH hiding (ppr, Arity)
import Language.Haskell.TH.Syntax (lift, Module)
import Prelude hiding (exp)
import Test.QuickCheck hiding (collect)
import Test.QuickCheck.Checkers.Algebra.Homos
import Test.QuickCheck.Checkers.Algebra.Patterns
import Test.QuickCheck.Checkers.Algebra.Ppr
import Test.QuickCheck.Checkers.Algebra.Theorems
import Test.QuickCheck.Checkers.Algebra.Types
import Test.QuickCheck.Checkers.Algebra.Unification


showTheorem :: Module -> Theorem -> Doc
showTheorem md thm =
  case sanityCheck' md thm of
    Just contradiction ->
      showContradictoryTheorem thm contradiction
    Nothing -> showSaneTheorem thm

propTestEq :: Theorem -> ExpQ
propTestEq t@(Law _ exp1 exp2) = do
  md <- thisModule
  let vars = nub $ unboundVars exp1 ++ unboundVars exp2
  names <- for vars $ newName . nameBase
  [e|
    counterexample $(lift $ render $ showTheorem md t) $
      property $(lamE (fmap varP names) [e|
       $(pure exp1) =-= $(pure exp2)
      |])
    |]

lawConf' :: ExpQ -> ExpQ
lawConf' = (lawConf =<<)

lawConf :: Exp -> ExpQ
lawConf e = do
  m <- thisModule
  listE . fmap propTestEq . theorize m $ parseLaws e

parseLaws :: Exp -> [NamedLaw]
parseLaws (DoE z) = concatMap collect z
parseLaws _ = error "you must call parseLaws with a do block"

theoremsOf' :: ExpQ -> ExpQ
theoremsOf' = (theoremsOf =<<)

theoremsOf :: Exp -> ExpQ
theoremsOf z = do
  md <- thisModule
  let (theorems, problems) = partition (sanityCheck md) $ theorize md $ parseLaws z
      contradicts = filter (maybe False isContradiction . sanityCheck' md) problems
      dodgy       = filter (maybe False isDodgy . sanityCheck' md) problems
  runIO $ do
    putStrLn ""
    putStrLn . render
             $ sep
             $ text "Theorems:" : text "" : fmap (showTheorem md) theorems
    putStrLn ""
    putStrLn ""
    when (not $ null dodgy) $ do
      putStrLn . render
               $ sep
               $ text "Dodgy Theorems:" : text "" : fmap (showTheorem md) dodgy
      putStrLn ""
      putStrLn ""
    when (not $ null contradicts) $ do
      putStrLn . render
               $ sep
               $ text "Contradictions:" : text "" : fmap (showTheorem md) contradicts
      putStrLn ""
      putStrLn ""
  listE $ fmap propTestEq theorems

collect :: Stmt -> [NamedLaw]
collect (LawDef lawname exp1 exp2) = [Law lawname exp1 exp2]
collect (HomoDef ty expr)          = makeHomo ty (knownHomos ty) expr
collect x = error $ show x
  -- "collect must be called with the form [e| law \"name\" (foo a b c == bar a d e) |]"

