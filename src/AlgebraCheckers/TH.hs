{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

module AlgebraCheckers.TH where

import Control.Monad
import Data.Bool
import Data.List (nub, partition)
import Data.Traversable
import Language.Haskell.TH hiding (ppr, Arity)
import Language.Haskell.TH.Syntax (lift, Module)
import Prelude hiding (exp)
import Test.QuickCheck hiding (collect)
import AlgebraCheckers.Homos
import AlgebraCheckers.Patterns
import AlgebraCheckers.Ppr
import AlgebraCheckers.Theorems
import AlgebraCheckers.Types
import AlgebraCheckers.Unification


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

testModel :: ExpQ -> ExpQ
testModel = (testModelImpl =<<)

testModelImpl :: Exp -> ExpQ
testModelImpl e = do
  m <- thisModule
  listE . fmap propTestEq . theorize m $ parseLaws e

parseLaws :: Exp -> [Law LawSort]
parseLaws (DoE z) = concatMap collect z
parseLaws _ = error "you must call parseLaws with a do block"

theoremsOf :: ExpQ -> ExpQ
theoremsOf = (theoremsOfImpl =<<)

theoremsOfImpl :: Exp -> ExpQ
theoremsOfImpl z = do
  md <- thisModule
  let (theorems, problems) = partition (sanityCheck md) $ theorize md $ parseLaws z
      contradicts = filter (maybe False isContradiction . sanityCheck' md) problems
      dodgy       = filter (maybe False isDodgy . sanityCheck' md) problems
  runIO $ do
    putStrLn ""
    printStuff md "Theorems"       theorems
    printStuff md "Dodgy Theorems" dodgy
    printStuff md "Contradictions" contradicts
  listE $ fmap propTestEq $ theorems ++ dodgy ++ contradicts

printStuff :: Module -> String -> [Theorem] -> IO ()
printStuff md sort laws =
  when (not $ null laws) $ do
    putStrLn . render
             $ sep
             $ text (sort ++ ":") : text "" : fmap (showTheorem md) laws
    putStrLn ""
    putStrLn ""

collect :: Stmt -> [Law LawSort]
collect (LawDef lawname exp1 exp2) = [Law (LawName lawname) exp1 exp2]
collect (NotDodgyDef exp1 exp2)    = [Law LawNotDodgy exp1 exp2]
collect (HomoDef ty expr)          = makeHomo ty (knownHomos ty) expr
collect x = error $ show x
  -- "collect must be called with the form [e| law \"name\" (foo a b c == bar a d e) |]"

