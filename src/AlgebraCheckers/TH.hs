{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_HADDOCK not-home #-}

module AlgebraCheckers.TH where

import qualified Data.Map as M
import AlgebraCheckers.Homos
import AlgebraCheckers.Patterns
import AlgebraCheckers.Ppr
import AlgebraCheckers.Suggestions
import AlgebraCheckers.Theorems
import AlgebraCheckers.Typechecking
import AlgebraCheckers.Types
import Control.Monad
import Data.Bool
import Data.List (partition)
import Data.Traversable
import Language.Haskell.TH hiding (ppr, Arity)
import Language.Haskell.TH.Syntax (lift, Module, putQ, getQ)
import Prelude hiding (exp)
import Test.QuickCheck hiding (collect)
import Test.QuickCheck.Checkers ((=-=))


showTheorem :: Module -> Theorem -> Doc
showTheorem md thm =
  case sanityCheck' md thm of
    Just contradiction ->
      showContradictoryTheorem thm contradiction
    Nothing -> showSaneTheorem thm

mkPattern :: Name -> Type -> PatQ
mkPattern nm ty = do
  let mono = monomorphize ty
  case mono == ty of
    True  -> varP nm
    False -> sigP (varP nm) $ pure mono


propTestEq :: Theorem -> ExpQ
propTestEq t@(Law _ exp1 exp2) = do
  md <- thisModule
  eqexp <- [e| $(pure exp1) =-= $(pure exp2) |]
  inferred <- fmap M.toList $ inferUnboundVars eqexp
  pats <-
    for inferred $ \(var, ty) -> do
      let pat = mkPattern var ty
      isFunctionWithArity 1 ty >>= \case
        True -> conP 'Fn [pat]
        False -> pat

  [e|
    counterexample $(lift $ render $ showTheorem md t) $
      property $(lamE (fmap pure pats) [e|
       $(pure eqexp)
      |])
    |]


------------------------------------------------------------------------------
-- | Generate QuickCheck property tests for the given model.
--
-- ==== __Examples__
--
-- @
--   lawTests :: ['Test.QuickCheck.Property']
--   lawTests = $('theoremsOf' [e| do
--
--   'AlgebraCheckers.law' "commutativity" $ a '+' b '==' b '+' a
--   'AlgebraCheckers.law' "identity" (a '+' 0 '==' a)
--
--   |])
-- @
testModel :: ExpQ -> ExpQ
testModel = (testModelImpl =<<)

testModelImpl :: Exp -> ExpQ
testModelImpl e = do
  m <- thisModule
  let theorems = theorize m $ parseLaws e
  putQ theorems
  listE $ fmap propTestEq theorems

parseLaws :: Exp -> [Law LawSort]
parseLaws (DoE z) = concatMap collect z
parseLaws _ = error "you must call parseLaws with a do block"

------------------------------------------------------------------------------
-- | Like 'testModel', but also interactively dumps all of the derived theorems
-- of your model. This is very helpful for finding dodgy derivations and
-- outright contradictions.
theoremsOf :: ExpQ -> ExpQ
theoremsOf = (theoremsOfImpl =<<)

theoremsOfImpl :: Exp -> ExpQ
theoremsOfImpl z = do
  md <- thisModule
  let ths = theorize md $ parseLaws z
  putQ ths
  let (theorems, problems) = partition (sanityCheck md) ths
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
collect (HomoDef ty bndr expr)     = makeHomo ty (knownHomos ty) bndr expr
collect x = error $ show x
  -- "collect must be called with the form [e| law \"name\" (foo a b c == bar a d e) |]"

suggestions :: DecsQ
suggestions = do
  Just theorems <- getQ @[Theorem]
  md <- thisModule
  sgs <- suggest md theorems
  runIO $ do
    putStrLn $ unlines $ fmap (render . pprSuggestion) sgs

  pure []

suggestionsFor :: [Name] -> DecsQ
suggestionsFor surface = do
  sgs <- suggestFor surface
  runIO $ do
    putStrLn $ unlines $ fmap (render . pprSuggestion) sgs

  pure []


