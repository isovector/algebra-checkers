{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns     #-}

{-# OPTIONS_HADDOCK not-home #-}

module AlgebraCheckers.TH where

import           AlgebraCheckers.Homos
import           AlgebraCheckers.Patterns
import           AlgebraCheckers.Ppr
import           AlgebraCheckers.Theorems
import           AlgebraCheckers.Typechecking
import           AlgebraCheckers.Types
import           AlgebraCheckers.Unification
import           Control.Arrow (second)
import           Control.Monad
import           Data.Bool
import           Data.List (partition)
import qualified Data.Map as M
import           Data.Traversable
import           Language.Haskell.TH hiding (ppr, Arity)
import           Language.Haskell.TH.Syntax (lift, Module)
import           Prelude hiding (exp)
import           Test.QuickCheck hiding (collect)
import           Test.QuickCheck.Checkers ((=-=))


showTheorem :: Bool -> Module -> CheckedTheorem -> Doc
showTheorem c _md thm =
  case snd $ lawData thm of
    Just contradiction ->
      showContradictoryTheorem c thm contradiction
    Nothing -> showSaneTheorem c thm

mkPattern :: M.Map Name Type -> Name -> Type -> PatQ
mkPattern defs nm ty = do
  let mono = monomorphize defs ty
  case mono == ty of
    True  -> varP nm
    False -> sigP (varP nm) $ pure mono


propTestEq :: M.Map Name Type -> CheckedTheorem -> ExpQ
propTestEq defs t@(Law _ exp1 exp2) = do
  md <- thisModule
  eq2exp <- [e| $(pure exp1) `eq2` $(pure exp2) |]
  (M.toList -> inferred, AppT _ z)
      <- fmap (second $ monomorphize defs) $ inferUnboundVarsAndTypecheck eq2exp
  pats <-
    for inferred $ \(var, ty) -> do
      mkPattern defs var ty

  [e|
    ($(lift $ render $ showTheorem False md t)
      , counterexample $(lift $ render $ showTheorem False md t) $
          property $(lamE (fmap pure pats) [e|
           ($(pure exp1) :: $(pure z)) =-= ($(pure exp2) :: $(pure z))
      |]))
    |]


buildPropTests :: M.Map Name Type -> [CheckedTheorem] -> Q [Exp]
buildPropTests defs ts = do
  traverse (propTestEq defs) ts


parseLaws :: Exp -> [Theorem]
parseLaws (DoE z) = concatMap collect z
parseLaws _ = error "you must call parseLaws with a do block"

constructLaws :: Exp -> Q [CheckedTheorem]
constructLaws z = do
  md <- thisModule
  let parsed = parseLaws z
  let unknown = join $ do
        Law _ a b <- parsed
        pure $ unknownVars a ++ unknownVars b
  unless (null unknown) $
    fail $ "Unknown variables: " ++ show unknown
  let ths = theorize md $ fmap (sanityCheck md) $ parsed
  let (theorems, contradicts) = partition isSane ths
  runIO $ do
    putStrLn ""
    printStuff md "Theorems"       theorems
    printStuff md "Contradictions" contradicts
  pure $ theorems ++ contradicts

emitProperties :: M.Map Name Type -> [CheckedTheorem] -> ExpQ
emitProperties defs laws = do
  tests <- buildPropTests defs laws
  listE $ fmap pure tests

printStuff :: Module -> String -> [CheckedTheorem] -> IO ()
printStuff md sort laws =
  when (not $ null laws) $ do
    putStrLn . render
             $ sep
             $ text (sort ++ ":") : text "" : fmap (showTheorem True md) laws
    putStrLn ""
    putStrLn ""

collect :: Stmt -> [Theorem]
collect (LawDef lawname exp1 exp2) = [Law (LawDefn lawname) exp1 exp2]
collect (HomoDef ty bndr expr)     = makeHomo ty (knownHomos ty) bndr expr
collect x = error $ show x
  -- "collect must be called with the form [e| law \"name\" (foo a b c == bar a d e) |]"

