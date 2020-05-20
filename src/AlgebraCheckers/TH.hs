{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_HADDOCK not-home #-}

module AlgebraCheckers.TH where

-- import Debug.Trace
import qualified Data.Map as M
import AlgebraCheckers.Homos
import AlgebraCheckers.Patterns
import AlgebraCheckers.Ppr
import AlgebraCheckers.Theorems
import AlgebraCheckers.Unification
import AlgebraCheckers.Typechecking
import AlgebraCheckers.Types
import Control.Monad
import Data.Bool
import Data.List (partition)
import Data.Traversable
import Language.Haskell.TH hiding (ppr, Arity)
import Language.Haskell.TH.Syntax (lift, Module)
import Prelude hiding (exp)
import Test.QuickCheck hiding (collect)
import Test.QuickCheck.Checkers ((=-=))


showTheorem :: Bool -> Module -> Theorem -> Doc
showTheorem c md thm =
  case sanityCheck' md thm of
    Just contradiction ->
      showContradictoryTheorem c thm contradiction
    Nothing -> showSaneTheorem c thm

mkPattern :: M.Map Name Type -> Name -> Type -> PatQ
mkPattern defs nm ty = do
  let mono = monomorphize defs ty
  case mono == ty of
    True  -> varP nm
    False -> sigP (varP nm) $ pure mono


propTestEq :: M.Map Name Type -> Theorem -> ExpQ
propTestEq defs t@(Law _ exp1 exp2) = do
  md <- thisModule
  eq2exp <- [e| $(pure exp1) `eq2` $(pure exp2) |]
  -- traceM "starting mono"
  -- traceM $ render $ ppr eq2exp
  AppT _ z <- fmap (monomorphize defs) $ typecheckExp eq2exp
  -- traceM "stopping mono"
  eqexp <- [e| ($(pure exp1) :: $(pure z)) =-= ($(pure exp2) :: $(pure z)) |]
  -- traceM "starting infer"
  inferred <- fmap M.toList $ inferUnboundVars eqexp
  -- traceM "stopping infer"
  pats <-
    for inferred $ \(var, ty) -> do
      mkPattern defs var ty
      -- let pat = mkPattern var ty
      -- isFunctionWithArity 1 ty >>= \case
      --   True -> conP 'Fn [pat]
      --   False -> pat

  [e|
    ($(lift $ render $ showTheorem False md t)
      , counterexample $(lift $ render $ showTheorem False md t) $
          property $(lamE (fmap pure pats) [e|
          $(pure eqexp)
      |]))
    |]


buildPropTests :: M.Map Name Type -> [Theorem] -> Q [Exp]
buildPropTests defs ts = do
  traverse (propTestEq defs) ts


parseLaws :: Exp -> [Law LawSort]
parseLaws (DoE z) = concatMap collect z
parseLaws _ = error "you must call parseLaws with a do block"

constructLaws :: Exp -> Q [Theorem]
constructLaws z = do
  md <- thisModule
  let parsed = parseLaws z
  let unknown = join $ do
        Law _ a b <- parsed
        pure $ unknownVars a ++ unknownVars b
  unless (null unknown) $
    fail $ "Unknown variables: " ++ show unknown
  let ths = theorize md $ parsed
  let (theorems, contradicts) = partition (sanityCheck md) ths
  runIO $ do
    putStrLn ""
    printStuff md "Theorems"       theorems
    printStuff md "Contradictions" contradicts
  pure $ theorems ++ contradicts

emitProperties :: M.Map Name Type -> [Theorem] -> ExpQ
emitProperties defs laws = do
  tests <- buildPropTests defs laws
  listE $ fmap pure tests

printStuff :: Module -> String -> [Theorem] -> IO ()
printStuff md sort laws =
  when (not $ null laws) $ do
    putStrLn . render
             $ sep
             $ text (sort ++ ":") : text "" : fmap (showTheorem True md) laws
    putStrLn ""
    putStrLn ""

collect :: Stmt -> [Law LawSort]
collect (LawDef lawname exp1 exp2) = [Law (LawName lawname) exp1 exp2]
collect (HomoDef ty bndr expr)     = makeHomo ty (knownHomos ty) bndr expr
collect x = error $ show x
  -- "collect must be called with the form [e| law \"name\" (foo a b c == bar a d e) |]"

