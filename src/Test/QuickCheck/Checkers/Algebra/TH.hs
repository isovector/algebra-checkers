{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

module Test.QuickCheck.Checkers.Algebra.TH where

import Control.Monad
import Data.Bool
import Data.Char
import Data.Function (on)
import Data.Generics.Schemes (listify)
import Data.List (nub, partition)
import Data.Maybe (isNothing, fromMaybe)
import Data.Semigroup
import Data.Traversable
import Language.Haskell.TH hiding (ppr, Arity)
import Language.Haskell.TH.Syntax (lift)
import Prelude hiding (exp)
import Test.QuickCheck hiding (collect)
import Test.QuickCheck.Checkers.Algebra.Ppr
import Test.QuickCheck.Checkers.Algebra.Types
import Test.QuickCheck.Checkers.Algebra.Unification
import Test.QuickCheck.Checkers.Algebra.Patterns
import Test.QuickCheck.Checkers.Algebra.Homos


showTheorem :: Theorem -> Doc
showTheorem thm =
  case sanityCheck' thm of
    Just contradiction -> showContradictoryTheorem thm contradiction
    Nothing -> showSaneTheorem thm

propTestEq :: Theorem -> ExpQ
propTestEq t@(Law _ exp1 exp2) = do
  let vars = nub $ unboundVars exp1 ++ unboundVars exp2
  names <- for vars $ newName . nameBase
  [e|
    counterexample $(lift $ render $ showTheorem t) $
      property $(lamE (fmap varP names) [e|
       $(pure exp1) =-= $(pure exp2)
      |])
    |]

lawConf' :: ExpQ -> ExpQ
lawConf' = (lawConf =<<)

lawConf :: Exp -> ExpQ
lawConf = listE . fmap propTestEq . theorize . parseLaws

parseLaws :: Exp -> [NamedLaw]
parseLaws (DoE z) = concatMap collect z
parseLaws _ = error "you must call parseLaws with a do block"

sanityCheck :: Theorem -> Bool
sanityCheck = isNothing . sanityCheck'

sanityCheck' :: Theorem -> Maybe ContradictionReason
sanityCheck' (Law _ lhs rhs) =
  either Just (const Nothing) $ foldr1 (>>)
    [ lift_error UnknownConstructors $ fmap (\(UnboundVarE n) -> n) $ listify is_unbound_ctor (lhs, rhs)
    , ensure_bound_matches lhs rhs
    , ensure_bound_matches rhs lhs
    , bool (Left UnequalValues) (Right ()) $
        on (&&) isFullyMatchable lhs rhs `implies` (==) lhs rhs
    , bool (Left UnequalValues) (Right ()) $ fromMaybe True $
        liftM2 (==) (matchableAppHead lhs) (matchableAppHead rhs)
    ]
  where
    is_unbound_ctor (UnboundVarE n) = isUpper . head $ nameBase n
    is_unbound_ctor _ = False

    ensure_bound_matches a b
      = lift_error UnboundMatchableVars
      $ filter (not . exists_in a)
      $ matchableMetaVars b
    lift_error _ [] = Right ()
    lift_error ctor x = Left $ ctor x
    exists_in exp var = not . null $ listify (== var) exp

implies :: Bool -> Bool -> Bool
implies p q = not p || q

matchableMetaVars :: Exp -> [Name]
matchableMetaVars (UnboundVarE n) = [n]
matchableMetaVars e =
  case matchableAppHead e of
    Just _ -> go e
    Nothing -> []
  where
    go (exp1 `AppE` exp2) =
      go exp1 ++ matchableMetaVars exp2
    go _ = []

isFullyMatchable :: Exp -> Bool
isFullyMatchable (ConE _)                 = True
isFullyMatchable (TupE es)                = all isFullyMatchable es
isFullyMatchable (ListE es)               = all isFullyMatchable es
isFullyMatchable (LitE _)                 = True
isFullyMatchable (UnboundVarE _)          = True
isFullyMatchable (AppE (UnboundVarE _) _) = False
isFullyMatchable (AppE exp1 exp2)         = isFullyMatchable exp1 && isFullyMatchable exp2
isFullyMatchable _                        = False

theorize :: [NamedLaw] -> [Theorem]
theorize laws =
  let law_defs = fmap (\t -> t { lawData = LawDefn $ lawData t }) laws
      sane_laws = filter sanityCheck law_defs
      theorems = do
         l1@Law{lawData = LawDefn l1name} <- sane_laws
         l2@Law{lawData = LawDefn l2name} <- sane_laws
         guard $ l1 /= l2
         (lhs, rhs) <- criticalPairs l1 l2
         pure $ Law (Interaction l1name l2name) lhs rhs
   in nub $ law_defs <> theorems

theoremsOf' :: ExpQ -> ExpQ
theoremsOf' = (theoremsOf =<<)

theoremsOf :: Exp -> ExpQ
theoremsOf z = do
  let (theorems, contradicts) = partition sanityCheck $ theorize $ parseLaws z
  runIO $ do
    putStrLn ""
    putStrLn . render $ sep (text "Theorems:" : text "" : fmap showTheorem theorems)
    putStrLn ""
    putStrLn ""
    when (not $ null contradicts) $ do
      putStrLn . render $ sep (text "Contradictions:" : text "" : fmap showTheorem contradicts)
      putStrLn ""
      putStrLn ""
  listE $ fmap propTestEq theorems

collect :: Stmt -> [NamedLaw]
collect (LawDef lawname exp1 exp2) = [Law lawname exp1 exp2]
collect (HomoDef ty expr)          = makeHomo ty (knownHomos ty) expr
collect _ = error
  "collect must be called with the form [e| law \"name\" (foo a b c == bar a d e) |]"

matchableAppHead :: Exp -> Maybe Name
matchableAppHead (ConE n)   = Just n
matchableAppHead (AppE f _) = matchableAppHead f
matchableAppHead _          = Nothing

