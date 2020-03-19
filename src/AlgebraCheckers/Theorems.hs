{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TupleSections         #-}

module AlgebraCheckers.Theorems where

import Data.Either
import Control.Monad
import Data.Bool
import Data.Char
import Data.Function (on)
import Data.Generics.Schemes (listify)
import Data.List (nub, (\\))
import Data.Maybe (isNothing, fromMaybe, mapMaybe)
import Data.Semigroup
import Language.Haskell.TH hiding (ppr, Arity)
import Language.Haskell.TH.Syntax (Module)
import Prelude hiding (exp)
import AlgebraCheckers.Homos
import AlgebraCheckers.Suggestions
import AlgebraCheckers.Types
import AlgebraCheckers.Unification


sanityCheck :: Module -> Theorem -> Bool
sanityCheck md = isNothing . sanityCheck' md

sanityCheck' :: Module -> Theorem -> Maybe TheoremProblem
sanityCheck' md (Law _ lhs rhs) =
  either Just (const Nothing) $ foldr1 (>>)
    [ lift_error (Contradiction . UnknownConstructors)
        $ fmap (\(UnboundVarE n) -> n)
        $ listify is_unbound_ctor (lhs, rhs)
    , ensure_bound_matches lhs rhs
    , ensure_bound_matches rhs lhs
    , bool (Left $ Contradiction UnequalValues) (Right ()) $
        on (&&) isFullyMatchable lhs rhs `implies` (==) lhs rhs
    , bool (Left $ Contradiction UnequalValues) (Right ()) $ fromMaybe True $
        liftM2 (==) (matchableAppHead lhs) (matchableAppHead rhs)
    , bool (Right ()) (Left $ Dodgy SelfRecursive) $ nonlinearUse md lhs rhs
    , bool (Right ()) (Left $ Dodgy SelfRecursive) $ nonlinearUse md rhs lhs
    ]
  where
    is_unbound_ctor (UnboundVarE n) = isUpper . head $ nameBase n
    is_unbound_ctor _ = False

    ensure_bound_matches a b
      = lift_error (Contradiction . UnboundMatchableVars)
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

namedLawToEither :: NamedLaw -> Either (Law ()) (Law String)
namedLawToEither (Law (LawName n) a b) = Right (Law n a b)
namedLawToEither (Law LawNotDodgy a b) = Left (Law () a b)

theorize :: Module -> [NamedLaw] -> [Theorem]
theorize md named_laws =
  let (not_dodgy, laws) = partitionEithers $ fmap namedLawToEither named_laws
      law_defs = fmap (\t -> t { lawData = LawDefn $ lawData t }) laws
      sane_laws = filter (sanityCheck md) law_defs
      theorems = do
         l1@Law{lawData = LawDefn l1name} <- sane_laws
         l2@Law{lawData = LawDefn l2name} <- sane_laws
         guard $ l1 /= l2
         (lhs, rhs) <- criticalPairs l1 l2
         pure $ Law (Interaction l1name l2name) lhs rhs
   in (nub $ law_defs <> theorems) \\ fmap (\l -> l {lawData = LawDefn ""} ) not_dodgy

matchableAppHead :: Exp -> Maybe Name
matchableAppHead (ConE n)   = Just n
matchableAppHead (AppE f _) = matchableAppHead f
matchableAppHead _          = Nothing

nonlinearUse :: Module -> Exp -> Exp -> Bool
nonlinearUse md exp1 exp2 =
  let exp2s = mapMaybe (\exp -> splitApps exp) $ fmap seExp $ subexps exp2
   in any (\(apphead, exps) -> nonlinearFunc md apphead && any (equalUpToAlpha exp1) exps) exp2s

nonlinearFunc :: Module -> Name -> Bool
nonlinearFunc _ name
  | name == 'const  = False
  -- | name == 'bool   = False
  | name == 'maybe  = False
  | name == 'either = False
nonlinearFunc md name = not $ sameModule md name

