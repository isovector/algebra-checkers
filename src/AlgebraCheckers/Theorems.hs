{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE ViewPatterns          #-}

module AlgebraCheckers.Theorems where

import Data.Either
import Control.Monad
import Data.Bool
import Data.Char
import Data.Function (on)
import Data.Generics.Schemes (listify)
import Data.List (nub)
import Data.Maybe (isNothing, fromMaybe)
import Data.Semigroup
import Language.Haskell.TH hiding (ppr, Arity)
import Language.Haskell.TH.Syntax (Module)
import Prelude hiding (exp)
import AlgebraCheckers.Suggestions
import AlgebraCheckers.Types
import AlgebraCheckers.Unification


sanityCheck :: Module -> Theorem -> CheckedTheorem
sanityCheck md t = t { lawData = (lawData t, sanityCheck' md t) }

isSane :: CheckedTheorem -> Bool
isSane = isNothing . snd . lawData

sanityCheck' :: Module -> Theorem -> Maybe ContradictionReason
sanityCheck' _md (Law _ lhs rhs) =
  either Just (const Nothing) $ foldr1 (>>)
    [ lift_error UnknownConstructors
        $ fmap (\(UnboundVarE n) -> n)
        $ listify is_unbound_ctor (lhs, rhs)
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
isFullyMatchable (ConE _)                      = True
isFullyMatchable (TupE (sequenceA -> Just es)) = all isFullyMatchable es
isFullyMatchable (ListE es)                    = all isFullyMatchable es
isFullyMatchable (LitE _)                      = True
isFullyMatchable (UnboundVarE _)               = True
isFullyMatchable (AppE (UnboundVarE _) _)      = False
isFullyMatchable (AppE exp1 exp2)              = isFullyMatchable exp1 && isFullyMatchable exp2
isFullyMatchable _                             = False

theorize :: Module -> [CheckedTheorem] -> [CheckedTheorem]
theorize md laws =
  let sane_laws = filter isSane laws
      theorems = do
         l1@Law{lawData = fst -> LawDefn l1name} <- sane_laws
         l2@Law{lawData = fst -> LawDefn l2name} <- sane_laws
         -- guard $ l1 /= l2
         (lhs, rhs) <- criticalPairs l1 l2
         pure $ sanityCheck md $ Law (Interaction l1name l2name) lhs rhs
   in (nub $ laws <> theorems)

matchableAppHead :: Exp -> Maybe Name
matchableAppHead (ConE n)   = Just n
matchableAppHead (AppE f _) = matchableAppHead f
matchableAppHead _          = Nothing

nonlinearFunc :: Module -> Name -> Bool
nonlinearFunc md name = not $ sameModule md name

