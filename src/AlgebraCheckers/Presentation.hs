{-# LANGUAGE  TupleSections      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module AlgebraCheckers.Presentation where

import           AlgebraCheckers.Types
import           AlgebraCheckers.Unification
import           Algorithm.Search
import           Control.Arrow
import           Control.Monad
import           Data.Data
import           Data.Foldable
import           Data.Generics.Aliases
import           Data.Generics.Schemes
import           Data.Ord (comparing)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Traversable
import           Debug.Trace
import           Language.Haskell.TH



isWhnf :: Exp -> Bool
isWhnf (ConE _)                            = True
isWhnf (TupE _)                            = True
isWhnf (ListE _)                           = True
isWhnf (LitE _)                            = True
isWhnf (AppE exp1 _)                       = isWhnf exp1
isWhnf (InfixE (Just _) (ConE _) (Just _)) = True
isWhnf _                                   = False

hasEliminated :: S.Set Name -> Exp -> Bool
hasEliminated ns (VarE e) = S.member e ns
hasEliminated _ _ = False

swapLaw :: Law a -> Law a
swapLaw (Law a b c) = Law a c b

bothWays :: Law a -> [Law a]
bothWays l = [l, swapLaw l]


countCons :: Data a => a -> Int
countCons = everything (+) $ mkQ 0 $
  \case
    ConE _ -> 1
    _      -> 0


-- | The resulting score is the expected gain from moving left to right. That
-- is, this is a negative cost!
scoreLaw :: Law a -> Law Int
scoreLaw (Law _ lhs rhs) =
  let lexps = length $ subexps lhs
      rexps = length $ subexps rhs
      lcons = countCons lhs
      rcons = countCons rhs
   in Law (rexps - lexps + (rcons - lcons) * 5) lhs rhs

weightLaws :: [Law Int] -> [Law Int]
weightLaws laws =
  let smallest = lawData $ minimumBy (comparing lawData) laws
   in fmap (modifyLawData ((+ 1) . subtract smallest)) laws


presentationEdges :: [Law a] -> Exp -> [Exp]
presentationEdges theorems e = do
  law <- theorems
  z <- applyLaw law e
  pure z

presentationEdges' :: [Law Int] -> Exp -> [(Int, Exp)]
presentationEdges' theorems e = do
  law <- theorems
  z <- applyLaw law e
  pure (lawData law, z)


boundedDfs
  :: (Foldable f, Ord state)
  => Int  -- ^ max depth
  -> (state -> f state)
  -> (state -> Bool)
  -> state
  -> Maybe [state]
boundedDfs d e f i = fmap (fmap snd) $
  dfs
    (\(ix, s) ->
      case ix >= d of
        True  -> []
        False -> fmap (ix + 1, ) $ toList $ e s)
    (f . snd)
    (0 :: Int, i)


betterDijkstra
    :: (Foldable f, Num cost, Ord cost, Ord state)
    => (state -> f (cost, state))
    -> (state -> Bool)
    -> state
    -> Maybe (cost, [state])
betterDijkstra e s i
  = fmap (second $ fmap snd)
  $ dijkstra (e . snd) (const fst) (s . snd) (0, i)


dumb :: [Theorem] -> (S.Set Name, Exp) -> Maybe [Exp]
dumb ts (bound, e) = boundedDfs 3 (presentationEdges ts) (\x -> isWhnf x || hasEliminated bound x) e

smarter :: [Theorem] -> (S.Set Name, Exp) -> Maybe [Exp]
smarter ts (bound, e) =
  let ws = weightLaws $ fmap scoreLaw ts
   in fmap snd $ betterDijkstra (presentationEdges' ws) (\x -> isWhnf x || hasEliminated bound x) e


fnArity :: Type -> Int
fnArity (ForallT _ _ t) = fnArity t
fnArity (_ :-> b) = 1 + fnArity b
fnArity _ = 0

mkExpr :: Exp -> Int -> Q (S.Set Name, Exp)
mkExpr h t = do
  ns <- replicateM t $ newName "x"
  let es = VarE <$> ns
  pure $ (S.fromList ns, foldl' AppE h es)

algebra
    :: [Name]  -- ^ algebra names
    -> Name    -- ^ potential presentation
    -> Q [(Set Name, Exp)]
algebra alg pres = do
  TyConI (DataD _ _ _ _ cons _) <- reify pres
  con_exps <-
    for cons $ \(NormalC n args) ->
      mkExpr (ConE n) $ length args
  heads <-
    for alg $ \method -> do
      VarI n ty _ <- reify method
      case fnArity ty of
        0 -> pure []
        nargs ->
          for con_exps $ \(bound, con) ->
            fmap (first (bound <>)) $ mkExpr (VarE method `AppE` con) (nargs - 1)
  pure $ join heads


