{-# LANGUAGE  TupleSections      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module AlgebraCheckers.Presentation where


import Control.Arrow
import qualified Data.Set as S
import Data.Set (Set)
import Debug.Trace
import Control.Monad
import Data.Traversable
import Data.Foldable
import Algorithm.Search
import AlgebraCheckers.Theorems
import AlgebraCheckers.Types
import AlgebraCheckers.Unification
import Language.Haskell.TH
import Data.Maybe



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


presentationEdges :: [Theorem] -> Exp -> [Exp]
presentationEdges theorems e = do
  -- traceM $ show e
  theorem <- theorems
  law     <- [theorem, swapLaw theorem]
  z <- applyLaw law e
  pure z


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


dumb :: [Theorem] -> (S.Set Name, Exp) -> Maybe [Exp]
dumb ts (bound, e) = boundedDfs 3 (presentationEdges ts) (\x -> isWhnf x || hasEliminated bound x) e


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


