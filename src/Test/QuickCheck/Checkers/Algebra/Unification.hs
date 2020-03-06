{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE ViewPatterns     #-}

module Test.QuickCheck.Checkers.Algebra.Unification where

import Debug.Trace
import           Control.Arrow ((&&&))
import           Control.Monad
import           Control.Monad.Gen
import           Control.Monad.Logic
import           Control.Monad.Trans
import           Data.Foldable
import           Data.Generics.Aliases
import           Data.Generics.Schemes
import qualified Data.Map.Strict     as M
import           Data.Maybe
import           Data.Monoid
import qualified Data.Set            as S
import           Language.Haskell.TH
import System.IO.Unsafe


type Term = Exp
type Id = Name

pattern FreeVar :: Id -> Term
pattern FreeVar n <- VarE (nameModule &&& id -> (Just _, n))
  where
    FreeVar n = VarE n

pattern LocalVar :: Id -> Term
pattern LocalVar n <- VarE (nameModule &&& id -> (Nothing, n))
  where
    LocalVar n = VarE n

pattern Lam :: Id -> Term -> Term
pattern Lam n e = LamE [VarP n] e


-- | Substitute a term for the de Bruijn variable @i@.
subst :: Term -> Id -> Term -> Term
subst new i = everywhere $ mkT $ \case
  LocalVar j | i == j -> new
  x -> x

-- | Substitute a term for all metavariables with a given identifier.
substMV :: Term -> Id -> Term -> Term
substMV new i = everywhere $ mkT $ \case
  UnboundVarE j | i == j -> new
  x -> x


metavars :: Exp -> S.Set Name
metavars = everything (<>) $
  mkQ mempty $ \case
    UnboundVarE n -> S.singleton n
    _ -> mempty

-- | Returns @True@ if a term has no free variables and is therefore a
-- valid candidate for a solution to a metavariable.
isClosed :: Term -> Bool
isClosed = getAll . everything (<>) (
  mkQ mempty $ \case
    FreeVar _ -> All False
    _         -> All True
                                    )

-- | Implement reduction for the language. Given a term, normalize it.
-- This boils down mainly to applying lambdas to their arguments and all
-- the appropriate congruence rules.
reduce :: Term -> Term
reduce = everywhere $ mkT $ \case
  AppE (Lam name body) r -> reduce (subst r name body)
  x -> x

-- | Check to see if a term is blocked on applying a metavariable.
isStuck :: Term -> Bool
isStuck UnboundVarE {} = True
isStuck (AppE f _) = isStuck f
isStuck _ = False

-- | Turn @f a1 a2 a3 a4 ... an@ to @(f, [a1...an])@.
peelApTelescope :: Term -> (Term, [Term])
peelApTelescope t = go t []
  where go (AppE f r) rest = go f (r : rest)
        go t rest = (t, rest)

-- | Turn @(f, [a1...an])@ into @f a1 a2 a3 a4 ... an@.
applyApTelescope :: Term -> [Term] -> Term
applyApTelescope = foldl' AppE

-------------------------------------------------------------------
---------------- the actual unification code ----------------------
-------------------------------------------------------------------

type UnifyM = LogicT Q
type Constraint = (Term, Term)

-- | Given a constraint, produce a collection of equivalent but
-- simpler constraints. Any solution for the returned set of
-- constraints should be a solution for the original constraint.
simplify :: Constraint -> UnifyM (S.Set Constraint)
simplify (t1, t2)
  | t1 == t2 && S.null (metavars t1) = return S.empty
  | reduce t1 /= t1 = simplify (reduce t1, t2)
  | reduce t2 /= t2 = simplify (t1, reduce t2)
  | (FreeVar i, cxt) <- peelApTelescope t1,
    (FreeVar j, cxt') <- peelApTelescope t2 = do
      guard (i == j && length cxt == length cxt')
      fold <$> mapM simplify (zip cxt cxt')
  | Lam l1 body1 <- t1,
    Lam l2 body2 <- t2 = do
      v <- FreeVar <$> lift (newName "x")
      return $ S.singleton (subst v l1 body1, subst v l2 body2)
  | otherwise =
    if isStuck t1 || isStuck t2
       then return $ S.singleton (t1, t2)
       else -- mzero
        trace (unlines [show t1, show t2]) mzero

type Subst = M.Map Id Term

-- | Generate all possible solutions to flex-rigid equations as an
-- infinite list of computations producing finite lists.
tryFlexRigid :: Constraint -> [UnifyM [Subst]]
tryFlexRigid (t1, t2)
  | (UnboundVarE i, cxt1) <- peelApTelescope t1,
    (stuckTerm, cxt2) <- peelApTelescope t2,
    not (i `S.member` metavars t2) = proj (length cxt1) i stuckTerm 0
  | (UnboundVarE i, cxt1) <- peelApTelescope t2,
    (stuckTerm, cxt2) <- peelApTelescope t1,
    not (i `S.member` metavars t1) = proj (length cxt1) i stuckTerm 0
  | otherwise = trace "done" []
  where
    proj :: Int -> Id -> Term -> Int -> [UnifyM [Subst]]
    proj bvars mv e@(ConE {}) nargs = pure $ pure $ pure $ M.singleton mv e
    proj bvars mv e@(LitE {}) nargs = pure $ pure $ pure $ M.singleton mv e
    proj bvars mv e@(FreeVar {}) nargs = pure $ pure $ pure $ M.singleton mv e
    proj bvars mv f nargs = trace (show f) $ proj2 bvars mv f nargs

    proj2 :: Int -> Id -> Term -> Int -> [UnifyM [Subst]]
    proj2 bvars mv f nargs =
      generateSubst bvars mv f nargs : proj2 bvars mv f (nargs + 1)

    generateSubst :: Int -> Id -> Term -> Int -> UnifyM [Subst]
    generateSubst bvars mv f nargs = do
      let mkLam tm = foldr ($) tm (replicate bvars (Lam (mkName "x") ))
      let saturateMV tm = foldl' AppE tm (map (LocalVar . mkName . ("arg"++) . show) [0..bvars - 1])
      let mkSubst = M.singleton mv
      args <- map saturateMV . map UnboundVarE <$> replicateM nargs (lift $ newName "x")
      return [mkSubst . mkLam $ applyApTelescope t args
             | t <- map (LocalVar . mkName . ("arg"++) . show) [0..bvars - 1] ++
                        if isClosed f then [f] else []]

-- | The reflexive transitive closure of @simplify@
repeatedlySimplify :: S.Set Constraint -> UnifyM (S.Set Constraint)
repeatedlySimplify cs = do
  cs' <- fold <$> traverse simplify (S.toList cs)
  if cs' == cs then return cs else repeatedlySimplify cs'

manySubst :: Subst -> Term -> Term
manySubst s t = M.foldrWithKey (\mv sol t -> substMV sol mv t) t s

(<+>) :: Subst -> Subst -> Subst
s1 <+> s2 | not (M.null (M.intersection s1 s2)) = error "Impossible"
s1 <+> s2 = M.union (manySubst s1 <$> s2) s1

-- | The top level function, given a substitution and a set of
-- constraints, produce a solution substution and the resulting set of
-- flex-flex equations.
unify :: Subst -> S.Set Constraint -> UnifyM (Subst, S.Set Constraint)
unify s cs = do
  let cs' = applySubst s cs
  cs'' <- repeatedlySimplify cs'
  let (flexflexes, flexrigids) = S.partition flexflex cs''
  if S.null flexrigids
    then return (s, flexflexes)
    else do
      let psubsts = tryFlexRigid (S.findMax flexrigids)
      trySubsts psubsts (flexrigids <> flexflexes)
  where
    applySubst s = S.map (\(t1, t2) -> (manySubst s t1, manySubst s t2))
    flexflex (t1, t2) = isStuck t1 && isStuck t2

    trySubsts
        :: [UnifyM [Subst]]
        -> S.Set Constraint
        -> UnifyM (Subst, S.Set Constraint)
    trySubsts [] cs
      | [(UnboundVarE n, expr)] <- S.toList cs =
        case (null $ metavars expr) of
          True -> pure $ (M.singleton n expr, mempty)
          False -> pure (mempty, cs)
      | [(expr, UnboundVarE n)] <- S.toList cs =
        case (null $ metavars expr) of
          True -> pure $ (M.singleton n expr, mempty)
          False -> pure (mempty, cs)
      | otherwise = mzero
    trySubsts [] cs = trace (show cs) mzero
    trySubsts (mss : psubsts) cs = do
      ss <- mss
      let these = foldr interleave mzero [unify (newS <+> s) cs | newS <- ss]
      let those = trySubsts psubsts cs
      these `interleave` those

runUnifyM :: UnifyM a -> IO [a]
runUnifyM = runQ . observeAllT

-- | Solve a constraint and return the remaining flex-flex constraints
-- and the substitution for it.
driver :: Constraint -> IO (Maybe (Subst, S.Set Constraint))
driver = fmap listToMaybe . runUnifyM . unify M.empty . S.singleton

x :: Exp
x = unsafePerformIO $ runQ $ [| S.insert 9 (S.insert 0 0) |]

y :: Exp
y = unsafePerformIO $ runQ $ [| S.insert 8 f |]

main :: IO ()
main = print =<< driver (x, y)

