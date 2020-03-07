{-# LANGUAGE LambdaCase #-}

module Test.QuickCheck.Checkers.Algebra.Unification where

import           Control.Monad
import           Data.Data
import           Data.Function
import           Data.Generics.Aliases
import           Data.Generics.Schemes
import qualified Data.Map as M
import qualified Data.Set as S
import           Language.Haskell.TH
import           Prelude hiding (exp)
import           Test.QuickCheck.Checkers.Algebra.TH
import           Test.QuickCheck.Checkers.Algebra.Types


testy :: Law x -> Maybe [(Name, Exp)]
testy (Law _ _ lhs rhs) = fmap M.toList $ unify lhs rhs


type Subst = M.Map Name Exp

sub :: Data a => Subst -> a -> a
sub = rebindVars

unifySub :: Subst -> Exp -> Exp -> Maybe Subst
unifySub s a b = fmap (s <>) $ on unify (sub s) a b


subexprs :: Exp -> S.Set Exp
subexprs = everything (<>) $ mkQ mempty $ \case
  UnboundVarE _ -> mempty
  e             -> S.singleton e


type Critical = (Exp, Exp)

-- TODO(sandy): ensure different var names
criticalPairs :: Law a -> Law a -> [Critical]
criticalPairs other me = do
  let (otherlhs, otherrhs)
        = renameVars (++ "1") (lawLhsExp other, lawRhsExp other)
      (melhs, merhs)
        = renameVars (++ "2") (lawLhsExp me, lawRhsExp me)

  -- pat <- S.toList $ subexprs me
  Just subs <- pure $ unify otherlhs melhs
  pure $ sub subs (merhs, otherrhs)


data SubExpr = SubExpr
  { seExpr  :: Exp
  , seSubId :: Int
  } deriving (Eq, Ord, Show)


unify :: Exp -> Exp -> Maybe Subst
unify (ParensE exp1) exp2 = unify exp1 exp2
unify exp1 (ParensE exp2) = unify exp1 exp2
unify (UnboundVarE name) exp = pure $ M.singleton name exp
unify exp (UnboundVarE name) = pure $ M.singleton name exp
unify (AppE f1 exp1) (AppE f2 exp2) = do
  s1 <- unify f1 f2
  s2 <- unifySub s1 exp1 exp2
  pure s2
unify (AppTypeE exp1 t1) (AppTypeE exp2 t2) = do
  guard $ t1 == t2
  unify exp1 exp2
unify (InfixE (Just lhs1) exp1 (Just rhs1))
      (InfixE (Just lhs2) exp2 (Just rhs2)) = do
  s1 <- unify exp1 exp2
  s2 <- unifySub s1 lhs1 lhs2
  s3 <- unifySub s2 rhs1 rhs2
  pure s3
unify (InfixE Nothing exp1 (Just rhs1))
      (InfixE Nothing exp2 (Just rhs2)) = do
  s1 <- unify exp1 exp2
  unifySub s1 rhs1 rhs2
unify (InfixE (Just lhs1) exp1 Nothing)
      (InfixE (Just lhs2) exp2 Nothing) = do
  s1 <- unify lhs1 lhs2
  unifySub s1 exp1 exp2
unify (TupE exps1) (TupE exps2) = do
  guard $ exps1 == exps2
  foldM (uncurry . unifySub) mempty $ zip exps1 exps2
unify (CondE cond1 then1 else1) (CondE cond2 then2 else2) = do
  s1 <- unify cond1 cond2
  s2 <- unifySub s1 then1 then2
  unifySub s2 else1 else2
unify (SigE exp1 t1) (SigE exp2 t2) = do
  guard $ t1 == t2
  unify exp1 exp2
unify a b = do
  guard $ a == b
  pure mempty

