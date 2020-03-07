{-# LANGUAGE LambdaCase #-}

module Test.QuickCheck.Checkers.Algebra.Unification where

import Debug.Trace
import Control.Applicative
import Control.Monad.State
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
import Control.Monad.Trans.Writer


testy :: Law x -> Maybe [(Name, Exp)]
testy (Law _ _ lhs rhs) = fmap M.toList $ unify lhs rhs


type Subst = M.Map Name Exp

sub :: Data a => Subst -> a -> a
sub = rebindVars

unifySub :: Subst -> Exp -> Exp -> Maybe Subst
unifySub s a b = fmap (s <>) $ on unify (sub s) a b



type Critical = (Exp, Exp)

-- TODO(sandy): ensure different var names
criticalPairs :: Law a -> Law b -> [Critical]
criticalPairs other me = do
  let (otherlhs, otherrhs)
        = renameVars (++ "1") (lawLhsExp other, lawRhsExp other)
      (melhs, merhs)
        = renameVars (++ "2") (lawLhsExp me, lawRhsExp me)

  pat <- subexps melhs
  Just subs <- pure $ unify (seExp pat) otherlhs
  traceM $ "unified"
  traceM $ pprint (seExp pat)
  traceM $ "with"
  traceM $ pprint otherlhs
  pure $ sub subs (merhs, replaceSubexp pat (const otherrhs) melhs)


data SubExp = SubExp
  { seExp  :: Exp
  , seSubId :: Int
  } deriving (Eq, Ord, Show)


subexps :: Exp -> [SubExp]
subexps e =
  flip evalState 0 $ execWriterT $
    everywhereM (mkM  $ \e' -> do
      ix <- get
      modify (+1)
      case e' of
        UnboundVarE _ -> pure ()
        se -> tell [(SubExp se ix)]
      pure e'
                             ) e


replaceSubexp :: SubExp -> (Exp -> Exp) -> Exp -> Exp
replaceSubexp (SubExp _ ix) f old =
  flip evalState 0 $
    everywhereM (mkM $ \e' -> do
      ix' <- get
      modify (+1)
      pure $ case ix == ix' of
        True  -> f e'
        False -> e'
                ) old


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

pprintcrit :: Critical -> IO ()
pprintcrit (exp1, exp2) = do
  putStrLn $ pprint exp1
  putStrLn $ pprint exp2
  putStrLn ""
  putStrLn ""

