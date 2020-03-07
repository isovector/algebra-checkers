module Test.QuickCheck.Checkers.Algebra
  ( Law, law
  , checkLaw, checkLawModel
  , confluent
  , confluentModel
  , testy
  ) where

import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           Control.Monad.Trans.Writer.CPS
import           Data.Bool
import           Data.Foldable
import qualified Data.Map as M
import           Data.Typeable
import           Language.Haskell.TH
import           Prelude hiding (exp)
import           Test.QuickCheck
import           Test.QuickCheck.Checkers
import           Test.QuickCheck.Checkers.Algebra.TH
import           Test.QuickCheck.Checkers.Algebra.Types
import Data.Function


liftStateT :: Monad m => (m a -> m b) -> StateT s m a -> StateT s m b
liftStateT f stm = StateT $ \s -> do
  (a, s') <- runStateT stm s
  b <- f $ pure a
  pure $ (b, s')


checkLaw :: (Eq x, EqProp x) => Law x -> Property
checkLaw (Law _ l _ _) = property $ flip evalStateT [] $ do
  (lhs, rhs) <- l
  let debug = pairwise lhs rhs
  pure $ counterexample debug $ lhValue lhs =-= lhValue rhs


checkLawModel :: (Model x' x, Eq x, EqProp x) => Law x' -> Property
checkLawModel = checkLaw . fmap model


confluent
    :: (Show x, Eq x, EqProp x)
    => Law x
    -> Law x
    -> Property
confluent (Law c1 law1 _ _) (Law c2 law2 _ _) | c1 >= c2 =
  property $ flip evalStateT [] $ do
  (l1l, l1r) <- law1
  let l1lhs = lhValue l1l
  l2 <- liftStateT (`suchThatMaybe` ((== l1lhs) . lhValue . fst)) law2
  case l2 of
    Nothing -> discard
    Just (l2l, l2r) -> do
      let debug = mconcat $ zipWith pairwise [l1l, l2l, l1r] [l1r, l2r, l2r]
      pure $ conjoin
        [ counterexample debug $ lhValue l1r =-= lhValue l2r
        ]
confluent l1 l2 = confluent l2 l1


pairwise :: (Eq x, EqProp x) => LawHand x -> LawHand x -> String
pairwise lhs rhs =
  mconcat
    [ lhDescriptor lhs
    , " "
    , bool "/=" "==" $ lhValue lhs == lhValue rhs
    , " "
    , lhDescriptor rhs
    , "\n"
    ]

confluentModel
    :: (Show x, Eq x, EqProp x, Model x' x, Typeable x, Typeable x')
    => Law x'
    -> Law x'
    -> Property
confluentModel law1 law2 = confluent (fmap model law1) (fmap model law2)

testy :: Law x -> Maybe [(Name, Exp)]
testy (Law _ _ lhs rhs) = fmap M.toList $ unify lhs rhs


type Subst = M.Map Name Exp

sub :: Subst -> Exp -> Exp
sub = rebindVars

unifySub :: Subst -> Exp -> Exp -> Maybe Subst
unifySub s a b = fmap (s <>) $ (unify `on` sub s) a b

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

