module Test.QuickCheck.Checkers.Algebra
  ( Law (..), law
  , checkLaw, checkLawModel
  , confluent
  , confluentModel
  ) where

import Data.Data
import Control.Monad
import Control.Monad.Trans.State
import Data.Bool
import Prelude hiding (exp)
import Test.QuickCheck
import Test.QuickCheck.Checkers
import Test.QuickCheck.Checkers.Algebra.TH
import Test.QuickCheck.Checkers.Algebra.Types


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

