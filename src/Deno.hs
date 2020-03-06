{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PackageImports        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -Wall              #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

-- {-# OPTIONS_GHC -ddump-splices     #-}

module Deno where

import           Control.Monad.Trans.State
import           Data.Bool
import           Data.Function
import           Data.List (nub)
import qualified Data.Set as S
import           Data.Typeable
import           Data.Word
import           Ok
import           Test.QuickCheck
import           Test.QuickCheck.Checkers





data Bool2 = Bool2
  { runBool2 :: forall r. r -> r -> r
  }

instance Show Bool2 where
  show b2 = runBool2 b2 "false" "true"

instance Eq Bool2 where
  a == b = runBool2 a @Int 0 1 == runBool2 b 0 1

instance Model Bool2 Bool where
  model b2 = runBool2 b2 False True

instance Arbitrary Bool2 where
  arbitrary = oneof $ fmap pure [ Bool2 const, Bool2 $ flip const ]

not2 :: Bool2 -> Bool2
not2 b2 = Bool2 $ \f t -> runBool2 b2 t f

and2 :: Bool2 -> Bool2 -> Bool2
and2 a b = Bool2 $ \f t -> runBool2 a f (runBool2 b f t)

deno_not2 :: Bool2 -> Bool
deno_not2 = not . model

deno_and2 :: Bool2 -> Bool2 -> Bool
deno_and2 x y = model x && model y




instance Model b b' => Model (a -> b) (a -> b') where
  model f = model . f

models
    :: (Model b b', Arbitrary a, EqProp b', Show a)
    => (a -> b')
    -> (a -> b)
    -> TestBatch
models g f =
  ( "denotation"
  , [("semantic eq", model . f =-= g)]
  )


main :: IO ()
main = quickBatch $ mconcat
  [ deno_not2 `models` not2
  , deno_and2 `models` and2
  , ("laws", [("k", confluentModel (commutLaw @Int) onlythreeLaw)])
  ]


instance EqProp a => EqProp (S.Set a) where
  (=-=) = (=-=) `on` S.toList

instance EqProp Word8 where
  (=-=) = (===)



data Foo a = Foo
  { fooMembers     :: [a]
  , fooInsertCount :: Int
  }

instance Show a => Show (Foo a) where
  show = show . fooMembers

instance Arbitrary a => Arbitrary (Foo a) where
  arbitrary = Foo <$> arbitrary <*> pure 0

instance Ord a => Model (Foo a) (S.Set a) where
  model = S.fromList . fooMembers

empty :: Foo a
empty = Foo [] 0

insert :: Eq a => a -> Foo a -> Foo a
insert a (Foo ms c) = Foo (nub $ a : ms) $ c + 1

size :: Foo a -> Int
size (Foo ms _) = length ms

remove :: Eq a => a -> Foo a -> Foo a
remove a (Foo ms c) = Foo (filter (/= a) ms) c



commut :: (Arbitrary a, Ord a) => Gen (Foo a, Foo a)
commut = do
  a <- arbitrary
  b <- arbitrary
  c <- arbitrary
  pure ( insert a $ insert b c
       , insert b $ insert a c
       )


onlythree :: (Arbitrary a, Ord a) => Gen (Foo a, Foo a)
onlythree = do
  a <- arbitrary
  b <- arbitrary
  c <- arbitrary
  pure ( insert a $ insert b $ insert c empty
       , insert b $ insert c empty
       )


data Zoop = One | Two | Three | Four | Five
  deriving (Eq, Ord, Show, Enum, Bounded)

instance EqProp Zoop where
  (=-=) = (===)

instance Arbitrary Zoop where
  arbitrary = oneof $ fmap pure [minBound..maxBound]


nofive :: Gen (Foo Zoop, Foo Zoop)
nofive = do
  a <- arbitrary
  pure ( insert Five a
       , a
       )


liftStateT :: Monad m => (m a -> m b) -> StateT s m a -> StateT s m b
liftStateT f stm = StateT $ \s -> do
  (a, s') <- runStateT stm s
  b <- f $ pure a
  pure $ (b, s')


confluent
    :: (Show x, Eq x, EqProp x)
    => Law x
    -> Law x
    -> Property
confluent (Law c1 law1) (Law c2 law2) | c1 >= c2 =
  property $ flip evalStateT [] $ do
  (l1l@(LawHand _ l1lhs), l1r) <- law1
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
pairwise (LawHand lstr lhs) (LawHand rstr rhs) =
  mconcat
    [ lstr
    , " "
    , bool "/=" "==" $ lhs == rhs
    , " "
    , rstr
    , "\n"
    ]

confluentModel
    :: (Show x, Eq x, EqProp x, Model x' x, Typeable x, Typeable x')
    => Law x'
    -> Law x'
    -> Property
confluentModel law1 law2 = confluent (fmap model law1) (fmap model law2)


commutLaw :: (Typeable z, Show z, Eq z, Arbitrary z) => Law (Foo z)
commutLaw =
  $(lawM [e|
    insert a (insert b c) == insert b (insert a c)
    |])

onlythreeLaw :: (Typeable z, Show z, Eq z, Arbitrary z) => Law (Foo z)
onlythreeLaw =
  $(lawM [e|
    insert a (insert b (insert c empty)) == insert b (insert c empty)
    |])

