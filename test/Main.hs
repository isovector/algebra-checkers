{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}

{-# OPTIONS_GHC -fno-warn-orphans  #-}
-- {-# OPTIONS_GHC -ddump-splices     #-}

-- module Main where

import           Data.Function
import           Data.List (nub)
import           Data.Monoid
import qualified Data.Set as S
import           Test.QuickCheck
import           Test.QuickCheck.Checkers
import           Test.QuickCheck.Checkers.Algebra.TH


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





-- main :: IO ()
-- main = quickBatch $ mconcat
--   [ deno_not2 `denotationFor` not2
--   , deno_and2 `denotationFor` and2
--   , ("laws", [("k", confluentModel (commutLaw @Int) onlythreeLaw)])
--   ]


instance EqProp a => EqProp (S.Set a) where
  (=-=) = (=-=) `on` S.toList

instance EqProp Any where
  (=-=) = (=-=) `on` getAny



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

get :: Int -> String -> Any
set :: Int -> Any -> String -> String
get = undefined
set = undefined


-- instance Model Bar Bool where
--   model = Temp

class Model a b => Unmodel a b where
  unmodel :: b -> a


lawTests :: [Property]
lawTests = $(theoremsOf'
  [e| do
  law "set/set"     (set i x' (set i x s) == set i x' s)
  law "set/get"    $ set i (get i s) s == s
  law "get/set"     (get i (set i x s) == x)
  homo @Monoid $ \h -> set i x h
  homo @Monoid $ \h -> get i h
  |])

