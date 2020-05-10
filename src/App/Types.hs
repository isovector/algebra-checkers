{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module App.Types where

import qualified Data.Map as M
import           Language.Haskell.Lexer
import           Text.Parsec


type Parser = Parsec [PosToken] ()

data Decl a
  = TypeSigD (TypeSig a)
  | LawD (Law a)
  | FunModelD (FunModel a)
  | TypeModelD (TypeModel a)
  | Import a
  | Other a
  | EmptyTypeD EmptyType
  | Opening
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data EmptyType = EmptyType String [String]
  deriving (Eq, Ord, Show)

data TypeSig a = TypeSig String a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Law a = Law String a a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data FunModel a = FunModel String a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data TypeModel a = TypeModel String [String] a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)


data StuffMap a = StuffMap
  { smHeader     :: [a]
  , smLaws       :: [Law a]
  , smFunModels  :: [FunModel a]
  , smTypeModels :: M.Map String (TypeModel a)
  , smOther      :: [Decl a]
  , smSigs       :: [TypeSig a]
  , smEmptyTypes :: [EmptyType]
  }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Semigroup (StuffMap a) where
  StuffMap a1 b1 c1 d1 e1 f1 g1 <> StuffMap a2 b2 c2 d2 e2 f2 g2 =
    StuffMap
      (a1 <> a2)
      (b1 <> b2)
      (c1 <> c2)
      (d1 <> d2)
      (e1 <> e2)
      (f1 <> f2)
      (g1 <> g2)

instance Monoid (StuffMap a) where
  mempty = StuffMap mempty mempty mempty mempty mempty mempty mempty

data SourceSpan = SourceSpan Pos Pos
  deriving (Eq, Ord, Show)

