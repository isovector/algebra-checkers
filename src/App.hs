{-# LANGUAGE DeriveFoldable              #-}
{-# LANGUAGE DeriveFunctor               #-}
{-# LANGUAGE DeriveTraversable           #-}
{-# LANGUAGE FlexibleInstances           #-}
{-# LANGUAGE MultiParamTypeClasses       #-}
{-# LANGUAGE TypeFamilies                #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans        #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module App where

import Data.Maybe
import Debug.Trace
import Control.Monad
import Data.Bool
import Language.Haskell.Lexer
import Text.Parsec
import Text.Parsec.Pos
import Text.Parsec.Combinator
import Data.Void
import Data.Foldable


type Parser = Parsec [PosToken] ()

prim :: (PosToken -> Maybe a) -> Parser a
prim = token (snd . snd) (posToSourcePos . fst . snd)

posToSourcePos :: Pos -> SourcePos
posToSourcePos (Pos _ l c) = newPos "" l c

matchToken :: Token -> Parser Token
matchToken t = prim $ bool Nothing (Just t) . (==) t . fst

matchTokenStr :: Token -> String -> Parser Token
matchTokenStr t s = prim $ \(t', (_, s')) ->
  bool Nothing (Just t) $ t == t' && s == s'

matchTokenWithStr :: Token -> Parser String
matchTokenWithStr t = prim $ \(t', (_, s)) -> bool Nothing (Just s) $ (==) t t'

varid :: Parser String
varid = matchTokenWithStr Varid


openingButNotEof :: Parser ()
openingButNotEof = asum
  [ void $ try $ matchToken $ Open 1
  , void $ matchToken $ Indent 1
  ]

opening :: Parser ()
opening = asum
  [ openingButNotEof
  , eof
  ]


typeSym :: Parser ()
typeSym = void $ matchTokenStr Reservedop "::"

eqSym :: Parser ()
eqSym = void $ matchTokenStr Reservedop "="

modelOf :: Parser ()
modelOf = void $ matchTokenStr Varid "μ"

unstringLit :: String -> String
unstringLit = init . drop 1

stringLit :: Parser String
stringLit = fmap unstringLit $ matchTokenWithStr StringLit

getLocation :: Parser Pos
getLocation = do
  (_, (start, _)) <- fmap (maybe (Whitespace, (Pos maxBound 0 0, "")) id . listToMaybe) getInput
  pure start


spanning :: Parser a -> Parser (SourceSpan, a)
spanning p = do
  start <- getLocation
  a <- p
  end <- getLocation
  pure (SourceSpan start end, a)

parseTypeSig :: Parser (Decl SourceSpan)
parseTypeSig = do
  opening
  name <- varid
  typeSym
  (span, _) <- spanning $ manyTill anyToken $ lookAhead opening
  pure $ TypeSig name span


parseLaw :: Parser (Decl SourceSpan)
parseLaw = do
  opening
  name <- flip label "rule name" $ stringLit

  (lhs, _) <- spanning $ manyTill (fmap fst anyToken) $ lookAhead eqSym
  eqSym
  (rhs, _) <- spanning $ manyTill (fmap fst anyToken) $ lookAhead opening
  pure $ Law name lhs rhs


parseModel :: Parser (Decl SourceSpan)
parseModel = do
  opening
  modelOf
  (span, _) <- spanning $ do
    void $ manyTill (fmap fst anyToken) $ lookAhead eqSym
    eqSym
    void $ manyTill (fmap fst anyToken) $ lookAhead opening
  pure $ Model span

parseOther :: Parser (Decl SourceSpan)
parseOther = do
  openingButNotEof
  (span, _) <- spanning $ manyTill (fmap fst anyToken) $ lookAhead opening
  pure $ Other span


data Decl a
  = TypeSig String a
  | Law String a a
  | Model a
  | Other a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

parseDecl :: Parser (Decl SourceSpan)
parseDecl = asum
  [ try parseTypeSig
  , try parseModel
  , try parseLaw
  , parseOther
  ]

data SourceSpan = SourceSpan Pos Pos
  deriving (Eq, Ord, Show)


betweenSpan :: String -> SourceSpan -> String
betweenSpan str (SourceSpan (Pos a _ _) (Pos b _ _)) =
  take (b - a) $ drop a str


parseAndSubst :: String -> Either ParseError [Decl String]
parseAndSubst str
  = fmap (fmap $ fmap $ betweenSpan str)
  . parse (many parseDecl) "test-file"
  $ lexerPass1 str


main :: IO ()
main
  = traverse_ (traverse_ print)
  . parseAndSubst
    =<< readFile "/home/sandy/prj/algebra-checkers/test-file"

