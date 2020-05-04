{-# LANGUAGE FlexibleInstances           #-}
{-# LANGUAGE MultiParamTypeClasses       #-}
{-# LANGUAGE TypeFamilies                #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans        #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module App where

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


opening :: Parser ()
opening = asum
  [ void $ try $ matchToken $ Open 1
  , void $ matchToken $ Indent 1
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


spanning :: Parser a -> Parser (SourceSpan, a)
spanning p = do
  start <- getPosition
  a <- p
  end <- getPosition
  pure (SourceSpan start end, a)

parseTypeSig :: Parser Decl
parseTypeSig = do
  opening
  name <- varid
  typeSym
  span <- fmap fst $ spanning $ manyTill anyToken $ lookAhead opening
  pure $ TypeSig name span


parseLaw :: Parser Decl
parseLaw = do
  opening
  name <- flip label "rule name" $ stringLit

  void $ manyTill (fmap fst anyToken) $ lookAhead eqSym
  eqSym
  void $ manyTill (fmap fst anyToken) $ lookAhead opening
  pure $ Law name


parseModel :: Parser Decl
parseModel = do
  opening
  modelOf
  void $ manyTill (fmap fst anyToken) $ lookAhead eqSym
  eqSym
  void $ manyTill (fmap fst anyToken) $ lookAhead opening
  pure $ Model


data Decl
  = TypeSig String SourceSpan
  | Law String -- SourcePos SourcePos
  | Model -- SourcePos
  deriving (Eq, Ord, Show)

parseDecl :: Parser Decl
parseDecl = asum
  [ try parseTypeSig
  , try parseModel
  , parseLaw
  ]

data SourceSpan = SourceSpan SourcePos SourcePos
  deriving (Eq, Ord, Show)


main :: IO ()
main
  = traverse_ (traverse_ print)
  . parse (many parseDecl) "test-file"
  . lexerPass1
    =<< readFile "/home/sandy/prj/algebra-checkers/test-file"

