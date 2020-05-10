{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module App.Parser
  ( parseAndSubst
  ) where

import App.Types
import Control.Monad
import Data.Bool
import Data.Foldable
import Data.Maybe
import Language.Haskell.Lexer
import Text.Parsec
import Text.Parsec.Pos


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

conid :: Parser String
conid = matchTokenWithStr Conid


nextIndent :: Parser ()
nextIndent = asum
  [ openingButNotEof
  , void $ matchToken $ Open 1
  , eof
  ]

openingButNotEof :: Parser ()
openingButNotEof = void $ matchToken $ Indent 1

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
  (span, _) <- spanning $ manyTill anyToken $ lookAhead nextIndent
  pure $ TypeSigD $ TypeSig name span


parseLaw :: Parser (Decl SourceSpan)
parseLaw = do
  opening
  name <- flip label "rule name" $ stringLit

  (lhs, _) <- spanning $ manyTill (fmap fst anyToken) $ lookAhead eqSym
  eqSym
  (rhs, _) <- spanning $ manyTill (fmap fst anyToken) $ lookAhead nextIndent
  pure $ LawD $ Law name lhs rhs

parseFunModel :: Parser (Decl SourceSpan)
parseFunModel = do
  opening
  modelOf
  (span, name) <- spanning $ do
    name <- varid
    void $ manyTill (fmap fst anyToken) $ lookAhead eqSym
    eqSym
    void $ manyTill (fmap fst anyToken) $ lookAhead nextIndent
    pure name
  pure $ FunModelD $ FunModel name span

parseTypeModel :: Parser (Decl SourceSpan)
parseTypeModel = do
  opening
  modelOf
  name <- conid
  vars <- manyTill varid $ lookAhead eqSym
  eqSym
  (span, name) <- spanning $ do
    void $ manyTill (fmap fst anyToken) $ lookAhead nextIndent
    pure name
  pure $ TypeModelD $ TypeModel name vars span

parseEmptyType :: Parser (Decl SourceSpan)
parseEmptyType = do
  opening
  void $ matchTokenStr Reservedid "type"
  name <- conid
  vars <- many varid
  lookAhead nextIndent
  pure $ EmptyTypeD $ EmptyType name vars

parseOther :: Parser (Decl SourceSpan)
parseOther = do
  openingButNotEof
  (span, _) <- spanning $ manyTill (fmap fst anyToken) $ lookAhead nextIndent
  pure $ Other span

parseOpening :: Parser (Decl SourceSpan)
parseOpening = do
  void $ matchToken $ Open 1
  pure Opening

parseDecl :: Parser (Decl SourceSpan)
parseDecl = asum
  [ try parseEmptyType
  , try parseTypeSig
  , try parseOpening
  , try parseTypeSig
  , try parseFunModel
  , try parseTypeModel
  , try parseLaw
  , parseOther
  ]


parseAndSubst :: String -> Either ParseError [Decl String]
parseAndSubst str
  = fmap (fmap $ fmap $ betweenSpan str)
  . parse (many parseDecl) "test-file"
  $ insertIndents =<< lexerPass1 str

insertIndents :: PosToken -> [PosToken]
insertIndents a@(Open 1, _) = [a, (Indent 1, (Pos 0 0 0, ""))]
insertIndents a = [a]


betweenSpan :: String -> SourceSpan -> String
betweenSpan str (SourceSpan (Pos a _ _) (Pos b _ _)) =
  take (b - a) $ drop a str

