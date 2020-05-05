{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans        #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module App where


import Data.Char
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
  pure $ TypeSig name span


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
  (span, name) <- spanning $ do
    name <- conid
    void $ manyTill (fmap fst anyToken) $ lookAhead eqSym
    eqSym
    void $ manyTill (fmap fst anyToken) $ lookAhead nextIndent
    pure name
  pure $ TypeModelD $ TypeModel name span

parseOther :: Parser (Decl SourceSpan)
parseOther = do
  openingButNotEof
  (span, _) <- spanning $ manyTill (fmap fst anyToken) $ lookAhead nextIndent
  pure $ Other span

parseOpening :: Parser (Decl SourceSpan)
parseOpening = do
  void $ matchToken $ Open 1
  pure Opening


data Decl a
  = TypeSig String a
  | LawD (Law a)
  | FunModelD (FunModel a)
  | TypeModelD (TypeModel a)
  | Import a
  | Other a
  | Opening
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Law a = Law String a a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data FunModel a = FunModel String a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data TypeModel a = TypeModel String a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

parseDecl :: Parser (Decl SourceSpan)
parseDecl = asum
  [ try parseOpening
  , try parseTypeSig
  , try parseFunModel
  , try parseTypeModel
  , try parseLaw
  , parseOther
  ]


data StuffMap a = StuffMap
  { smHeader     :: [a]
  , smLaws       :: [Law a]
  , smFunModels  :: [FunModel a]
  , smTypeModels :: [TypeModel a]
  , smOther      :: [Decl a]
  }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Semigroup (StuffMap a) where
  StuffMap a1 b1 c1 d1 e1 <> StuffMap a2 b2 c2 d2 e2 =
    StuffMap (a1 <> a2) (b1 <> b2) (c1 <> c2) (d1 <> d2) (e1 <> e2)

instance Monoid (StuffMap a) where
  mempty = StuffMap mempty mempty mempty mempty mempty

buildStuffMap :: [Decl a] -> StuffMap a
buildStuffMap = foldMap $ \case
  LawD       t -> StuffMap mempty [t] mempty mempty mempty
  FunModelD  t -> StuffMap mempty mempty [t] mempty mempty
  TypeModelD t -> StuffMap mempty mempty mempty [t] mempty
  t            -> StuffMap mempty mempty mempty mempty [t]


addImport :: a -> StuffMap a -> StuffMap a
addImport im sm =
  let (header, rest) = span (not . isOpening) $ smOther sm
   in sm { smOther = mconcat [ header, [Opening, Import im], drop 1 rest ] }

addHeader :: a -> StuffMap a -> StuffMap a
addHeader a sm =
  sm { smHeader = a : smHeader sm }

isOpening :: Decl a -> Bool
isOpening Opening = True
isOpening _       = False


data SourceSpan = SourceSpan Pos Pos
  deriving (Eq, Ord, Show)


betweenSpan :: String -> SourceSpan -> String
betweenSpan str (SourceSpan (Pos a _ _) (Pos b _ _)) =
  take (b - a) $ drop a str


parseAndSubst :: String -> Either ParseError [Decl String]
parseAndSubst str
  = fmap (fmap $ fmap $ betweenSpan str)
  . parse (many parseDecl) "test-file"
  $ insertIndents =<< lexerPass1 str



passThrough :: Decl String -> String
passThrough (TypeSig z m) = mconcat [z, " :: ", m]
passThrough LawD{}        = mempty
passThrough FunModelD{}   = mempty
passThrough TypeModelD{}  = mempty
passThrough (Other m)     = m
passThrough Opening       = mempty
passThrough (Import m)    = "import " ++ m ++ "\n"


dumpStuffMap :: StuffMap String -> String
dumpStuffMap sm =
  unlines
    [ unlines $ smHeader sm
    , foldMap passThrough $ smOther sm
    , "pure []"
    , "prop_laws :: [Property]"
    , "prop_laws = [theoremsOf| do"
    , foldMap dumpLaw $ smLaws sm
    , "|]"
    ]

dropEndWhile :: (a -> Bool) -> [a] -> [a]
dropEndWhile p = foldr (\x xs -> if p x && null xs then [] else x:xs) []

trimTrailingSpace :: String -> String
trimTrailingSpace = dropEndWhile isSpace

dumpLaw :: Law String -> String
dumpLaw (Law name lhs rhs) =
  mconcat
    [ "law "
    , show name
    , " $ ("
    , trimTrailingSpace lhs
    , ") == ("
    , trimTrailingSpace rhs
    , ")\n"
    ]

insertIndents :: PosToken -> [PosToken]
insertIndents a@(Open 1, _) = [a, (Indent 1, (Pos 0 0 0, ""))]
insertIndents a = [a]

main :: IO ()
main
  = traverse_
  ( putStrLn
  . dumpStuffMap
  . addHeader "{-# LANGUAGE TemplateHaskell #-}"
  . addImport "Test.QuickCheck"
  . buildStuffMap
  )
  . parseAndSubst
    =<< readFile "/home/sandy/prj/algebra-checkers/test-file"

