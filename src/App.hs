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
  pure $ LawD $ Law name lhs rhs


parseFunModel :: Parser (Decl SourceSpan)
parseFunModel = do
  opening
  modelOf
  (span, name) <- spanning $ do
    name <- varid
    void $ manyTill (fmap fst anyToken) $ lookAhead eqSym
    eqSym
    void $ manyTill (fmap fst anyToken) $ lookAhead opening
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
    void $ manyTill (fmap fst anyToken) $ lookAhead opening
    pure name
  pure $ TypeModelD $ TypeModel name span

parseImport :: Parser (Decl SourceSpan)
parseImport = do
  opening
  void $ matchTokenStr Reservedid "import"
  (span, _) <- spanning $ manyTill (fmap fst anyToken) $ lookAhead opening
  pure $ Import span

parseOther :: Parser (Decl SourceSpan)
parseOther = do
  openingButNotEof
  (span, _) <- spanning $ manyTill (fmap fst anyToken) $ lookAhead opening
  pure $ Other span


data Decl a
  = TypeSig String a
  | LawD (Law a)
  | FunModelD (FunModel a)
  | TypeModelD (TypeModel a)
  | Import a
  | Other a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Law a = Law String a a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data FunModel a = FunModel String a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data TypeModel a = TypeModel String a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

parseDecl :: Parser (Decl SourceSpan)
parseDecl = asum
  [ try parseTypeSig
  , try parseFunModel
  , try parseTypeModel
  , try parseLaw
  , try parseImport
  , parseOther
  ]


data StuffMap a = StuffMap
  { smLaws       :: [Law a]
  , smFunModels  :: [FunModel a]
  , smTypeModels :: [TypeModel a]
  , smOther      :: [Decl a]
  }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Semigroup (StuffMap a) where
  StuffMap a1 b1 c1 d1 <> StuffMap a2 b2 c2 d2 =
    StuffMap (a1 <> a2) (b1 <> b2) (c1 <> c2) (d1 <> d2)

instance Monoid (StuffMap a) where
  mempty = StuffMap mempty mempty mempty mempty

buildStuffMap :: [Decl a] -> StuffMap a
buildStuffMap = foldMap $ \case
  LawD       t -> StuffMap [t] mempty mempty mempty
  FunModelD  t -> StuffMap mempty [t] mempty mempty
  TypeModelD t -> StuffMap mempty mempty [t] mempty
  t            -> StuffMap mempty mempty mempty [t]


-- TODO(sandy): Does the wrong thing if there are no imports.
insertImport :: a -> StuffMap a -> StuffMap a
insertImport im sm =
  let (header, rest) = span (not . isImport) $ smOther sm
   in sm { smOther = mconcat [ header, [Import im], rest ] }

isImport :: Decl a -> Bool
isImport (Import _) = True
isImport _          = False


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



passThrough :: Decl String -> String
passThrough (TypeSig z m) = mconcat [z, " :: ", m]
passThrough LawD{}         = mempty
passThrough FunModelD{}   = mempty
passThrough TypeModelD{}  = mempty
passThrough (Other m)     = m
passThrough (Import m)    = "import " ++ m


dumpStuffMap :: StuffMap String -> String
dumpStuffMap sm =
  unlines
    [ foldMap passThrough $ smOther sm
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


main :: IO ()
main
  = traverse_ (putStrLn . dumpStuffMap . buildStuffMap)
  . parseAndSubst
    =<< readFile "/home/sandy/prj/algebra-checkers/test-file"

