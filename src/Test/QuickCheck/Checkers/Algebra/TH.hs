{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ViewPatterns        #-}

module Test.QuickCheck.Checkers.Algebra.TH where

import Data.Char
import           Control.Monad
import           Data.Bool
import           Data.Function (on)
import           Data.Generics.Schemes (listify)
import qualified Data.Kind as Kind
import           Data.List (nub, foldl', partition)
import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map as M
import           Data.Maybe (isNothing, fromMaybe)
import           Data.Semigroup
import           Data.Traversable
import           Language.Haskell.TH (runQ)
import qualified Language.Haskell.TH as Ppr (ppr)
import           Language.Haskell.TH hiding (ppr, Arity)
import           Language.Haskell.TH.PprLib (to_HPJ_Doc)
import           Language.Haskell.TH.Syntax (lift)
import           Prelude hiding (exp)
import           System.Console.ANSI
import           Test.QuickCheck hiding (collect)
import           Test.QuickCheck.Checkers.Algebra.Types
import           Test.QuickCheck.Checkers.Algebra.Unification
import qualified Text.PrettyPrint.HughesPJ as Ppr
import           Text.PrettyPrint.HughesPJ hiding ((<>))


ppr :: Ppr a => a -> Doc
ppr = to_HPJ_Doc . Ppr.ppr


propTestEq :: Theorem -> ExpQ
propTestEq t@(Theorem _ exp1 exp2) = do
  let vars = nub $ unboundVars exp1 ++ unboundVars exp2
  names <- for vars $ newName . nameBase
  [e|
    counterexample $(lift $ render $ showTheorem t) $
      property $(lamE (fmap varP names) [e|
       $(pure exp1) =-= $(pure exp2)
      |])
    |]

lawConf' :: ExpQ -> ExpQ
lawConf' = (lawConf =<<)

lawConf :: Exp -> ExpQ
lawConf = listE . fmap propTestEq . theorize . parseLaws

parseLaws :: Exp -> [Law]
parseLaws (DoE z) = concatMap collect z
parseLaws _ = error "you must call parseLaws with a do block"

data TheoremSource
  = LawDefn String
  | Interaction String String
  deriving (Eq, Ord, Show)

showTheoremSource :: TheoremSource -> Doc
showTheoremSource (LawDefn n) =
  text "definition of" <+> colorize lawColor (text $ show n)
showTheoremSource (Interaction a b) =
  hsep
    [ text "implied by"
    , colorize lawColor $ text $ show $ min a b
    , text "and"
    , colorize lawColor $ text $ show $ max a b
    ]

lawColor :: Color
lawColor = Yellow


data Theorem = Theorem
  { theoremSort :: TheoremSource
  , theoremLhs  :: Exp
  , theoremRhs  :: Exp
  }

instance Eq Theorem where
  Theorem _ a a' == Theorem _ b b' =
    equalUpToAlpha a b && equalUpToAlpha a' b'

sanityCheck :: Theorem -> Bool
sanityCheck = isNothing . sanityCheck'

sanityCheck' :: Theorem -> Maybe ContradictionReason
sanityCheck' (Theorem _ lhs rhs) =
  either Just (const Nothing) $ foldr1 (>>)
    [ lift_error UnknownConstructors $ fmap (\(UnboundVarE n) -> n) $ listify is_unbound_ctor (lhs, rhs)
    , ensure_bound_matches lhs rhs
    , ensure_bound_matches rhs lhs
    , bool (Left UnequalValues) (Right ()) $
        on (&&) isFullyMatchable lhs rhs `implies` (==) lhs rhs
    , bool (Left UnequalValues) (Right ()) $ fromMaybe True $
        liftM2 (==) (matchableAppHead lhs) (matchableAppHead rhs)
    ]
  where
    is_unbound_ctor (UnboundVarE n) = isUpper . head $ nameBase n
    is_unbound_ctor _ = False

    ensure_bound_matches a b
      = lift_error UnboundMatchableVars
      $ filter (not . exists_in a)
      $ matchableMetaVars b
    lift_error _ [] = Right ()
    lift_error ctor x = Left $ ctor x
    exists_in exp var = not . null $ listify (== var) exp

implies :: Bool -> Bool -> Bool
implies p q = not p || q

  --  in all (exists_in lhs) (matchableMetaVars rhs)
  --  && all (exists_in rhs) (matchableMetaVars lhs)
  --  && bool True (lhs == rhs) (isFullyMatchable lhs && isFullyMatchable rhs)

matchableMetaVars :: Exp -> [Name]
matchableMetaVars (UnboundVarE n) = [n]
matchableMetaVars e =
  case matchableAppHead e of
    Just _ -> go e
    Nothing -> []
  where
    go (exp1 `AppE` exp2) =
      go exp1 ++ matchableMetaVars exp2
    go _ = []

isFullyMatchable :: Exp -> Bool
isFullyMatchable (ConE _) = True
isFullyMatchable (TupE es) = all isFullyMatchable es
isFullyMatchable (ListE es) = all isFullyMatchable es
isFullyMatchable (LitE _) = True
isFullyMatchable (UnboundVarE _) = True
isFullyMatchable (AppE (UnboundVarE _) _) = False
isFullyMatchable (AppE exp1 exp2) = isFullyMatchable exp1 && isFullyMatchable exp2
isFullyMatchable _ = False

theorize :: [Law] -> [Theorem]
theorize laws =
  let law_defs = fmap (\(Law n a b) -> Theorem (LawDefn n) a b) laws
      sane_laws = filter (\(Law _ a b) -> sanityCheck $ Theorem undefined a b) laws
      theorems = do
         l1 <- sane_laws
         l2 <- sane_laws
         guard $ l1 /= l2
         (lhs, rhs) <- criticalPairs l1 l2
         pure $ Theorem (Interaction (lawName l1) (lawName l2)) lhs rhs
   in nub $ law_defs <> theorems


theoremsOf' :: ExpQ -> ExpQ
theoremsOf' = (theoremsOf =<<)


theoremsOf :: Exp -> ExpQ
theoremsOf z = do
  let (theorems, contradicts) = partition sanityCheck $ theorize $ parseLaws z
  runIO $ do
    putStrLn ""
    putStrLn . render $ sep (text "Theorems:" : text "" : fmap showTheorem theorems)
    putStrLn ""
    putStrLn ""
    when (not $ null contradicts) $ do
      putStrLn . render $ sep (text "Contradictions:" : text "" : fmap showTheorem contradicts)
      putStrLn ""
      putStrLn ""
  listE []


colorize :: Color -> Doc -> Doc
colorize c doc
       = zeroWidthText (setSGRCode [SetColor Foreground Vivid c])
  Ppr.<> doc
  Ppr.<> zeroWidthText (setSGRCode [SetDefaultColor Foreground])

deepColorize :: Color -> Doc -> Doc
deepColorize c doc
       = zeroWidthText (setSGRCode [SetColor Foreground Vivid c, SetConsoleIntensity BoldIntensity])
  Ppr.<> doc
  Ppr.<> zeroWidthText (setSGRCode [SetDefaultColor Foreground, SetConsoleIntensity NormalIntensity])

backcolorize :: Color -> Doc -> Doc
backcolorize c doc
       = zeroWidthText (setSGRCode [SetColor Background Dull c])
  Ppr.<> doc
  Ppr.<> zeroWidthText (setSGRCode [SetDefaultColor Background])


showTheorem :: Theorem -> Doc
showTheorem thm@(Theorem n a b) = hang (text "•") 2 $
  sep
  [ case sanityCheck' thm of
      Nothing ->
        hang (colorize exprColor $ ppr $ deModuleName a) 6
          . hang (text "==") 4
          . colorize exprColor
          . ppr
          $ deModuleName b
      Just contradiction ->
        vcat
          [ backcolorize Red $ hang (ppr $ deModuleName a) 6
              . hang (text "==") 4
              . ppr
              $ deModuleName b
          , nest 2 $ pprContradiction contradiction
          ]
  , nest 2 $ parens $ showTheoremSource n
  ]

exprColor :: Color
exprColor = Blue


collect :: Stmt -> [Law]
collect (LawStmt lawname exp1 exp2) = [Law lawname exp1 exp2]
collect (LawDollar lawname exp1 exp2) = [Law lawname exp1 exp2]
collect (Homo ty expr) = makeHomo ty (knownHomos ty) expr
collect (HomoDollar ty expr) = makeHomo ty (knownHomos ty) expr
collect _ = error
  "collect must be called with the form [e| law \"name\" (foo a b c == bar a d e) |]"

pattern LawStmt :: String -> Exp -> Exp -> Stmt
pattern LawStmt lawname exp1 exp2 <- NoBindS
  (      VarE ((==) 'law -> True)
  `AppE` LitE  (StringL lawname)
  `AppE` (InfixE (Just exp1)
                 (VarE ((==) '(==) -> True))
                 (Just exp2)
         )
  )

pattern LawDollar :: String -> Exp -> Exp -> Stmt
pattern LawDollar lawname exp1 exp2 <- NoBindS
  (InfixE
    (Just (  VarE ((==) 'law -> True)
      `AppE` LitE  (StringL lawname)))
    (VarE ((==) '($) -> True))
    (Just (InfixE (Just exp1)
                  (VarE ((==) '(==) -> True))
                  (Just exp2)
          )
    )
  )

pattern Homo :: Name -> Exp -> Stmt
pattern Homo ty expr <- NoBindS
  (      (VarE ((==) 'homo -> True) `AppTypeE` ConT ty)
  `AppE` expr
  )

pattern HomoDollar :: Name -> Exp -> Stmt
pattern HomoDollar ty expr <- NoBindS
  (InfixE
    (Just ((VarE ((==) 'homo -> True) `AppTypeE` ConT ty)))
    (VarE ((==) '($) -> True))
    (Just expr)
  )


law :: String -> Bool -> law
law = undefined

homo
    :: forall (homo :: Kind.Type -> Kind.Constraint) a b law
     . (homo a, homo b)
    => (a -> b)
    -> law
homo = undefined

matchableAppHead :: Exp -> Maybe Name
matchableAppHead (ConE n) = Just n
matchableAppHead (AppE f _) = matchableAppHead f
matchableAppHead _ = Nothing

appHead :: Exp -> Maybe Name
appHead (VarE n) = Just n
appHead (ConE n) = Just n
appHead (AppE f _) = appHead f
appHead _ = Nothing

data Arity = Binary | Prefix Int

aritySize :: Arity -> Int
aritySize Binary = 2
aritySize (Prefix n) = n


makeHomo :: Name -> [(Name, Arity)] -> Exp -> [Law]
makeHomo ty ops (LamE [VarP name] body) =
  let app_head = maybe "<expr>" nameBase $ appHead body
      homo_name = nameBase ty
      hs = fmap (UnboundVarE . mkName . (nameBase name ++) . show)
                [1 .. maximum $ fmap (aritySize . snd) ops]
      mk_lawname fn =
        mconcat
          [ app_head, ":", homo_name, ":", nameBase fn ]
   in flip fmap ops $ \(fn_name, arity) ->
        mkHomo name hs body (mk_lawname fn_name) (VarE fn_name) arity
makeHomo _ _ _ = error "monoidal homomorphism needs a lambda"


mkHomo :: Name -> [Exp] -> Exp -> String -> Exp -> Arity -> Law
mkHomo name (v1:v2:_) body law_name fn Binary =
  let replace x = rebindVars (M.singleton name x) body
   in Law law_name
          (replace $ InfixE (Just v1) fn (Just v2))
          (InfixE (Just $ replace v1)
                  fn
                  (Just $ replace v2))
mkHomo _ _ _ _ _ Binary = error "not enough args to mkHomo"
mkHomo name all_vars body law_name fn (Prefix n)=
  let replace x = rebindVars (M.singleton name x) body
      vars = take n all_vars
   in Law law_name
          (replace $ foldl' AppE fn vars)
          (foldl' AppE fn $ fmap replace vars)


knownHomos :: Name -> [(Name, Arity)]
knownHomos nm
  | nm == ''Semigroup
        = [ ('(<>),   Binary) ]
  | nm == ''Monoid
        = [ ('mempty, Prefix 0)
          , ('(<>),   Binary)
          ]
  | nm == ''Eq
        = [ ('(==), Binary) ]
  | nm == ''Ord
        = [ ('compare, Prefix 2) ]
  | otherwise = error $ "unsupported homo type " ++ show nm


data ContradictionReason
  = UnboundMatchableVars [Name]
  | UnequalValues
  | UnknownConstructors [Name]
  deriving (Eq, Ord, Show)

plural :: String -> String -> [a] -> Doc
plural one _ [_] = text one
plural _ many _  = text many

pprContradiction :: ContradictionReason -> Doc
pprContradiction (UnboundMatchableVars vars) =
  sep
    [ text "the matchable"
    , plural "variable" "variables" vars
    , sep $ punctuate (char ',') $ fmap ppr vars
    , nest 4 $ sep
        [ plural "is" "are" vars
        , text "undetermined"
        ]
    ]
pprContradiction (UnknownConstructors vars) =
  sep
    [ text "the"
    , plural "constructor" "constructors" vars
    , sep $ punctuate (char ',') $ fmap ppr vars
    , nest 4 $ sep
        [ plural "does" "do" vars
        , text "not exist"
        ]
    ]
pprContradiction UnequalValues =
  text "unequal values"

