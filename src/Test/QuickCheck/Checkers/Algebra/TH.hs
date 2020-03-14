{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

module Test.QuickCheck.Checkers.Algebra.TH where

import           Control.Monad
import           Data.Bool
import           Data.Char
import           Data.Function (on)
import           Data.Generics.Schemes (listify)
import           Data.List (nub, foldl', partition)
import qualified Data.Map as M
import           Data.Maybe (isNothing, fromMaybe)
import           Data.Semigroup
import           Data.Traversable
import           Language.Haskell.TH hiding (ppr, Arity)
import           Language.Haskell.TH.Syntax (lift)
import           Prelude hiding (exp)
import           Test.QuickCheck hiding (collect)
import           Test.QuickCheck.Checkers.Algebra.Ppr
import           Test.QuickCheck.Checkers.Algebra.Types
import           Test.QuickCheck.Checkers.Algebra.Unification
import           Test.QuickCheck.Checkers.Algebra.Patterns


showTheorem :: Theorem -> Doc
showTheorem thm =
  case sanityCheck' thm of
    Just contradiction -> showContradictoryTheorem thm contradiction
    Nothing -> showSaneTheorem thm

propTestEq :: Theorem -> ExpQ
propTestEq t@(Law _ exp1 exp2) = do
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

parseLaws :: Exp -> [NamedLaw]
parseLaws (DoE z) = concatMap collect z
parseLaws _ = error "you must call parseLaws with a do block"


sanityCheck :: Theorem -> Bool
sanityCheck = isNothing . sanityCheck'

sanityCheck' :: Theorem -> Maybe ContradictionReason
sanityCheck' (Law _ lhs rhs) =
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
isFullyMatchable (ConE _)                 = True
isFullyMatchable (TupE es)                = all isFullyMatchable es
isFullyMatchable (ListE es)               = all isFullyMatchable es
isFullyMatchable (LitE _)                 = True
isFullyMatchable (UnboundVarE _)          = True
isFullyMatchable (AppE (UnboundVarE _) _) = False
isFullyMatchable (AppE exp1 exp2)         = isFullyMatchable exp1 && isFullyMatchable exp2
isFullyMatchable _                        = False

theorize :: [NamedLaw] -> [Theorem]
theorize laws =
  let law_defs = fmap (\t -> t { lawData = LawDefn $ lawData t }) laws
      sane_laws = filter sanityCheck law_defs
      theorems = do
         l1@Law{lawData = LawDefn l1name} <- sane_laws
         l2@Law{lawData = LawDefn l2name} <- sane_laws
         guard $ l1 /= l2
         (lhs, rhs) <- criticalPairs l1 l2
         pure $ Law (Interaction l1name l2name) lhs rhs
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
  listE $ fmap propTestEq theorems




collect :: Stmt -> [NamedLaw]
collect (LawStmt lawname exp1 exp2)   = [Law lawname exp1 exp2]
collect (LawDollar lawname exp1 exp2) = [Law lawname exp1 exp2]
collect (Homo ty expr)                = makeHomo ty (knownHomos ty) expr
collect (HomoDollar ty expr)          = makeHomo ty (knownHomos ty) expr
collect _ = error
  "collect must be called with the form [e| law \"name\" (foo a b c == bar a d e) |]"


matchableAppHead :: Exp -> Maybe Name
matchableAppHead (ConE n)   = Just n
matchableAppHead (AppE f _) = matchableAppHead f
matchableAppHead _          = Nothing

appHead :: Exp -> Maybe Name
appHead (VarE n)   = Just n
appHead (ConE n)   = Just n
appHead (AppE f _) = appHead f
appHead _          = Nothing

aritySize :: Arity -> Int
aritySize Binary     = 2
aritySize (Prefix n) = n


makeHomo :: Name -> [(Name, Arity)] -> Exp -> [NamedLaw]
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


mkHomo :: Name -> [Exp] -> Exp -> String -> Exp -> Arity -> NamedLaw
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


