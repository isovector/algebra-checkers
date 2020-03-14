{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE ViewPatterns          #-}

module Test.QuickCheck.Checkers.Algebra.Patterns where

import qualified Data.Kind as Kind
import           Language.Haskell.TH hiding (ppr, Arity)

pattern LawParens :: String -> Exp -> Exp -> Stmt
pattern LawParens lawname exp1 exp2 <- NoBindS
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

matchLaw :: Stmt -> Maybe (String, Exp, Exp)
matchLaw (LawParens name exp1 exp2) = Just (name, exp1, exp2)
matchLaw (LawDollar name exp1 exp2) = Just (name, exp1, exp2)
matchLaw _ = Nothing

pattern LawDef :: String -> Exp -> Exp -> Stmt
pattern LawDef name exp1 exp2 <- (matchLaw -> Just (name, exp1, exp2))


pattern HomoParens :: Name -> Exp -> Stmt
pattern HomoParens ty expr <- NoBindS
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

matchHomo :: Stmt -> Maybe (Name, Exp)
matchHomo (HomoParens ty expr) = Just (ty, expr)
matchHomo (HomoDollar ty expr) = Just (ty, expr)
matchHomo _ = Nothing


pattern HomoDef :: Name -> Exp -> Stmt
pattern HomoDef ty expr <- (matchHomo -> Just (ty, expr))



law :: String -> Bool -> law
law = undefined

homo
    :: forall (homo :: Kind.Type -> Kind.Constraint) a b law
     . (homo a, homo b)
    => (a -> b)
    -> law
homo = undefined
