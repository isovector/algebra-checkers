{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE ViewPatterns          #-}

{-# OPTIONS_HADDOCK not-home #-}

module AlgebraCheckers.Patterns where

import Language.Haskell.TH hiding (ppr, Arity)

pattern NotDodgyParens :: Exp -> Exp -> Stmt
pattern NotDodgyParens exp1 exp2 <- NoBindS
  (      VarE ((==) 'notDodgy -> True)
  `AppE` (InfixE (Just exp1)
                 (VarE ((==) '(==) -> True))
                 (Just exp2)
         )
  )

pattern NotDodgyDollar :: Exp -> Exp -> Stmt
pattern NotDodgyDollar exp1 exp2 <- NoBindS
  (InfixE
    (Just ( VarE ((==) 'notDodgy -> True)))
    (VarE ((==) '($) -> True))
    (Just (InfixE (Just exp1)
                  (VarE ((==) '(==) -> True))
                  (Just exp2)
          )
    )
  )

matchNotDodgy :: Stmt -> Maybe (Exp, Exp)
matchNotDodgy (NotDodgyParens exp1 exp2) = Just (exp1, exp2)
matchNotDodgy (NotDodgyDollar exp1 exp2) = Just (exp1, exp2)
matchNotDodgy _ = Nothing

pattern NotDodgyDef :: Exp -> Exp -> Stmt
pattern NotDodgyDef exp1 exp2 <- (matchNotDodgy -> Just (exp1, exp2))


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


------------------------------------------------------------------------------
-- | Asserts that an algebraic law must hold. This function /must/ be called
-- only in the context of either 'AlgebraCheckers.testModel' or
-- 'AlgebraCheckers.theoremsOf'.
--
-- Any variables that appear in the 'Bool' parameter are considered to be
-- metavariables, and will be varied in the resulting property test.
--
-- The 'Bool' parameter /must/ be an expression of the form @exp1 '==' exp2@
--
-- ==== __Examples__
--
-- @'law' "set/get" $ set x (get x s) '==' s@
--
-- @'law' "set/set" (set x' (set x s) '==' set x' s)@
law
    :: String  -- ^ Name
    -> Bool    -- ^ Law. /This is not any ordinary 'Bool'!/ See the documentation
               -- on 'law' for more information.
    -> law
law =
  error "law may be called only inside of a call to testModel or theoremsOf"


------------------------------------------------------------------------------
-- | Convinces 'AlgebraCheckers.theoremsOf' that the following law is not dodgy,
-- preventing it from appearing in the dodgy theorems list.
--
-- This function does not introduce a new law.
--
-- This function /must/ be called only in the context of either
-- 'AlgebraCheckers.testModel' or 'AlgebraCheckers.theoremsOf'.
notDodgy :: Bool -> law
notDodgy =
  error "notDodgy may be called only inside of a call to testModel or theoremsOf"


------------------------------------------------------------------------------
-- | Asserts that a function should be a homomorphism in the argument described
-- by a lambda.
--
-- This function /must/ be called with a type application describing the desired
-- homomorphism. Acceptable typeclasses are 'Data.Semigroup.Semigroup',
-- 'Monoid', 'Data.Group.Group', 'Eq' and 'Ord'.
--
-- The argument to this function must be a lambda binding a single variable.
--
-- This function introduces a law for every method in the typeclass.
--
-- This function /must/ be called only in the context of either
-- 'AlgebraCheckers.testModel' or 'AlgebraCheckers.theoremsOf'.
--
-- ==== __Examples__
--
-- @'homo' \@'Monoid' $ \s -> set x s@
homo
    :: (homo a, homo b)
    => (a -> b)  -- ^ The function expected to be a homomorphism.
                 -- /This is not any ordinary function!/ See the documentation
                 -- on 'homo' for more information.
    -> law
homo =
  error "homo may be called only inside of a call to testModel or theoremsOf"

