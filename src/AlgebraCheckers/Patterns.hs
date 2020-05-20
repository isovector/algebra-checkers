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

pattern LawEq :: Exp -> Exp -> Exp
pattern LawEq exp1 exp2
  <- InfixE
       (Just exp1)
       (VarE ((==) '(==) -> True))
       (Just exp2)
  where
    LawEq exp1 exp2
      = InfixE
          (Just exp1)
          (VarE '(==))
          (Just exp2)


getArg :: Exp -> Maybe (Exp, Exp)
getArg (InfixE (Just f) (VarE ((==) '($) -> True)) (Just e)) = Just (f, e)
getArg (AppE f e) = Just (f, e)
getArg _ = Nothing

pattern App :: Exp -> Exp -> Exp
pattern App f e <- (getArg -> Just (f, e))
  where
    App f e = AppE f e

getBinderName :: Pat -> Maybe Name
getBinderName (VarP n) = Just n
getBinderName (SigP p _) = getBinderName p
getBinderName _ = Nothing

pattern LawN :: Exp
pattern LawN <- VarE ((==) 'law -> True)

pattern HomoN :: Exp
pattern HomoN <- VarE ((==) 'homo -> True)

pattern TyNameApp :: Exp -> Name -> Exp
pattern TyNameApp e t <- e `AppTypeE` ConT t


pattern StringLit :: String -> Exp
pattern StringLit str = LitE (StringL str)

pattern LawDef :: String -> Exp -> Exp -> Stmt
pattern LawDef name exp1 exp2
  <- NoBindS ((LawN `AppE` StringLit name) `App` LawEq exp1 exp2)


pattern HomoDef :: Name -> Name -> Exp -> Stmt
pattern HomoDef ty var expr
  <- NoBindS (TyNameApp HomoN ty `App` LamE [getBinderName -> Just var] expr)


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
-- @'homo' \@'Monoid' $ \\s -> set x s@
homo
    :: (homo a, homo b)
    => (a -> b)  -- ^ The function expected to be a homomorphism.
                 -- /This is not any ordinary function!/ See the documentation
                 -- on 'homo' for more information.
    -> law
homo =
  error "homo may be called only inside of a call to testModel or theoremsOf"

