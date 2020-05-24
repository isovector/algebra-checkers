{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}

module AlgebraCheckers.Unification where

import           AlgebraCheckers.Utils
import           Control.Applicative
import           Control.Monad.State
import           Control.Monad.Trans.Writer
import           Data.Char
import           Data.Data
import           Data.Function
import           Data.Generics.Aliases
import           Data.Generics.Schemes
import qualified Data.Map as M
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import           Prelude hiding (exp)
import           {-# SOURCE #-} AlgebraCheckers.Types


data SubExp = SubExp
  { seExp  :: Exp
  , seSubId :: Int
  } deriving (Eq, Ord, Show)


deModuleName :: Data a => a -> a
deModuleName = everywhere $ mkT $ \case
  NameQ _ -> NameS
  NameG _ _ _ -> NameS
  n       -> n


varsToQuantify :: Exp -> [Name]
varsToQuantify = everything (++) $
  mkQ [] $ \case
    UnboundVarE n
      | length (dropEndWhile isPrimeChar $ nameBase n) <= 2 -> [n]
    _ -> []

unboundVars :: Exp -> [Name]
unboundVars = everything (++) $
  mkQ [] $ \case
    UnboundVarE n -> [n]
    _ -> []

unknownVars :: Exp -> [Name]
unknownVars e =
  let to_quantify = varsToQuantify e
   in filter (not . flip elem to_quantify) $ unboundVars e

isPrimeChar :: Char -> Bool
isPrimeChar '\'' = True
isPrimeChar c    = isDigit c


------------------------------------------------------------------------------
-- | Operates over UnboundVarEs
bindVars :: Data a => M.Map Name Exp -> a -> a
bindVars m = everywhere $ mkT $ \case
  e@(UnboundVarE n) ->
    case M.lookup n m of
      Just e' -> e'
      Nothing -> e
  t -> t


------------------------------------------------------------------------------
-- | Operates over VarEs
rebindVars :: Data a => M.Map Name Exp -> a -> a
rebindVars m = everywhere $ mkT $ \case
  e@(VarE n) ->
    case M.lookup n m of
      Just e' -> e'
      Nothing -> e
  t -> t

sloppyRebindVars :: Data a => M.Map Name Exp -> a -> a
sloppyRebindVars m = everywhere $ mkT $ \case
  e@(VarE n) ->
    case M.lookup (mkName $ nameBase n) m of
      Just e' -> e'
      Nothing -> e
  t -> t


renameVars :: Data a => (String -> String) -> a -> a
renameVars f = everywhere $ mkT $ \case
  UnboundVarE n -> UnboundVarE . mkName . f $ nameBase n
  t -> t


type Subst = M.Map Name Exp

sub :: Data a => Subst -> a -> a
sub = bindVars

unifySub :: Subst -> Exp -> Exp -> Maybe Subst
unifySub s a
  = fmap ((M.map =<< sub) . flip mappend s)
  . on unify (sub s) a



type Critical = (Exp, Exp)

criticalPairs :: Law a -> Law a -> [Critical]
criticalPairs other me = do
  let (otherlhs, otherrhs)
        = renameVars (++ "1") (lawLhsExp other, lawRhsExp other)
      (melhs, merhs)
        = renameVars (++ "2") (lawLhsExp me, lawRhsExp me)

  pat <- subexps melhs
  Just subs <- pure $ unify (seExp pat) otherlhs
  let res = bindVars subs (merhs, replaceSubexp pat (const otherrhs) melhs)
  guard $ uncurry (/=) res
  let (a,b) = res
  pure (b, a)


applyLaw :: Law a -> Exp -> [Exp]
applyLaw law exp = do
  let (lhs, rhs) = (lawLhsExp law, lawRhsExp law)
  pat <- subexps exp
  Just subs <- pure $ unify (seExp pat) lhs
  pure $ replaceSubexp pat (const $ bindVars subs rhs) exp


subexps :: Exp -> [SubExp]
subexps e =
  flip evalState 0 $ execWriterT $
    everywhereM (mkM  $ \e' -> do
      ix <- get
      modify (+1)
      case e' of
        UnboundVarE _ -> pure ()
        se -> tell [(SubExp se ix)]
      pure e'
                             ) e


replaceSubexp :: SubExp -> (Exp -> Exp) -> Exp -> Exp
replaceSubexp (SubExp _ ix) f old =
  flip evalState 0 $
    everywhereM (mkM $ \e' -> do
      ix' <- get
      modify (+1)
      pure $ case ix == ix' of
        True  -> f e'
        False -> e'
                ) old


equalUpToAlpha :: Exp -> Exp -> Bool
equalUpToAlpha a b =
  maybe
    False
    (\subst -> all isUnbound subst
            && uncurry (==) (bindVars subst (a, b)))
    (unify a b)
  where
    isUnbound (UnboundVarE _) = True
    isUnbound _ = False


unify :: Exp -> Exp -> Maybe Subst
unify (ParensE exp1) exp2 = unify exp1 exp2
unify exp1 (ParensE exp2) = unify exp1 exp2
unify (UnboundVarE name) exp = pure $ M.singleton name exp
unify exp (UnboundVarE name) = pure $ M.singleton name exp
unify (AppE f1 exp1) (AppE f2 exp2) = do
  s1 <- unify f1 f2
  s2 <- unifySub s1 exp1 exp2
  pure s2
unify (AppTypeE exp1 t1) (AppTypeE exp2 t2) = do
  guard $ t1 == t2
  unify exp1 exp2
unify (InfixE (Just lhs1) exp1 (Just rhs1))
      (InfixE (Just lhs2) exp2 (Just rhs2)) = do
  s1 <- unify exp1 exp2
  s2 <- unifySub s1 lhs1 lhs2
  s3 <- unifySub s2 rhs1 rhs2
  pure s3
unify (InfixE Nothing exp1 (Just rhs1))
      (InfixE Nothing exp2 (Just rhs2)) = do
  s1 <- unify exp1 exp2
  unifySub s1 rhs1 rhs2
unify (InfixE (Just lhs1) exp1 Nothing)
      (InfixE (Just lhs2) exp2 Nothing) = do
  s1 <- unify lhs1 lhs2
  unifySub s1 exp1 exp2
unify (TupE exps1) (TupE exps2) = do
  guard $ exps1 == exps2
  foldM (uncurry . unifySub) mempty $ zip exps1 exps2
unify (CondE cond1 then1 else1) (CondE cond2 then2 else2) = do
  s1 <- unify cond1 cond2
  s2 <- unifySub s1 then1 then2
  unifySub s2 else1 else2
unify (SigE exp1 t1) (SigE exp2 t2) = do
  guard $ t1 == t2
  unify exp1 exp2
unify a b = do
  guard $ a == b
  pure mempty

