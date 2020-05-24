{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TupleSections    #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module AlgebraCheckers.Typechecking
  ( inferUnboundVarsAndTypecheck
  , typecheck
  , monomorphize
  , pattern (:->)
  , typecheckExp
  ) where

import           AlgebraCheckers.Types
import           AlgebraCheckers.Unification (unboundVars, varsToQuantify)
import           AlgebraCheckers.Utils
import           Data.Foldable
import           Data.Generics.Aliases
import           Data.Generics.Schemes
import qualified Data.Map as M
import           Data.Maybe
import           Data.Traversable
import           Data.Word
import           Language.Haskell.TH.Datatype (applySubstitution)
import           Language.Haskell.TH.Syntax
import           Language.Haskell.TH.Typecheck
import           Test.QuickCheck.Checkers


type Scope = M.Map Name Type

instance EqProp Word8 where
  (=-=) = eq


monomorphize :: M.Map Name Type -> Type -> Type
monomorphize defs = everywhere $ mkT $ \case
  VarT t ->
    case M.lookup (sloppy t) defs of
      Just t' -> t'
      Nothing -> ConT ''Word8
  t -> t


instantiate' :: MonadTc m => Type -> m Type
instantiate' (ForallT tys _ t) = do
  let names = fmap bndrName tys
  tys' <- for names $ \name -> (name, ) <$> freshNamedTy (nameBase name)
  instantiate' $ applySubstitution (M.fromList tys') t
instantiate' (a :-> b) = (a :->) <$> instantiate' b
instantiate' t = pure t


typecheck :: MonadTc m => Scope -> Exp -> m Type
typecheck scope = \case
  UnboundVarE n -> do
    t <- freshTy
    pure $ fromMaybe t $ M.lookup n scope
  ConE n -> do
    qReify n >>= \case
      DataConI _ t _ -> instantiate' t
      x -> error $ mappend "ConE " $ show x
  VarE n -> do
    case M.lookup n scope of
      Just t -> pure t
      Nothing ->
        qReify n >>= \case
          VarI _ t _ -> instantiate' t
          ClassOpI _ t _ -> instantiate' t
          x -> error $ mappend "VarE " $ show x
  AppE f a -> do
    t <- freshTy
    ft <- typecheck scope f
    at <- typecheck scope a
    unifyTy' ft $ at :-> t
    pure t
  LitE (CharL _) -> pure $ ConT ''Char
  LitE (StringL _) -> pure $ ConT ''String
  LitE (IntegerL _) -> freshTy
  LitE (RationalL _) -> freshTy
  LitE t -> error $ mappend "LitE" $ show t
  SigE e t -> do
    et <- typecheck scope e
    unifyTy' et t
    pure t
  InfixE (Just e1) op (Just e2) -> do
    t <- freshTy
    opt <- typecheck scope op
    e1t <- typecheck scope e1
    e2t <- typecheck scope e2

    unifyTy' opt $ e1t :-> e2t :-> t
    pure t
  InfixE (Just e1) op Nothing -> do
    t <- freshTy
    opt <- typecheck scope op
    e1t <- typecheck scope e1
    e2t <- freshTy

    unifyTy' opt $ e1t :-> e2t :-> t
    pure $ e2t :-> t
  InfixE Nothing op (Just e2) -> do
    t <- freshTy
    opt <- typecheck scope op
    e1t <- freshTy
    e2t <- typecheck scope e2

    unifyTy' opt $ e1t :-> e2t :-> t
    pure $ e1t :-> t
  ParensE e -> typecheck scope e
  ListE exps -> do
    t <- freshTy
    innert <- freshTy
    for_ exps $ \e -> do
      et <- typecheck scope e
      unifyTy' innert et
    unifyTy' t $ ListT `AppT` innert
    pure t
  TupE exps -> do
    t <- freshTy
    tts <- for exps $ \e -> do
      typecheck scope e
    unifyTy' t $ foldl AppT (TupleT $ length exps) tts
    pure t
  LamE ps e -> do
    let pns = fmap getVarPat ps
    t <- freshTy
    tps <- for pns $ const freshTy
    et <- typecheck (M.fromList (zip pns tps) <> scope) e
    unifyTy t $ foldr (:->) et tps
    pure t




  x -> error $ mappend "typecheck" $ show x

getVarPat :: Pat -> Name
getVarPat (VarP n) = n
getVarPat p = error $ "getVarPat: requires a variable pattern, got: " ++ show p


freshTy :: MonadTc m => m Type
freshTy = VarT <$> freshUnifTV

freshNamedTy :: MonadTc m => String -> m Type
freshNamedTy str = VarT <$> freshNamedUnifTV str


bndrName :: TyVarBndr -> Name
bndrName (PlainTV n) = n
bndrName (KindedTV n _) = n


inferUnboundVarsAndTypecheck :: Exp -> Q (Scope, Type)
inferUnboundVarsAndTypecheck e = runTc $ do
  let unbound = varsToQuantify e
  vars <-
    fmap M.fromList $ for unbound $ \var -> do
      t <- freshTy
      pure (var, t)
  t <- substZonked =<< typecheck vars e
  sc <- traverse substZonked vars
  pure (sc, t)

typecheckExp :: Exp -> Q Type
typecheckExp e = runTc $ do
  let unbound = unboundVars e
  vars <-
    fmap M.fromList $ for unbound $ \var -> do
      t <- freshTy
      pure (var, t)
  z <- typecheck vars e
  substZonked z


unifyTy' :: MonadTc m => Type -> Type -> m ()
unifyTy' a b = do
  -- traceM $ "unifying " ++ show (ppr a) ++ " = " ++ show (ppr b)
  unifyTy a b

