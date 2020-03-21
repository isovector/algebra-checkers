{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TupleSections    #-}

module AlgebraCheckers.Typechecking where

import           AlgebraCheckers.Unification (unboundVars)
import           Control.Monad
import qualified Data.Map as M
import           Data.Traversable
import           Debug.Trace
import           Language.Haskell.TH.Datatype (applySubstitution)
import           Language.Haskell.TH.Lib
import           Language.Haskell.TH.Ppr
import           Language.Haskell.TH.Syntax
import           Language.Haskell.TH.Typecheck

type Scope = M.Map Name Type


instantiate' :: MonadTc m => Type -> m Type
instantiate' (ForallT tys _ t) = do
  let names = fmap bndrName tys
  tys' <- for names $ \name -> (name, ) <$> freshTy
  let sub = applySubstitution (M.fromList tys')

  t' <- instantiate' t
  pure $ sub t'
instantiate' (a :-> b) = (a :->) <$> instantiate b
instantiate' t = pure t


typecheck :: MonadTc m => Scope -> Exp -> m Type
typecheck scope = (substZonked =<<) . \case
  UnboundVarE n -> pure $ scope M.! n
  ConE n -> do
    qReify n >>= \case
      DataConI _ t _ -> instantiate' t
      x -> error $ mappend "ConE " $ show x
  VarE n -> do
    qReify n >>= \case
      VarI _ t _ -> instantiate' t
      ClassOpI _ t _ -> instantiate' t
      x -> error $ mappend "VarE " $ show x
  AppE f a -> do
    t <- freshTy
    ft <- typecheck scope f
    at <- typecheck scope a
    unifyTy t =<< mkAppTy ft at
    pure t
  LitE (CharL _) -> pure $ ConT ''Char
  LitE (StringL _) -> pure $ ConT ''String
  LitE (IntegerL _) -> freshTy
  LitE (RationalL _) -> freshTy
  LitE t -> error $ mappend "LitE" $ show t
  AppTypeE e t -> do
    et <- typecheck scope e
    unifyTy et t
    pure t
  InfixE (Just e1) op (Just e2) -> do
    t <- freshTy
    opt <- typecheck scope op
    e1t <- typecheck scope e1
    e2t <- typecheck scope e2

    t1 <- mkAppTy opt e1t
    t2 <- mkAppTy t1 e2t
    unifyTy t t2
    pure t2
  ParensE e -> typecheck scope e
  x -> error $ mappend "typecheck" $ show x

freshTy :: MonadTc m => m Type
freshTy = VarT <$> freshUnifTV

mkAppTy :: MonadTc m => Type -> Type -> m Type
mkAppTy (ForallT tys c ty) a = do
  killForall . ForallT tys c <$> mkAppTy ty a
mkAppTy (th :-> tb) a = do
  unifyTy th a
  pure tb
mkAppTy x _ = error $ mappend "mkAppTy " $ show x

bndrName :: TyVarBndr -> Name
bndrName (PlainTV n) = n
bndrName (KindedTV n _) = n


inferUnboundVars :: Exp -> Q Scope
inferUnboundVars e = runTc $ do
  let unbound = unboundVars e
  vars <-
    fmap M.fromList $ for unbound $ \var -> do
      t <- freshTy
      pure (var, t)
  void $ typecheck vars e
  traverse substZonked vars


testIt2 :: Q Exp -> Q Exp
testIt2 qe = do
  e <- qe
  t <- inferUnboundVars e
  litE $ stringL $ show t


testIt :: Q Exp -> Q Exp
testIt qe = do
  e <- qe
  traceM $ show e
  t <- runTc $ substZonked =<< typecheck mempty e
  litE $ stringL $ show $ ppr t

killForall :: Type -> Type
killForall (ForallT [] _ t) = t
killForall t = t


pattern (:->) :: Type -> Type -> Type
pattern t :-> ts <- AppT (AppT ArrowT t) ts
  where
    t :-> ts = AppT (AppT ArrowT t) ts

