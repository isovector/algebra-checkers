{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE TemplateHaskell  #-}

module AlgebraCheckers.Typechecking where

import Debug.Trace
import Control.Monad
import Data.Traversable
import AlgebraCheckers.Unification (unboundVars)
import qualified Data.Map as M
import Language.Haskell.TH.Typecheck
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Ppr
import Language.Haskell.TH.Datatype (applySubstitution)

type Scope = M.Map Name Type


typecheck :: MonadTc m => Scope -> Exp -> m Type
typecheck scope = \case
  UnboundVarE n -> pure $ scope M.! n
  ConE n -> do
    qReify n >>= \case
      DataConI _ t _ -> instantiate t
      x -> error $ mappend "ConE " $ show x
  VarE n -> do
    qReify n >>= \case
      VarI _ t _ -> instantiate t
      x -> error $ mappend "VarE " $ show x
  AppE f a -> do
    t <- freshTy
    ft <- typecheck scope f
    at <- typecheck scope a
    ft' <- substZonked ft
    unifyTy t =<< mkAppTy ft' at
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
mkAppTy (ForallT tys c (VarT th :-> tb)) a = do
  let sub = applySubstitution (M.singleton th a)
  pure
    $ ForallT (filter ((/= th) . bndrName) tys)
              (fmap sub c)
    $ sub tb
mkAppTy (ForallT tys c ty) a =
  ForallT tys c <$> mkAppTy ty a
mkAppTy (VarT th :-> tb) a = pure $
  applySubstitution (M.singleton th a) tb
mkAppTy (th :-> tb) a = do
  unifyTy th a
  pure tb
mkAppTy x _ = error $ mappend "mkAppTy " $ show x

bndrName :: TyVarBndr -> Name
bndrName (PlainTV n) = n
bndrName (KindedTV n _) = n


inferUnboundVars :: MonadTc m => Exp -> m Scope
inferUnboundVars e = do
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
  t <- runTc $ inferUnboundVars e
  litE $ stringL $ show t


testIt :: Q Exp -> Q Exp
testIt qe = do
  e <- qe
  traceM $ show e
  t <- runTc $ substZonked =<< typecheck mempty e
  litE $ stringL $ show $ ppr t


pattern (:->) :: Type -> Type -> Type
pattern t :-> ts <- AppT (AppT ArrowT t) ts
  where
    t :-> ts = AppT (AppT ArrowT t) ts

