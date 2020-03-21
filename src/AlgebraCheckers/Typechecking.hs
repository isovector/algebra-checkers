{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TupleSections    #-}

module AlgebraCheckers.Typechecking
  ( inferUnboundVars
  , isFunctionWithArity
  ) where

import Control.Arrow (second)
import Debug.Trace
import           AlgebraCheckers.Unification (unboundVars)
import           Control.Monad
import qualified Data.Map as M
import           Data.Traversable
import           Language.Haskell.TH.Datatype (applySubstitution, resolveTypeSynonyms)
import           Language.Haskell.TH.Syntax
import           Language.Haskell.TH.Typecheck


type Scope = M.Map Name Type


instantiate' :: MonadTc m => Type -> m Type
instantiate' (ForallT tys _ t) = do
  t' <- instantiate' t
  let names = fmap bndrName tys
  tys' <- for names $ \name -> (name, ) <$> freshTy
  pure $ applySubstitution (M.fromList tys') t'
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


killForall :: Type -> Type
killForall (ForallT [] _ t) = t
killForall t = t


pattern (:->) :: Type -> Type -> Type
pattern t :-> ts <- AppT (AppT ArrowT t) ts
  where
    t :-> ts = AppT (AppT ArrowT t) ts


headAppT :: Type -> Maybe (Name, [Type])
headAppT (ConT n) = Just (n, [])
headAppT (AppT a t) = fmap (second (++ [t])) (headAppT a)
headAppT _ = Nothing


isFunctionWithArity :: Int -> Type -> Q Bool
isFunctionWithArity n t = runTc $ do
  t'  <- runQ $ resolveTypeSynonyms t
  tys <- for [0..n] $ const freshTy
  let arr = foldl1 (:->) tys
  unifyTyResult t' arr >>= \case
    Equal -> pure True
    _     -> do
      case headAppT t' of
        Nothing -> pure $ trace (show t) False
        Just (h, apps) -> runQ (reify h) >>= \case
          TyConI (NewtypeD _ _ vars _ con _) ->
            case getNewtypeConType con of
              Just nty ->
                runQ
                  $ isFunctionWithArity n
                  $ applySubstitution
                      (M.fromList $ zip (fmap bndrName vars) apps)
                  $ nty
              Nothing -> trace "not a newtype" $ pure False
          _ -> pure $ trace "bad reify" False

getNewtypeConType :: Con -> Maybe Type
getNewtypeConType (NormalC _ [(_, t)]) = Just t
getNewtypeConType (RecC _ [(_, _, t)]) = Just t
getNewtypeConType _ = Nothing

