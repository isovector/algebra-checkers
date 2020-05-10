{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TupleSections    #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module AlgebraCheckers.Typechecking
  ( inferUnboundVars
  , isFunctionWithArity
  , typecheck
  , monomorphize
  , pattern (:->)
  , typecheckExp
  ) where

import Debug.Trace
import           AlgebraCheckers.Unification (unboundVars, varsToQuantify)
import           Control.Arrow (second)
import           Control.Monad
import           Data.Foldable
import           Data.Generics.Aliases
import           Data.Generics.Schemes
import qualified Data.Map as M
import           Data.Maybe
import           Data.Traversable
import           Data.Word
import           Language.Haskell.TH.Datatype (applySubstitution, resolveTypeSynonyms)
import           Language.Haskell.TH.Syntax
import           Language.Haskell.TH.Typecheck
import           Language.Haskell.TH.Ppr (ppr)
import           Test.QuickCheck.Checkers


type Scope = M.Map Name Type

instance EqProp Word8 where
  (=-=) = eq


monomorphize :: Type -> Type
monomorphize = everywhere $ mkT $ \case
  VarT _ -> ConT ''Word8
  t -> t


instantiate' :: MonadTc m => Type -> m Type
instantiate' (ForallT tys _ t) = do
  let names = fmap bndrName tys
  tys' <- for names $ \name -> (name, ) <$> freshTy
  instantiate' $ applySubstitution (M.fromList tys') t
instantiate' (a :-> b) = (a :->) <$> instantiate' b
instantiate' t = pure t


typecheck :: MonadTc m => Scope -> Exp -> m Type
typecheck scope = (substZonked =<<) . \case
  UnboundVarE n -> do
    t <- freshTy
    pure $ fromMaybe t $ M.lookup n scope
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
  ParensE e -> typecheck scope e
  ListE exps -> do
    t <- freshTy
    innert <- freshTy
    for_ exps $ \e -> do
      et <- typecheck scope e
      unifyTy' innert et
    unifyTy' t $ ListT `AppT` innert
    pure t


  x -> error $ mappend "typecheck" $ show x


freshTy :: MonadTc m => m Type
freshTy = VarT <$> freshUnifTV



bndrName :: TyVarBndr -> Name
bndrName (PlainTV n) = n
bndrName (KindedTV n _) = n


inferUnboundVars :: Exp -> Q Scope
inferUnboundVars e = runTc $ do
  let unbound = varsToQuantify e
  vars <-
    fmap M.fromList $ for unbound $ \var -> do
      t <- freshTy
      pure (var, t)
  void $ typecheck vars e
  traverse substZonked vars

typecheckExp :: Exp -> Q Type
typecheckExp e = runTc $ do
  let unbound = unboundVars e
  vars <-
    fmap M.fromList $ for unbound $ \var -> do
      t <- freshTy
      pure (var, t)
  z <- typecheck vars e
  substZonked z


pattern (:->) :: Type -> Type -> Type
pattern t :-> ts <- AppT (AppT ArrowT t) ts
  where
    t :-> ts = AppT (AppT ArrowT t) ts

infixr 0 :->


headAppT :: Type -> Maybe (Name, [Type])
headAppT (ConT n) = Just (n, [])
headAppT (AppT a t) = fmap (second (++ [t])) (headAppT a)
headAppT _ = Nothing


isFunctionWithArity :: Int -> Type -> Q Bool
isFunctionWithArity n t = runTc $ do
  t'  <- runQ $ resolveTypeSynonyms t
  tys <- for [0..n] $ const freshTy
  let arr = foldr1 (:->) tys
  unifyTyResult t' arr >>= \case
    Equal -> pure True
    _     -> pure False --  do
      -- case headAppT t' of
      --   Nothing -> pure $ trace (show t) False
      --   Just (h, apps) -> runQ (reify h) >>= \case
      --     TyConI (NewtypeD _ _ vars _ con _) ->
      --       case getNewtypeConType con of
      --         Just nty ->
      --           runQ
      --             $ isFunctionWithArity n
      --             $ applySubstitution
      --                 (M.fromList $ zip (fmap bndrName vars) apps)
      --             $ nty
      --         Nothing -> trace "not a newtype" $ pure False
      --     _ -> pure $ trace "bad reify" False

getNewtypeConType :: Con -> Maybe Type
getNewtypeConType (NormalC _ [(_, t)]) = Just t
getNewtypeConType (RecC _ [(_, _, t)]) = Just t
getNewtypeConType _ = Nothing


unifyTy' :: MonadTc m => Type -> Type -> m ()
unifyTy' a b = do
  -- traceM $ "unifying " ++ show (ppr a) ++ " = " ++ show (ppr b)
  unifyTy a b

