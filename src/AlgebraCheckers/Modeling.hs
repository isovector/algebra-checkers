{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}

module AlgebraCheckers.Modeling where

import           AlgebraCheckers.Ppr
import           AlgebraCheckers.Suggestions
import           AlgebraCheckers.Typechecking
import           AlgebraCheckers.Unification
import           Control.Arrow
import           Data.Data
import           Data.Generics.Aliases
import           Data.Generics.Schemes
import qualified Data.Map as M
import           Data.Maybe
import           Language.Haskell.TH hiding (ppr, Arity)
import           Test.QuickCheck.Checkers (Model, ModelOf, model)


unmodel :: Model a => ModelOf a -> a
unmodel = undefined


getModelType :: Type -> Q Type
getModelType ty =
  hasInstance ''Model ty >>= \case
    False -> pure ty
    True -> [t|ModelOf $(pure ty)|]


denotationType :: Type -> Q Type
denotationType ty = do
  let (args, res) = unrollTyArr ty
  foldr (:->)
    <$> getModelType res
    <*> traverse getModelType args


replaceWithModelNames :: Data a => (Name -> Name) -> [Name] -> a -> a
replaceWithModelNames f
  = rebindVars
  . M.fromList
  . fmap (id &&& VarE . f)


mkModelName :: Name -> Name
mkModelName = mkName . mappend "model_" . nameBase

mkTycheckName :: Name -> Name
mkTycheckName = mkName . mappend "typecheck_" . nameBase


deleteFunctionCall :: Data a => Name -> a -> a
deleteFunctionCall nm = everywhere $ mkT $ \case
  VarE x | x == nm -> VarE 'id
  x                -> x


modelFor :: [Name] -> Dec -> Q Dec
modelFor _ (SigD name ty) = SigD (mkModelName name) <$> denotationType ty
modelFor nms (FunD name cls)
  = pure
  . FunD (mkModelName name)
  . deleteFunctionCall 'model
  . deleteFunctionCall 'unmodel
  $ replaceWithModelNames mkModelName nms cls
modelFor _ x = fail $ "not allowed in modelFor: " ++ render (ppr x)

tycheckFor :: [Name] -> Dec -> Maybe Dec
tycheckFor _ (SigD name ty) = pure $ SigD (mkTycheckName name) ty
tycheckFor nms (FunD name cls) = pure $ FunD (mkTycheckName name) $ replaceWithModelNames mkTycheckName nms cls
tycheckFor _ _ = Nothing

defines :: Dec -> Maybe Name
defines (FunD name _) = pure name
defines _             = Nothing

modelsFor :: [Dec] -> Q [Dec]
modelsFor decs = do
  let nms = mapMaybe defines decs
  mappend <$> traverse (modelFor nms) decs <*> pure (mapMaybe (tycheckFor nms) decs)

