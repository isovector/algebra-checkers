{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE ViewPatterns       #-}

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
import           Language.Haskell.TH.Syntax (putQ, getQ)
import           Test.QuickCheck.Checkers (Model, ModelOf, model)


data TypeTemplate = TypeTemplate
  { ttCon   :: Name
  , ttArity :: Integer
  , ttArgs  :: [Name]
  , ttType  :: Type
  } deriving (Eq, Ord, Show, Data)

sloppy :: Name -> Name
sloppy = mkName . nameBase

replaceTT :: Data a => M.Map Name TypeTemplate -> a -> a
replaceTT tts = everywhere $ mkT $ \case
  ConT (sloppy -> n) | Just tt <- M.lookup n tts ->
    case ttArity tt of
      0 -> ttType tt
      _ -> UInfixT (LitT (NumTyLit $ ttArity tt - 1)) n (TupleT 0)
  AppT (UInfixT (LitT (NumTyLit 0)) n args) arg | Just tt <- M.lookup n tts ->
    let replacement
          = M.fromList
          . zip (ttArgs tt)
          . reverse
          . unravel
          $ AppT args arg
     in rebindTyVars replacement $ ttType tt
  AppT (UInfixT (LitT (NumTyLit arity)) n args) arg ->
    UInfixT (LitT (NumTyLit $ arity - 1)) n (AppT args arg)
  t -> t

constructTTs :: [Dec] -> M.Map Name TypeTemplate
constructTTs ds =
  let tts = mapMaybe mkTypeTemplate ds
   in M.fromList $ fmap (ttCon &&& id) tts

mkTypeTemplate :: Dec -> Maybe TypeTemplate
mkTypeTemplate (TySynD n args res)
  = Just $ TypeTemplate (sloppy n) (fromIntegral $ length args) (fmap getTVName args) res
mkTypeTemplate _ = Nothing

getTVName :: TyVarBndr -> Name
getTVName (PlainTV n)    = n
getTVName (KindedTV n _) = n

rebindTyVars :: Data a => M.Map Name Type -> a -> a
rebindTyVars m = everywhere $ mkT $ \case
  e@(VarT n) ->
    case M.lookup n m of
      Just e' -> e'
      Nothing -> e
  t -> t

unravel :: Type -> [Type]
unravel (TupleT 0) = []
unravel (AppT a b) = b : unravel a
unravel _ = error "unravel"




unmodel :: Model a => ModelOf a -> a
unmodel = undefined


getModelType :: M.Map Name TypeTemplate -> Type -> Q Type
getModelType tts ty = pure $ replaceTT tts ty


denotationType :: M.Map Name TypeTemplate -> Type -> Q Type
denotationType tts ty = do
  let (args, res) = unrollTyArr ty
  foldr (:->)
    <$> getModelType tts res
    <*> traverse (getModelType tts) args


replaceWithModelNames :: Data a => (Name -> Name) -> [Name] -> a -> a
replaceWithModelNames f
  = rebindVars
  . M.fromList
  . fmap (id &&& VarE . f)

sloppyReplaceWithModelNames :: Data a => (Name -> Name) -> [Name] -> a -> a
sloppyReplaceWithModelNames f
  = sloppyRebindVars
  . M.fromList
  . fmap (mkName . nameBase &&& VarE . f . mkName . nameBase)


mkModelName :: Name -> Name
mkModelName = mkName . mappend "model_" . nameBase

mkTycheckName :: Name -> Name
mkTycheckName = mkName . mappend "typecheck_" . nameBase


deleteFunctionCall :: Data a => Name -> a -> a
deleteFunctionCall nm = everywhere $ mkT $ \case
  VarE x | x == nm -> VarE 'id
  x                -> x

genModel :: Data a => [Name] -> a -> a
genModel nms
  = deleteFunctionCall 'model
  . deleteFunctionCall 'unmodel
  . replaceWithModelNames mkModelName nms


remapModelTypes :: Data a => M.Map Name TypeTemplate -> a -> Q a
remapModelTypes tts = everywhereM $ mkM
  (\case
    SigP p ty -> SigP p <$> denotationType tts ty
    t         -> pure t) `extM`
  (\case
    SigE e ty     -> SigE e <$> denotationType tts ty
    AppTypeE e ty -> AppTypeE e <$> denotationType tts ty
    t             -> pure t)



modelFor :: M.Map Name TypeTemplate -> [Name] -> Dec -> Q Dec
modelFor tts _ (SigD name ty) = SigD (mkModelName name) <$> denotationType tts ty
modelFor tts nms (FunD name cls)
  = remapModelTypes tts
  . FunD (mkModelName name)
  $ genModel nms cls
modelFor tts nms (ValD name body decs)
  = remapModelTypes tts
  $ ValD (everywhere (mkT mkModelName) name)
         (genModel nms body)
         (genModel nms decs)
modelFor _ _ x = fail $ "not allowed in modelFor: " ++ render (ppr x)

tycheckFor :: [Name] -> Dec -> Maybe Dec
tycheckFor _ (SigD name ty) = pure $ SigD (mkTycheckName name) ty
tycheckFor nms (ValD name body decs)
  = pure $ ValD (everywhere (mkT mkTycheckName) name)
                (replaceWithModelNames mkTycheckName nms body)
                (replaceWithModelNames mkTycheckName nms decs)
tycheckFor nms (FunD name cls)
  = pure $ FunD (mkTycheckName name) $ replaceWithModelNames mkTycheckName nms cls
tycheckFor _ _ = Nothing

defines :: Dec -> Maybe Name
defines (ValD (VarP name) _ _) = pure name
defines (ValD _ _ _) = error "defines doesn't support complicated ValDs"
defines (FunD name _)   = pure name
defines _               = Nothing

modelsFor :: M.Map Name TypeTemplate -> [Dec] -> Q [Dec]
modelsFor tts decs = do
  -- tts <- fmap (fromMaybe mempty) getQ
  -- Just tts <- getQ
  let nms = mapMaybe defines decs
  z <- mappend <$> traverse (modelFor tts nms) decs <*> pure (mapMaybe (tycheckFor nms) decs)
  putQ nms
  pure z

