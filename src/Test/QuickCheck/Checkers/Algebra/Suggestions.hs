{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module Test.QuickCheck.Checkers.Algebra.Suggestions where

import Data.Char
import Control.Monad
import Prelude hiding (exp)
import Data.Traversable
import Language.Haskell.TH hiding (ppr)
import Language.Haskell.TH.Syntax
import Test.QuickCheck.Checkers.Algebra.Ppr
import Test.QuickCheck.Checkers.Algebra.Unification
import Test.QuickCheck.Checkers.Algebra.Patterns
import Data.Generics.Schemes (listify)
import Data.Data
import Data.Maybe
import THInstanceReification
import Data.Group


data Suggestion
  = HomoSuggestion Name Type Type Exp
  deriving (Eq, Ord, Show)


pprSuggestion :: Suggestion -> Doc
pprSuggestion (HomoSuggestion nm arg_ty res_ty (LamE [VarP var] exp)) =
  ppr $ deModuleName $
    VarE 'law `AppTypeE` ConT nm `AppE` (LamE [SigP (VarP var) arg_ty] $ SigE exp res_ty)
pprSuggestion (HomoSuggestion nm _ _ exp) =
  ppr $ deModuleName $
    VarE 'law `AppTypeE` ConT nm `AppE` exp

suggest :: Data a => Module -> a -> Q [Suggestion]
suggest md a = do
  let surface = getSurface md a
  fmap (join . join) $ for [''Semigroup, ''Monoid, ''Group] $ \tc_name ->
    for surface $ \nm -> do
      VarI _ ty _ <- reify nm
      possibleHomos tc_name nm ty


suggest' :: Data a => a -> Q [Suggestion]
suggest' a = do
  md <- thisModule
  suggest md a



possibleHomos :: Name -> Name -> Type -> Q [Suggestion]
possibleHomos tc_name fn ty = do
  let (args, res) = unrollTyArr ty
  hasInstance tc_name res >>= \case
    False -> pure []
    True  -> do
      names <- for args $ newName . goodTyName
      fmap catMaybes $ for (zip names args) $ \(name, arg) ->
        hasInstance tc_name arg >>= \case
          False -> pure Nothing
          True  -> do
            exp <- lamE [varP name] $ appsE $ varE fn : fmap varE names
            pure $ Just $ HomoSuggestion tc_name arg res exp


goodTyName :: Type -> String
goodTyName = fmap toLower . take 1 . dropWhile (not . isAlpha) . render . ppr . deModuleName

getSurface :: Data a => Module -> a -> [Name]
getSurface m = listify (sameModule m)


sameModule :: Module -> Name -> Bool
sameModule (Module (PkgName pkg) (ModName md)) n =
  nameModule n == Just md && namePackage n == Just pkg


unrollTyArr :: Type -> ([Type], Type)
unrollTyArr ty =
  let tys = unloopTyArrs ty
   in (init tys, last tys)
  where
    unloopTyArrs :: Type -> [Type]
    unloopTyArrs (ArrowT `AppT` a `AppT` b) =  a : unloopTyArrs b
    unloopTyArrs t =  [t]

hasInstance :: Name -> Type -> Q Bool
hasInstance tc_name ty =
  isProperInstance tc_name [ty]

