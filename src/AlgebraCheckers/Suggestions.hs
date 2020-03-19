{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module AlgebraCheckers.Suggestions where

import Data.List
import Data.Char
import Control.Monad
import Prelude hiding (exp)
import Data.Traversable
import Language.Haskell.TH hiding (ppr)
import Language.Haskell.TH.Syntax
import AlgebraCheckers.Ppr
import AlgebraCheckers.Unification
import AlgebraCheckers.Patterns
import Data.Generics.Schemes (listify)
import Data.Data
import Data.Maybe
import THInstanceReification
import Data.Group


data Suggestion
  = HomoSuggestion Name Name Int Type Type Exp
  deriving (Eq, Ord, Show)

homoSuggestionEq :: Suggestion -> Suggestion -> Bool
homoSuggestionEq (HomoSuggestion _ fn1 ix1 _ _ _)
                 (HomoSuggestion _ fn2 ix2 _ _ _) = fn1 == fn2
                                                 && ix1 == ix2


pprSuggestion :: Suggestion -> Doc
pprSuggestion (HomoSuggestion nm _ _ arg_ty res_ty (LamE [VarP var] exp)) =
  ppr $ deModuleName $
    VarE 'law `AppTypeE` ConT nm `AppE` (LamE [SigP (VarP var) arg_ty] $ SigE exp res_ty)
pprSuggestion (HomoSuggestion nm _ _ _ _ exp) =
  ppr $ deModuleName $
    VarE 'law `AppTypeE` ConT nm `AppE` exp


knownSuggestionHierarchies :: [[Name]]
knownSuggestionHierarchies =
  [ [ ''Group, ''Monoid, ''Semigroup ]
  ]

suggest :: Data a => Module -> a -> Q [Suggestion]
suggest md a = do
  let surface = getSurface md a
  fmap (join . join) $
    for surface $ \nm ->
      for knownSuggestionHierarchies $ \hierarchy -> do
        zs <- fmap join $ for hierarchy $ \tc_name -> do
          VarI _ ty _ <- reify nm
          possibleHomos tc_name nm ty
        pure $ nubBy homoSuggestionEq zs


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
      fmap catMaybes $ for (zip3 names args [0..]) $ \(name, arg, ix) ->
        hasInstance tc_name arg >>= \case
          False -> pure Nothing
          True  -> do
            exp <- lamE [varP name] $ appsE $ varE fn : fmap varE names
            pure $ Just $ HomoSuggestion tc_name fn ix arg res exp


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
hasInstance tc_name = isProperInstance tc_name . pure

