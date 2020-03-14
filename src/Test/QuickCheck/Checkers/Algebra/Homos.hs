{-# LANGUAGE TemplateHaskellQuotes #-}

module Test.QuickCheck.Checkers.Algebra.Homos where

import           Data.List (foldl')
import qualified Data.Map as M
import           Language.Haskell.TH hiding (ppr, Arity)
import           Test.QuickCheck.Checkers.Algebra.Types
import           Test.QuickCheck.Checkers.Algebra.Unification


appHead :: Exp -> Maybe Name
appHead (VarE n)   = Just n
appHead (ConE n)   = Just n
appHead (AppE f _) = appHead f
appHead _          = Nothing

aritySize :: Arity -> Int
aritySize Binary     = 2
aritySize (Prefix n) = n

makeHomo :: Name -> [(Name, Arity)] -> Exp -> [NamedLaw]
makeHomo ty ops (LamE [VarP name] body) =
  let app_head = maybe "<expr>" nameBase $ appHead body
      homo_name = nameBase ty
      hs = fmap (UnboundVarE . mkName . (nameBase name ++) . show)
                [1 .. maximum $ fmap (aritySize . snd) ops]
      mk_lawname fn =
        mconcat
          [ app_head, ":", homo_name, ":", nameBase fn ]
   in flip fmap ops $ \(fn_name, arity) ->
        mkHomo name hs body (mk_lawname fn_name) (VarE fn_name) arity
makeHomo _ _ _ = error "monoidal homomorphism needs a lambda"


mkHomo :: Name -> [Exp] -> Exp -> String -> Exp -> Arity -> NamedLaw
mkHomo name vars body law_name fn Binary =
  case vars of
    (v1:v2:_) ->
      let replace x = rebindVars (M.singleton name x) body
       in Law law_name
              (replace $ InfixE (Just v1) fn (Just v2))
              (InfixE (Just $ replace v1)
                      fn
                      (Just $ replace v2))
    _ -> error "not enough args to mkHomo"
mkHomo name all_vars body law_name fn (Prefix n)=
  let replace x = rebindVars (M.singleton name x) body
      vars = take n all_vars
   in Law law_name
          (replace $ foldl' AppE fn vars)
          (foldl' AppE fn $ fmap replace vars)


knownHomos :: Name -> [(Name, Arity)]
knownHomos nm
  | nm == ''Semigroup
        = [ ('(<>),   Binary) ]
  | nm == ''Monoid
        = [ ('mempty, Prefix 0)
          , ('(<>),   Binary)
          ]
  | nm == ''Eq
        = [ ('(==), Binary) ]
  | nm == ''Ord
        = [ ('compare, Prefix 2) ]
  | otherwise = error $ "unsupported homo type " ++ show nm

