{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-name-shadowing -Wno-orphans #-}

-- | Poor man's typechecker in Template Haskell. Capable of working with type
-- synonyms, type families, DataKinds, kind polymorphism.
--
-- Levity polymorphism is currently not supported. Return kind inference in
-- type families is not supported.
--
-- GHC cannot reify roles correctly, so we cannot solve Coercible constraints
-- correctly, so instance resolution was left out.
module Language.Haskell.TH.Typecheck
  ( MonadTc
  , TcScope
  , runTc
  , TV
  , freshUnifTV
  , freshNamedUnifTV
  , HasTV(..)
  , extractKind
  , unifyTy
  , unifyTys
  , UnifyResult(..)
  , unifyTyResult
  , unifyTysResult
  , extractSubst
  , substZonked
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad.State.Class
import Control.Monad.Trans
import Control.Monad.Trans.State (StateT, evalStateT)
import Data.Foldable
import Data.List as L
import Data.Maybe
import Data.Map as M
import Data.Set as S
import Language.Haskell.TH
import Language.Haskell.TH.Instances () -- Quasi StateT
import Language.Haskell.TH.Syntax hiding (lift)
import Numeric.Natural

{-

data Constr = ClsC Name [Type] | EqC Type Role Type deriving Show

data TcInst = TcInst
  { instArgs :: [Type]
  , instOverlap :: Overlap
  , instContext :: [Constr]
  } deriving Show
-}

-- | Type variable.
type TV = Name

data AxBranch = AxBranch
  { axLhs :: [Type]
  , axRhs :: Type
  , axIncomp :: [Natural]
  } deriving Show

type AxBranched = [AxBranch]

data TcConInfo
  = TcPlainCon
  { conKind :: Kind
  , conRoles :: [Role]
  }
  | TcCls
  { clsArgKinds :: [Kind]
{-, clsInst :: [TcInst]
  , clsSuper :: [Constr] -}
  }
  | TcFam
  { famArgKinds :: [Kind]
  , famResKind :: Kind
  , famAxioms :: [AxBranched]
  } deriving Show

data ConName = Con Name | Promoted Name | LitCon TyLit | StarCon
  deriving (Eq, Ord, Show)

-- | Scope of the typechecker. Includes information about unificational vs
-- rigid (skolem) type variables, and a cache of type information reified from
-- GHC.
data TcScope = TcScope
  { _tsUnifVars :: S.Set TV
  , _tsZonkedVars :: M.Map TV Type
  , _tsVarKind :: M.Map TV Kind
  , _tsTyCons :: M.Map ConName TcConInfo
  }

makeLenses ''TcScope

-- | Constraints for the typechecking monad. You probably want to use
-- @m ~ 'StateT' 'TcScope' 'Q'@
type MonadTc m = (Quasi m, MonadState TcScope m)

-- | Execute a typechecker computation. Unificational variables will not persist
-- between different 'runTc' blocks.
runTc :: Monad m => StateT TcScope m a -> m a
runTc = (`evalStateT` emptyScope)
  where
    emptyScope = TcScope
      { _tsUnifVars = S.empty
      , _tsZonkedVars = M.empty
      , _tsVarKind = M.empty
      , _tsTyCons = M.empty
      }

tcFail :: MonadTc m => String -> m a
tcFail = fail

qLookupTypeName :: MonadTc m => String -> m (Maybe Name)
qLookupTypeName = qLookupName True

qLookupValueName :: MonadTc m => String -> m (Maybe Name)
qLookupValueName = qLookupName False

-- | Make a fresh (unused) unificational type variable. Unification will be able
-- to replace this type variable with a concrete type.
freshUnifTV :: MonadTc m => m TV
freshUnifTV = do
  v <- qNewName "u"
  tsUnifVars . at v .= Just ()
  pure v

-- | Make a fresh (unused) unificational type variable. Unification will be able
-- to replace this type variable with a concrete type.
freshNamedUnifTV :: MonadTc m => String -> m TV
freshNamedUnifTV nm = do
  v <- qNewName nm
  tsUnifVars . at v .= Just ()
  pure v

-- | A class for thigns that contain type variables.
class HasTV a where
  -- | Replace all free variables with fresh unificational type variables.
  instantiate :: MonadTc m => a -> m a
  instantiate x = evalStateT (instantiating x) M.empty
  -- | Replace all free variables with fresh unificational type variables, in
  -- a state transformer.
  instantiating :: MonadTc m => a -> StateT (M.Map TV TV) m a
  -- | Free variables.
  occurrences :: a -> S.Set TV

instance HasTV Name where
  instantiating v = do
    use (at v) >>= \case
      Just v' -> pure v'
      Nothing -> do
        v' <- lift freshUnifTV
        at v .= Just v'
        k' <- lift (tvKind v) >>= instantiating
        lift $ tvSetKind v' k'
        pure v'
  occurrences = S.singleton

instance HasTV a => HasTV [a] where
  instantiating = traverse instantiating
  occurrences = S.unions . L.map occurrences

instance (HasTV a, HasTV b) => HasTV (a, b) where
  instantiating (x, y) = (,) <$> instantiating x <*> instantiating y
  occurrences (x, y) = occurrences x `S.union` occurrences y

instance HasTV Type where
  instantiating (ForallT tvbs cxt ty) = ForallT
    <$> traverse protectTVB tvbs
    <*> traverse instantiating cxt
    <*> instantiating ty
    where
      protectTVB :: MonadTc m => TyVarBndr -> StateT (M.Map TV TV) m TyVarBndr
      protectTVB (PlainTV v) = (at v .= Just v) *> pure (PlainTV v)
      protectTVB (KindedTV v k) =
        (at v .= Just v) *> (KindedTV v <$> instantiating k)
  instantiating (AppT f x) = AppT <$> instantiating f <*> instantiating x
  instantiating (SigT t k) = SigT <$> instantiating t <*> instantiating k
  instantiating (VarT v) = VarT <$> instantiating v
  instantiating (InfixT x op y) = InfixT
    <$> instantiating x
    <*> pure op
    <*> instantiating y
  instantiating (UInfixT x op y) = UInfixT
    <$> instantiating x
    <*> pure op
    <*> instantiating y
  instantiating (ParensT t) = ParensT <$> instantiating t
  instantiating t = pure t
  occurrences (ForallT _ cxt ty) = occurrences cxt <> occurrences ty
  occurrences (AppT f x) = occurrences f <> occurrences x
  occurrences (SigT t k) = occurrences t <> occurrences k
  occurrences (VarT v') = occurrences v'
  occurrences (InfixT x _ y) = occurrences x <> occurrences y
  occurrences (UInfixT x _ y) = occurrences x <> occurrences y
  occurrences (ParensT t) = occurrences t
  occurrences _ = S.empty

occursCheck :: MonadTc m => TV -> Type -> m ()
occursCheck v t = do
  t' <- substZonked t
  if v `S.member` occurrences t'
  then tcFail $ "Occurs check: " ++ show v ++ " ~ " ++ show t'
  else pure ()

memoizedWith
  :: MonadState s m => ALens' s (Maybe a) -> ((a -> m ()) -> m b) -> m a
memoizedWith l f = do
  use (cloneLens l) >>= \case
    Just r -> pure r
    Nothing -> f (\r -> cloneLens l .= Just r) >> memoizedWith l f

memoized :: MonadState s m => ALens' s (Maybe a) -> m a -> m a
memoized l f = memoizedWith l (\m -> f >>= \r -> r <$ m r)

skolemizing :: (HasTV a, MonadTc m) => a -> m b -> m b
skolemizing t f = do
  unif <- use tsUnifVars
  zonked <- use $ tsZonkedVars . to M.keysSet
  let occ = (occurrences t `S.intersection` unif) S.\\ zonked
  tsUnifVars %= (S.\\ occ)
  r <- f
  tsUnifVars %= S.union occ
  pure r

tvSetKind :: MonadTc m => TV -> Kind -> m ()
tvSetKind v k = tsVarKind . at v .= Just k

-- we assume unknown kinds to be unificational kind vars
tvKind :: MonadTc m => TV -> m Kind
tvKind v = memoized (tsVarKind . at v) $ do
  kv <- freshUnifTV
  tvSetKind kv StarT -- rep poly?
  pure $ VarT kv

isUnifTV :: MonadTc m => TV -> m Bool
isUnifTV tv = isJust <$> use (tsUnifVars . at tv)

zonkTV :: MonadTc m => TV -> Type -> m ()
zonkTV tv ty = do
  isUnifTV tv >>= \case
    True -> case ty of
      VarT tv' | tv == tv'
        -> tcFail $ "Attempted to zonk a tyvar with itself: " ++ show tv
      _ -> pure ()
    False -> tcFail $ "Attempted to zonk a skolem " ++ show tv
  use (tsZonkedVars . at tv) >>= \case
    Nothing -> do
      tsZonkedVars . at tv .= Just ty
    Just ty' -> tcFail $ "Attempted to zonk " ++ show tv ++ " with "
      ++ show ty ++ " but it already equals " ++ show ty'

isZonked :: MonadTc m => TV -> m (Maybe Type)
isZonked tv = use (tsZonkedVars . at tv)

-- convert NameS and NameQ into a NameG
normalizeTypeName :: MonadTc m => Name -> m Name
normalizeTypeName (Name (OccName nm) NameS) =
  qLookupTypeName nm >>= \case
    Just nm -> pure nm
    Nothing -> tcFail $ "Could not find dynamically bound name " ++ nm
normalizeTypeName (Name (OccName nm) (NameQ (ModName mod))) =
  qLookupTypeName (mod ++ "." ++ nm) >>= \case
    Just nm -> pure nm
    Nothing -> tcFail $ "Could not find qualified name " ++ mod ++ "." ++ nm
normalizeTypeName nm@(Name _ (NameG TcClsName _ _)) = pure nm
normalizeTypeName (Name occ flav) =
  tcFail $ "normalizeTypeName (Name " ++ show occ ++ " " ++ show flav ++ ")"

normalizePromotedName :: MonadTc m => Name -> m Name
normalizePromotedName (Name (OccName nm) NameS) =
  qLookupValueName nm >>= \case
    Just nm -> pure nm
    Nothing -> tcFail $ "Could not find dynamically bound name " ++ nm
normalizePromotedName (Name (OccName nm) (NameQ (ModName mod))) =
  qLookupValueName (mod ++ "." ++ nm) >>= \case
    Just nm -> pure nm
    Nothing -> tcFail $ "Could not find qualified name " ++ mod ++ "." ++ nm
normalizePromotedName nm@(Name _ (NameG DataName _ _)) = pure nm
normalizePromotedName (Name occ flav) =
  tcFail $ "normalizePromotedName (Name " ++ show occ ++ " " ++ show flav ++ ")"

normalizeConName :: MonadTc m => ConName -> m ConName
normalizeConName (Con nm) = Con <$> normalizeTypeName nm
normalizeConName (Promoted nm) = Promoted <$> normalizePromotedName nm
normalizeConName con = pure con

addTVB :: MonadTc m => TyVarBndr -> m Kind
addTVB (PlainTV v) = tvKind v
addTVB (KindedTV v k) = tvSetKind v k *> pure k

name_Tuple, name_UnboxedTuple, name_UnboxedSum, name_PromotedTuple
  :: String -> Name
name_Tuple = mkNameG_tc "ghc-prim" "GHC.Tuple"
name_UnboxedTuple = mkNameG_tc "ghc-prim" "GHC.Prim"
name_UnboxedSum = mkNameG_tc "ghc-prim" "GHC.Prim"
name_PromotedTuple = mkNameG_d "ghc-prim" "GHC.Tuple"

name_Arrow, name_Equality, name_List, name_Nil, name_Cons, name_Constraint,
  name_Symbol, name_Nat, name_TYPE :: Name
name_Arrow = mkNameG_tc "ghc-prim" "GHC.Prim" "->"
name_Equality = mkNameG_tc "base" "Data.Type.Equality" "~"
name_List = mkNameG_tc "ghc-prim" "GHC.Types" "[]"
name_Nil = mkNameG_d "ghc-prim" "GHC.Types" "[]"
name_Cons = mkNameG_d "ghc-prim" "GHC.Types" ":"
name_Constraint = mkNameG_tc "ghc-prim" "GHC.Types" "Constraint"
name_Symbol = mkNameG_tc "ghc-prim" "GHC.Types" "Symbol"
name_Nat = mkNameG_tc "ghc-prim" "GHC.Types" "Nat"
name_TYPE = mkNameG_tc "ghc-prim" "GHC.Prim" "TYPE"

isConName :: Type -> Maybe ConName
isConName (ConT nm) = Just $ Con nm
isConName (PromotedT nm) = Just $ Promoted nm
isConName (LitT lit) = Just $ LitCon lit
isConName (TupleT arity) = Just $ Con $ name_Tuple name
  where name = "(" ++ replicate (arity - 1) ',' ++ ")"
isConName (UnboxedTupleT arity) = Just $ Con $ name_UnboxedTuple name
  where name = "(#" ++ replicate (arity - 1) ',' ++ "#)"
isConName (UnboxedSumT arity) = Just $ Con $ name_UnboxedSum name
  where name = "(#" ++ replicate (arity - 1) '|' ++ "#)"
isConName ArrowT = Just $ Con name_Arrow
isConName EqualityT = -- possibly not?
  Just $ Con name_Equality
isConName ListT =
  Just $ Con name_List
isConName (PromotedTupleT arity) = Just $ Promoted $ name_PromotedTuple name
  where name = "(" ++ replicate (arity - 1) ',' ++ ")"
isConName PromotedNilT = Just $ Promoted name_Nil
isConName PromotedConsT = Just $ Promoted name_Cons
isConName StarT = Just StarCon
isConName ConstraintT = Just $ Con name_Constraint
isConName (AppT (ConT nm) _) | nm == name_TYPE = Just StarCon
isConName _ = Nothing

mkArrow :: [Type] -> Type -> Type
mkArrow = flip $ L.foldr (\t ts -> ArrowT `AppT` t `AppT` ts)

splitTyConApp :: Type -> Maybe (ConName, [Type])
splitTyConApp = go []
  where
    go args t | Just ucn <- isConName t = Just (ucn, args)
    go args (AppT f x) = go (x:args) f
    go args (SigT t _) = go args t
    go args (InfixT x ucn y) = Just (Con ucn, x:y:args)
    go args (ParensT t) = go args t
    go _ _ = Nothing

data SplitResult = FamApp ConName [Type] | App Type Type | SingleCon ConName

trySplitApp :: MonadTc m => Type -> m SplitResult
trySplitApp t = case splitTyConApp t of
  Just (cn, args) -> conInfo cn >>= \case
    TcFam{..} -> do
      let arity = length famArgKinds
      case compare (length args) arity of
        LT -> tcFail
          $ "Partially applied type family: " ++ show cn ++ " " ++ show args
        EQ -> pure $ FamApp cn args
        GT -> split t
    _ -> split t
  _ -> split t
  where
    split t | Just cn <- isConName t = SingleCon <$> normalizeConName cn
    split (AppT f x) = pure $ App f x
    split (SigT t _) = split t
    split (InfixT x ucn y) = pure $ App (ConT ucn `AppT` x) y
    split (ParensT t) = split t
    split t = tcFail $ "split " ++ show t

tryExpandTyFam :: MonadTc m => Bool -> ConName -> [Type] -> m (Maybe Type)
tryExpandTyFam False _ _ = pure Nothing
tryExpandTyFam True cn args = conInfo cn >>= \case
  TcFam{..} -> skolemizing args $ matchAxioms famAxioms args
  _ -> pure Nothing
  where
    matchAxioms :: MonadTc m => [AxBranched] -> [Type] -> m (Maybe Type)
    matchAxioms [] _ = pure Nothing
    matchAxioms (a:as) args = matchAxiom S.empty (zip [0..] a) args >>= \case
      Just ty -> pure $ Just ty
      Nothing -> matchAxioms as args

    matchAxiom :: MonadTc m
      => S.Set Natural -> [(Natural, AxBranch)] -> [Type] -> m (Maybe Type)
    matchAxiom apart ((i, AxBranch{..}):as) args
      | all (`S.member` apart) axIncomp = do
        (lhs, rhs) <- instantiate (axLhs, axRhs)
        unifyTysResultE True {- args could have TFs -} lhs args >>= \case
          Equal -> pure $ Just rhs
          Unknown _ -> matchAxiom apart as args
          Apart _ -> matchAxiom (S.insert i apart) as args
      | otherwise = matchAxiom apart as args
    matchAxiom _ [] _ = pure Nothing

-- | Result of unification
data UnifyResult
  = Apart String
    -- ^ The types are known to be different. (Includes an error message for if
    -- the types were expected to be equal).
  | Unknown String
    -- ^ The types may be different depending on substitutions of rigid type
    -- variables or not-yet-known type family instances. (Includes an error
    -- message for if the types were expected to be equal).
  | Equal -- ^ The types are known to be equal
  deriving (Eq, Ord, Show)

matchError :: Show a => a -> a -> String
matchError x y = "Could not match " ++ show x ++ " with " ++ show y

tryZonk :: MonadTc m
  => (Type -> Type -> m UnifyResult) -> TV -> Type -> m UnifyResult
tryZonk unify v t' = isUnifTV v >>= \case
  True -> isZonked v >>= \case
    Nothing -> substZonked t' >>= \case
      VarT v' | v == v' -> pure Equal
      t' -> occursCheck v t' >> zonkTV v t' >> pure Equal
    Just t -> unify t t'
  False -> case t' of
    VarT v' -> isUnifTV v' >>= \case
      True -> isZonked v' >>= \case
        Nothing -> zonkTV v' (VarT v) >> pure Equal
        Just t' -> tryZonk unify v t'
      False -> pure $ if v == v'
        then Equal
        else Unknown $ matchError v v'
    _ -> pure $ Unknown $ matchError (VarT v) t'

unifyTyResultE
  :: MonadTc m
  => Bool -- ^ expand type familes?
  -> Type -> Type -> m UnifyResult
unifyTyResultE expand (VarT v) t' = tryZonk (unifyTyResultE expand) v t'
unifyTyResultE expand t (VarT v') = tryZonk (flip $ unifyTyResultE expand) v' t
unifyTyResultE expand (SigT t k) t' = do
  extractKind t' >>= unifyTy k
  unifyTyResultE expand t t'
unifyTyResultE expand t (SigT t' k') = do
  extractKind t >>= unifyTy k'
  unifyTyResultE expand t t'
unifyTyResultE expand t t' =
  liftA2 (,) (trySplitApp t) (trySplitApp t') >>= \case
    (App f x, App f' x') -> unifyTysResultE expand [f, x] [f', x']
    (FamApp cn args, r') -> tryExpandTyFam expand cn args >>= \case
      Just t -> unifyTyResultE expand t t'
      Nothing -> case r' of
        FamApp cn' args' -> tryExpandTyFam expand cn' args' >>= \case
          Just t' -> unifyTyResultE expand t t'
          Nothing -> plainUnifyTyResult t t'
        _ -> pure $ Unknown $ matchError t t'
    (_, FamApp cn' args') -> tryExpandTyFam expand cn' args' >>= \case
       Just t' -> unifyTyResultE expand t t'
       Nothing -> pure $ Unknown $ matchError t t'
    (SingleCon cn, SingleCon cn') -> pure $ if cn == cn'
      then Equal else Apart $ matchError cn cn'
    _ -> pure $ Apart $ matchError t t'
  where
    plainUnifyTyResult :: MonadTc m => Type -> Type -> m UnifyResult
    plainUnifyTyResult t t'
      | Just cn <- isConName t
      , Just cn' <- isConName t' = pure $ if cn == cn'
        then Equal else Apart $ matchError cn cn'
    plainUnifyTyResult t@(AppT f x) t'@(AppT f' x') =
      plainUnifyTyResult f f' >>= \case
        Apart _ -> pure $ Apart $ matchError t t'
        _ -> unifyTyResultE expand x x' >>= \case
          Apart _ -> pure $ Apart $ matchError t t'
          Unknown _ -> pure $ Unknown $ matchError t t'
          Equal -> pure Equal
    plainUnifyTyResult t t' = unifyTyResultE expand t t'

unifyTysResultE
  :: MonadTc m
  => Bool -- ^ expand type families?
  -> [Type] -> [Type] -> m UnifyResult
unifyTysResultE _ [] [] = pure Equal
unifyTysResultE expand (t:ts) (t':ts') = unifyTyResultE expand t t' >>= \case
  Apart err -> pure $ Apart err
  r -> unifyTysResultE expand ts ts' >>= \case
    Apart err -> pure $ Apart err
    Equal -> pure r
    rs -> pure rs
unifyTysResultE _ _ _ =
  pure $ Apart "Constructor applied to a different number of arguments"

-- | Attempt unification and return an indication of whether the types were
-- equal or not.
unifyTyResult :: MonadTc m => Type -> Type -> m UnifyResult
unifyTyResult = unifyTyResultE True

-- | Assert that two types are equal, and replace unificational variables as
-- necessary. Throws an error if the two types cannot be shown equal.
unifyTy :: MonadTc m => Type -> Type -> m ()
unifyTy t t' = unifyTyResult t t' >>= \case
  Equal -> pure ()
  Unknown err -> tcFail err
  Apart err -> tcFail err

-- | Attempt unifying two lists of types. If any two corresponding types in the
-- lists are apart, returns 'Apart'. If the lists are of different lengths,
-- returns 'Apart'.
unifyTysResult :: MonadTc m => [Type] -> [Type] -> m UnifyResult
unifyTysResult = unifyTysResultE True

-- | Assert that two lists of types are equal, replace unificational variables
-- as necessary. Throws an error if two corresponding types could not be shown
-- to be equal, or if lists have different lengths.
unifyTys :: MonadTc m => [Type] -> [Type] -> m ()
unifyTys [] [] = pure ()
unifyTys (t:ts) (t':ts') = unifyTy t t' >> unifyTys ts ts'
unifyTys _ _ = tcFail "Constructor applied to a different number of arguments"

-- | Recursively collect all zonked (unified with a type) unificational
-- variables in the type, into a substitution. This is a separate step because
-- we cannot actually replace the variables as the data structure is immutable.
extractSubst :: MonadTc m => Type -> m [(TV, Type)]
extractSubst x = go $ S.toList $ occurrences x
  where
    go [] = pure []
    go (v:vs) = isZonked v >>= \case
      Nothing -> go vs
      Just t -> ((v, t):) <$> go (S.toList (occurrences t) ++ vs)

-- | Recursively replace all zonked unificational variables in the type.
substZonked :: MonadTc m => Type -> m Type
substZonked (ForallT tvbs cxt ty) = ForallT
  <$> traverse instTVB tvbs
  <*> traverse substZonked cxt
  <*> substZonked ty
  where
    instTVB (PlainTV v) = pure $ PlainTV v
    instTVB (KindedTV v k) = KindedTV v <$> substZonked k
substZonked (AppT f x) = AppT <$> substZonked f <*> substZonked x
substZonked (SigT t k) = SigT <$> substZonked t <*> substZonked k
substZonked (VarT v) = isZonked v >>= \case
  Nothing -> pure $ VarT v
  Just t -> substZonked t
substZonked (InfixT x op y) = InfixT
  <$> substZonked x
  <*> pure op
  <*> substZonked y
substZonked (UInfixT x op y) = UInfixT
  <$> substZonked x
  <*> pure op
  <*> substZonked y
substZonked (ParensT t) = ParensT <$> substZonked t
substZonked t = pure t

-- | Attempt to compute the kind of a type. GHC doesn't give us complete kind
-- information so this migth be more general than expected.
extractKind :: MonadTc m => Type -> m Kind
extractKind (SigT t k') = do
  k <- extractKind t
  unifyTy k k'
  pure k
extractKind (VarT v) = isZonked v >>= \case
  Nothing -> tvKind v
  Just t -> extractKind t
extractKind t = trySplitApp t >>= \case
  FamApp cn args -> conInfo cn >>= \case
    TcFam{..} -> do
      (aks, rk) <- instantiate (famArgKinds, famResKind)
      aks' <- traverse extractKind args
      unifyTys aks aks'
      pure rk
    ci -> tcFail $ "extractKind " ++ show ci
  App f x -> do
    kf <- extractKind f
    k <- extractKind x
    kv <- freshUnifTV
    unifyTy kf (ArrowT `AppT` k `AppT` VarT kv)
    pure $ VarT kv
  SingleCon cn -> instantiate =<< tcConKind cn

unifyKind :: MonadTc m => Kind -> Type -> m ()
unifyKind k t = extractKind t >>= unifyTy k

kindUnifyDC :: MonadTc m => [Kind] -> Con -> m ()
kindUnifyDC _ (NormalC _ bts) =
  traverse_ (unifyKind StarT . snd) bts
kindUnifyDC _ (RecC _ vbts) =
  traverse_ (unifyKind StarT . \(_, _, t) -> t) vbts
kindUnifyDC _ (InfixC (_, x) _ (_, y)) = do
  unifyKind StarT x
  unifyKind StarT y
kindUnifyDC ks (ForallC _ cxt con) = do
  traverse_ (unifyKind ConstraintT) cxt
  kindUnifyDC ks con
kindUnifyDC ks (GadtC _ bts ty) = do
  traverse_ (unifyKind StarT . snd) bts
  case splitTyConApp ty of
    Just (_, args) -> sequence_ $ zipWith unifyKind ks args
    Nothing -> tcFail $ "Could not splitTyConApp " ++ show ty
kindUnifyDC ks (RecGadtC _ bts ty) = do
  traverse_ (unifyKind StarT . \(_, _, t) -> t) bts
  case splitTyConApp ty of
    Just (_, args) -> sequence_ $ zipWith unifyKind ks args
    Nothing -> tcFail $ "Could not splitTyConApp " ++ show ty

dataKind :: MonadTc m => Type -> m (Type, [Type])
dataKind (ForallT tvbs cxt t) = do
  traverse_ addTVB tvbs
  traverse_ extractKind cxt
  dataKind t
dataKind (ArrowT `AppT` t `AppT` ts) = do
  (k, ks) <- dataKind ts
  pure (k, t:ks)
dataKind t = case splitTyConApp t of
  Just _ -> pure (t, [])
  Nothing -> tcFail $ "dataKind " ++ show t

parseTySynEqn :: MonadTc m => TySynEqn -> m ([Type], Type)
parseTySynEqn (TySynEqn k lhs rhs) = error "no tysyns sorry" -- pure (lhs, rhs)

parseTyInst :: MonadTc m => Dec -> m AxBranch
parseTyInst (TySynInstD eqn) = parseTySynEqn eqn >>= \case
  (lhs, rhs) -> pure $ AxBranch
    { axLhs = lhs
    , axRhs = rhs
    , axIncomp = []
    }
parseTyInst dec = tcFail $ "parseTyInst " ++ show dec

checkIncomps :: MonadTc m => [([Type], Type)] -> m [AxBranch]
checkIncomps = go [] . zip [0..]
  where
    go _ [] = pure []
    go prev ((i, ax):axs) = do
      is <- check ax prev
      let
        ab = AxBranch
          { axLhs = fst ax
          , axRhs = snd ax
          , axIncomp = is
          }
      (ab:) <$> go ((i, ax):prev) axs
    check _ [] = pure []
    check ax ((i, ax'):axs) =
      compat ax ax' >>= \case
        True -> check ax axs
        False -> (i:) <$> check ax axs
    compat ax ax' = do
      ((lhs, rhs), (lhs', rhs')) <- instantiate (ax, ax')
      unifyTysResultE False {- there shouldn't be any -} lhs lhs' >>= \case
        Apart _ -> pure True
        Unknown _ -> pure False
        Equal -> skolemizing (rhs, rhs') (unifyTyResultE False rhs rhs') >>=
          \case
            Equal -> pure True
            _ -> pure False

tvOfTVB :: TyVarBndr -> TV
tvOfTVB (PlainTV tv) = tv
tvOfTVB (KindedTV tv _) = tv

conInfo :: MonadTc m => ConName -> m TcConInfo
conInfo ucn = normalizeConName ucn >>= \case
  Con con -> memoizedWith (tsTyCons . at (Con con)) $ \save -> do
    qReify con >>= \case
      TyConI dec -> case dec of
        DataD _ nm _ (Just k) _ _ | nm == con -> do
          roles <- qReifyRoles con
          save $ TcPlainCon
            { conKind = k
            , conRoles = roles
            }
        DataD cxt nm tvb Nothing dcs _ | nm == con -> do
          ks <- traverse addTVB tvb
          roles <- qReifyRoles con
          save $ TcPlainCon
            { conKind = mkArrow ks StarT
            , conRoles = roles
            }
          traverse_ extractKind cxt
          traverse_ (kindUnifyDC ks) dcs
        NewtypeD _ nm _ (Just k) _ _ | nm == con -> do
          roles <- qReifyRoles con
          save $ TcPlainCon
            { conKind = k
            , conRoles = roles
            }
        NewtypeD cxt nm tvb Nothing dc _ | nm == con -> do
          ks <- traverse addTVB tvb
          roles <- qReifyRoles con
          save $ TcPlainCon
            { conKind = mkArrow ks StarT
            , conRoles = roles
            }
          traverse_ extractKind cxt
          kindUnifyDC ks dc
        TySynD nm tvbs rhs | nm == con -> do
          ks <- traverse addTVB tvbs
          kv <- freshUnifTV
          save $ TcFam
            { famArgKinds = ks
            , famResKind = VarT kv
            , famAxioms = [[AxBranch
              { axLhs = VarT . tvOfTVB <$> tvbs
              , axRhs = rhs
              , axIncomp = []
              }]]
            }
          extractKind rhs >>= unifyTy (VarT kv)
        dec -> tcFail
          $ "Expected a newtype or data constructor, got " ++ show dec
      PrimTyConI nm arity _ | nm == con -> do
        save $ TcPlainCon
          { conKind = mkArrow (replicate arity StarT) StarT
          , conRoles = replicate arity NominalR
          }
      FamilyI (ClosedTypeFamilyD (TypeFamilyHead nm tvbs res _) axs) []
        | nm == con -> do
          ks <- traverse addTVB tvbs
          k <- case res of
            NoSig -> do
              kv <- freshUnifTV
              tvSetKind kv StarT
              pure $ VarT kv
            KindSig k -> pure k
            TyVarSig tvb -> addTVB tvb
          axb <- checkIncomps =<< traverse parseTySynEqn axs
          save $ TcFam
            { famArgKinds = ks
            , famResKind = k
            , famAxioms = [axb]
            }
      FamilyI (OpenTypeFamilyD (TypeFamilyHead nm tvbs res _)) axs
        | nm == con -> do
          ks <- traverse addTVB tvbs
          k <- case res of
            NoSig -> do
              kv <- freshUnifTV
              tvSetKind kv StarT
              pure $ VarT kv
            KindSig k -> pure k
            TyVarSig tvb -> addTVB tvb
          axioms <- traverse parseTyInst axs
          save $ TcFam
            { famArgKinds = ks
            , famResKind = k
            , famAxioms = L.map pure axioms
            }
      ClassI dec _ -> case dec of
        ClassD cxt nm tvbs _ _ | nm == con -> do
          ks <- traverse addTVB tvbs
          save $ TcCls
            { clsArgKinds = ks
            }
          traverse_ extractKind cxt
        dec -> tcFail $ "Expected a class, got " ++ show dec
      info -> tcFail $ "Expected a type constructor, got " ++ show info
  Promoted con -> memoizedWith (tsTyCons . at (Promoted con)) $ \save -> do
    qReify con >>= \case
      DataConI nm ty _ | nm == con -> do
        (k, ks) <- dataKind ty
        save $ TcPlainCon
          { conKind = mkArrow ks k
          , conRoles = replicate (length ks) RepresentationalR
          }
      info -> tcFail $ "Expected a data constructor, got " ++ show info
  LitCon (NumTyLit _) -> pure $ TcPlainCon
    { conKind = ConT name_Nat
    , conRoles = []
    }
  LitCon (StrTyLit _) -> pure $ TcPlainCon
    { conKind = ConT name_Symbol
    , conRoles = []
    }
  StarCon -> pure $ TcPlainCon
    { conKind = StarT
    , conRoles = []
    }

tcConKind :: MonadTc m => ConName -> m Kind
tcConKind con = conInfo con >>= \case
  TcPlainCon{..} -> pure conKind
  TcCls{..} -> pure $ mkArrow clsArgKinds ConstraintT
  i@TcFam{} -> tcFail $ "tcConKind " ++ show i

