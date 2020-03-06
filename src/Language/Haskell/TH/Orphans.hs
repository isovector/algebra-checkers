{-# LANGUAGE DeriveLift         #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.Haskell.TH.Orphans where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax


deriving instance Lift AnnTarget
deriving instance Lift Bang
deriving instance Lift Body
deriving instance Lift Callconv
deriving instance Lift Clause
deriving instance Lift Con
deriving instance Lift Dec
deriving instance Lift DerivClause
deriving instance Lift DerivStrategy
deriving instance Lift Exp
deriving instance Lift FamilyResultSig
deriving instance Lift Fixity
deriving instance Lift FixityDirection
deriving instance Lift Foreign
deriving instance Lift FunDep
deriving instance Lift Guard
deriving instance Lift InjectivityAnn
deriving instance Lift Inline
deriving instance Lift Lit
deriving instance Lift Match
deriving instance Lift ModName
deriving instance Lift Name
deriving instance Lift NameFlavour
deriving instance Lift NameSpace
deriving instance Lift OccName
deriving instance Lift Overlap
deriving instance Lift Pat
deriving instance Lift PatSynArgs
deriving instance Lift PatSynDir
deriving instance Lift Phases
deriving instance Lift PkgName
deriving instance Lift Pragma
deriving instance Lift Range
deriving instance Lift Role
deriving instance Lift RuleBndr
deriving instance Lift RuleMatch
deriving instance Lift Safety
deriving instance Lift SourceStrictness
deriving instance Lift SourceUnpackedness
deriving instance Lift Stmt
deriving instance Lift TyLit
deriving instance Lift TySynEqn
deriving instance Lift TyVarBndr
deriving instance Lift Type
deriving instance Lift TypeFamilyHead

