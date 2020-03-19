module AlgebraCheckers.Types where

import Language.Haskell.TH

data Law a = Law
  { lawData :: a
  , lawLhsExp :: Exp
  , lawRhsExp :: Exp
  }


