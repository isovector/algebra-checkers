module AlgebraCheckers.Utils where

import           Language.Haskell.TH.Syntax

dropEndWhile :: (a -> Bool) -> [a] -> [a]
dropEndWhile p = foldr (\x xs -> if p x && null xs then [] else x:xs) []

sloppy :: Name -> Name
sloppy = mkName . nameBase
