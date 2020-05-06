module AlgebraCheckers.Utils where

dropEndWhile :: (a -> Bool) -> [a] -> [a]
dropEndWhile p = foldr (\x xs -> if p x && null xs then [] else x:xs) []
