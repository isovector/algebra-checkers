module App.Cleaning where

import AlgebraCheckers.Utils
import Data.Char
import Language.Haskell.Lexer


sanitizeSpan :: String -> String
sanitizeSpan = trimTrailingSpace . removeComments


trimTrailingSpace :: String -> String
trimTrailingSpace = dropEndWhile isSpace


rmSpace2 :: [PosToken] -> [PosToken]
rmSpace2 = filter $ notWhite . fst


notWhite :: Token -> Bool
notWhite t = t/=Commentstart && t/=Comment &&
             t/=NestedComment


removeComments :: String -> String
removeComments = foldMap (snd . snd) . rmSpace2 . lexerPass0

