module Main where

import App (app)
import App.Parser (parseAndSubst)
import System.Environment

main :: IO ()
main = do
  (_:inf:outf:_) <- getArgs
  file <- readFile inf
  let Right z = parseAndSubst file
  writeFile outf $ app z

