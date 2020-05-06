module Main where

import qualified App as A
import System.Environment

main :: IO ()
main = do
  (_:inf:outf:_) <- getArgs
  file <- readFile inf
  let Right z = A.parseAndSubst file
  writeFile outf
    . A.dumpStuffMap
    . A.addHeader "{-# LANGUAGE TemplateHaskell #-}"
    . A.addImport "Test.QuickCheck"
    $ A.buildStuffMap z

