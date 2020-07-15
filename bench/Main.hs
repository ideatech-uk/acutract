module Main where

import qualified Criterion.Main as Criterion
import qualified Frontend.Parser as Parser
import qualified FrontendDesugar
import Juvix.Library

main :: IO ()
main =
  Criterion.defaultMain
    [ Parser.bench,
      FrontendDesugar.bench
    ]
