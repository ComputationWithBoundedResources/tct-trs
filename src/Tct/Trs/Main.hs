module Main (main) where


import Tct.Core

import Tct.Trs.Data.Mode (trsMode)
import Tct.Trs.Processor (defaultDeclarations)


main :: IO ()
main = setMode $ trsMode `withStrategies` defaultDeclarations

