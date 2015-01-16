module Main (main) where


import Tct.Core

import Tct.Trs.Data.Mode (trsMode)
import Tct.Trs.Processor (defaultSD)


main :: IO ()
main = apply defaultTctConfig $ trsMode `withStrategies` defaultSD

