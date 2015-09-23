module Main (main) where


import Tct.Trs.Data.Mode (trs, trsConfig)
import Tct.Trs.Interactive


main :: IO ()
main = trs $ trsConfig

