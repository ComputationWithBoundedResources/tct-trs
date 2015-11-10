{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module Main (main) where

import Tct.Core
import Tct.Trs
import Tct.Trs.Interactive

instance Declared Trs Trs where decls = trsDeclarations

main :: IO ()
main = runTrs trsConfig
  -- `setSolver` ("z3",[])
