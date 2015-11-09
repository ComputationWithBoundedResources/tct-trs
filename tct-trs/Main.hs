{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module Main (main) where

import Tct.Trs.Config
import Tct.Trs.Interactive

import Tct.Trs.Data
import Tct.Core
import Tct.Trs.Declarations

instance Declared Trs Trs where
  decls = trsDeclarations

main :: IO ()
main = trs trsConfig
  -- `setSolver` ("z3",[])
