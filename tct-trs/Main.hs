{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module Main (main) where

import Tct.Trs.Config
import Tct.Trs.Interactive

main :: IO ()
main = trs trsConfig
  -- `setSolver` ("z3",[])
