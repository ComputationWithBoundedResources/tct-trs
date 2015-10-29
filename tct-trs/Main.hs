{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module Main (main) where

import Tct.Trs.Config
import Tct.Trs.Interactive

import qualified Tct.Core.Data as T
import Tct.Trs.Data
import Tct.Core.Data.Types (Declared (..))
import Tct.Trs.Declarations

instance Declared TrsProblem TrsProblem where
  decls = T.SD mystrat : trsDeclarations

mystrat :: T.Declaration ('[] T.:-> T.Strategy prob prob)
mystrat = T.strategy "xxx" () T.abort


main :: IO ()
main = trs trsConfig
  -- `setSolver` ("z3",[])
