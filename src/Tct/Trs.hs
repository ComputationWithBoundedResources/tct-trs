{-| This module re-exports most common types and strategies for generating executables and custom strategies.

An example executable that adds a custom strategy to the default strategies `trsDeclarations`:

@
module Main (main) where

import Tct.Core
import Tct.Trs


instance Declared Trs Trs where decls = lints :trsDeclarations

main :: IO ()
main = runTrs trsConfig
  -- `setSolver` ("z3",[])

-- use polynomial and matrix interpretations of a certain degree
lints = SD $ strategy "lints" (OneTuple degreeArg) $ \deg ->
  polys deg deg .<||> matrices deg deg

@

The custom strategy can then be accessesd over the command line via.

>>> tct-trs -s lints problem.trs

-}
module Tct.Trs (module M) where

import Tct.Trs.Config       as M (runTrs, TrsConfig, trsConfig, setSolver)
import Tct.Trs.Data         as M
import Tct.Trs.Strategies   as M

