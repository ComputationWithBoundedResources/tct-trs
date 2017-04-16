-- {-# OPTIONS_GHC -fno-warn-unused-imports #-}
-- module Main (main) where

-- import Tct.Core
-- import Tct.Trs
-- import Tct.Trs.Interactive

-- instance Declared Trs Trs where decls = trsDeclarations

-- main :: IO ()
-- main = runTrs trsConfig
--   -- `setSolver` ("z3",[])


module Main (main) where

import           Tct.Core
import           Tct.Core.Data

import           Tct.Trs
import           Tct.Trs.Processor.Matrix.MI (eda')

instance Declared Trs Trs where decls = ds


main :: IO ()
main = runTrs trsConfig -- `setSolver` ("z3",[])

ds =
  trsDeclarations ++
  [ SD $ strategy "Cpolys"    args $ over pxs
  , SD $ strategy "Cmatrices" args $ over mxs
  , SD $ strategy "Cints"     args $ over ixs
  , SD $ strategy "Cara" () $ ara' NoHeuristics Nothing 1 3 60
  ]

args = (degreeArg `optional` 1, degreeArg `optional` 3)

px sha     = poly'   sha      NoRestrict UArgs URules Nothing
mx dim deg = matrix' dim deg  Algebraic  UArgs URules Nothing


-- MS: apply EDA alternatively
mxs 0 = mx 1 0
mxs 1 = mx 1 1 .<||> mx 2 1
mxs n = mx n n .<||> eda' n

-- MS: there was a bug in PI that restricted constants of constructors to 1
pxs 0 = px (Mixed 0)
pxs 1 = px StronglyLinear .<||> px Linear
pxs 2 = px Quadratic      .<||> px (Mixed 2)
pxs n = px (Mixed n)

ixs 0 = mxs 0
ixs 1 = mxs 1 .<||> px StronglyLinear
ixs 2 = mxs 2 .<||> pxs 2
ixs 3 = mxs 3 .<||> pxs 3
ixs n = mxs n

over f lb ub = fastest [ wait (max 0 (pred n)) (f n) | n <- [lb..ub] ]

