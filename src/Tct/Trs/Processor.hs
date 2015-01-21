module Tct.Trs.Processor 
  ( 
  defaultDeclarations

  , empty
  , emptyDeclaration
  ) where


import qualified Tct.Core.Data            as T
import qualified Tct.Core.Processor.Empty as E

import           Tct.Trs.Data.Problem
import           Tct.Trs.Data.Xml         ()

import Tct.Trs.Method.DP.UsableRules (usableRulesDeclaration)
import Tct.Trs.Method.DP.DependencyPairs (dependencyPairsDeclaration, dependencyTuplesDeclaration)
import Tct.Trs.Method.Poly.NaturalPI (polyDeclaration)


defaultDeclarations :: [T.StrategyDeclaration Problem]
defaultDeclarations = 
  [ T.SD emptyDeclaration
  , T.SD usableRulesDeclaration
  , T.SD dependencyPairsDeclaration 
  , T.SD dependencyTuplesDeclaration 
  , T.SD polyDeclaration
  ]

empty :: T.Strategy Problem
empty = E.empty isTrivial

emptyDeclaration :: T.Declaration ('[] T.:-> T.Strategy Problem)
emptyDeclaration = T.declare "empty" [desc] () empty
  where desc = "Checks if the the strict components is empty."

