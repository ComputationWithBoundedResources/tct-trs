
-- | This module provides the /Empty/ processor.
module Tct.Trs.Method.Empty
  ( emptyDeclaration
  , empty
  ) where

import qualified Tct.Core.Processor.Empty                        as E
import qualified Tct.Core.Data as T

import qualified Tct.Trs.Data.Problem as Prob
import Tct.Trs.Data

empty :: T.Strategy TrsProblem
empty = E.empty Prob.isTrivial

emptyDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
emptyDeclaration = T.declare "empty" [desc] () empty
  where desc = "Checks if the the strict components is empty."

