module Tct.Trs.Processor 
  ( 
  defaultSD 

  , empty
  , emptySD
  ) where


import qualified Tct.Core.Data            as T
import qualified Tct.Core.Processor.Empty as E

import           Tct.Trs.Data.Problem
import           Tct.Trs.Data.Xml         ()


defaultSD :: [T.StrategyDeclaration Problem]
defaultSD = 
  [ T.SD emptySD ]


empty :: T.Strategy Problem
empty = E.empty isTrivial

emptySD :: T.Declaration ('[] T.:-> T.Strategy Problem)
emptySD = T.declare "empty" [desc] () empty
  where desc = "Checks if the the strict components is empty."

