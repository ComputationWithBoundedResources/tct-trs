-- | This module re-exports some types and functionalities of Tct.Trs.Data.*.
module Tct.Trs.Data 
  ( module M )
  where

import Tct.Trs.Data.Problem as M (Problem, F, V, TrsProblem)
import Tct.Trs.Data.Signature as M (Signature, Symbols)
import Tct.Trs.Data.Trs as M (Trs)
import Tct.Trs.Data.RuleSelector as M (RuleSelector, ExpressionSelector)
import Tct.Trs.Data.Xml as M ()

