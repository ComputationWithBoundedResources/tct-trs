-- | This module re-exports some types and functionalities of Tct.Trs.Data.*.
module Tct.Trs.Data ( module M ) where

import Tct.Trs.Data.DependencyGraph as M (DependencyGraph, DG, CDG, NodeId)
import Tct.Trs.Data.Problem         as M (F, Problem, TrsProblem, V)
import Tct.Trs.Data.RuleSelector    as M (ExpressionSelector, RuleSelector)
import Tct.Trs.Data.RuleSet         as M (RuleSet)
import Tct.Trs.Data.Signature       as M (Signature, Symbols)
import Tct.Trs.Data.Trs             as M (Trs)

