-- | This module re-exports most types and some functionalities of Tct.Trs.Data.*.
module Tct.Trs.Data
  ( module M
  , TrsStrategy
  , TrsDeclaration
  ) where


import Tct.Trs.Data.DependencyGraph as M (DependencyGraph, DG, CDG, NodeId)
import Tct.Trs.Data.Problem         as M (Problem, Trs)
import Tct.Trs.Data.ProblemKind     as M (StartTerms, Strategy)
import Tct.Trs.Data.RuleSelector    as M (ExpressionSelector, RuleSelector)
import Tct.Trs.Data.RuleSet         as M (RuleSet)
import Tct.Trs.Data.Signature       as M (Signature, Symbols)
import Tct.Trs.Data.Symbol          as M (F, V, Fun)
import Tct.Trs.Data.Rules           as M (Rules)
import Tct.Trs.Data.ComplexityPair  as M (IsComplexityPair, ComplexityPair, ComplexityPairProof)
import Tct.Trs.Data.Precedence      as M (Order, Precedence)

import qualified Tct.Core.Data      as T

-- | Type synonym for Trs strategies.
type TrsStrategy    = T.Strategy Trs Trs

-- | Type synonym for Trs declarations.
type TrsDeclaration = T.StrategyDeclaration Trs Trs

