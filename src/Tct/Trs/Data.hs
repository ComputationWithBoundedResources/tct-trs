-- | This module re-exports some types and functionalities of Tct.Trs.Data.*.
module Tct.Trs.Data 
  ( module M 
  , TrsStrategy
  ) where


import Tct.Trs.Data.DependencyGraph as M (DependencyGraph, DG, CDG, NodeId)
import Tct.Trs.Data.Problem         as M (Problem, TrsProblem)
import Tct.Trs.Data.ProblemKind     as M (StartTerms, Strategy)
import Tct.Trs.Data.RuleSelector    as M (ExpressionSelector, RuleSelector)
import Tct.Trs.Data.RuleSet         as M (RuleSet)
import Tct.Trs.Data.Signature       as M (Signature, Symbols)
import Tct.Trs.Data.Symbol          as M (F, V, Fun)
import Tct.Trs.Data.Trs             as M (Trs)
import Tct.Trs.Data.ComplexityPair  as M (IsComplexityPair, ComplexityPair, ComplexityPairProof)

import qualified Tct.Core.Data      as T

type TrsStrategy = T.Strategy TrsProblem TrsProblem

