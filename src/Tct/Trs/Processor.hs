module Tct.Trs.Processor
  ( module M

  , defaultDeclarations

  -- * Abbreviations
  , (>>!)
  , (>>!!)
  , successive
  , whenNonTrivial
  , tew
  , selAny
  , selAnyRule
  , selAllRules

  -- * Strategies
  , dpsimps
  , decomposeIndependent
  , decomposeIndependentSG
  , cleanSuffix
  , toDP
  , removeLeaf
  ) where


import           Tct.Core
import qualified Tct.Core.Data                                   as T

import           Tct.Trs.Data
import qualified Tct.Trs.Data.DependencyGraph                    as DG
import qualified Tct.Trs.Data.Problem                            as Prob
import qualified Tct.Trs.Data.RuleSelector                       as RS
import qualified Tct.Trs.Data.RuleSet                            as Prob
import qualified Tct.Trs.Data.Trs                                as Trs

import qualified Tct.Trs.Method.ComplexityPair                   as CP

import           Tct.Trs.Method.Bounds                           as M
import           Tct.Trs.Method.Decompose                        as M
import           Tct.Trs.Method.DP.DependencyPairs               as M
import           Tct.Trs.Method.DP.DPGraph.DecomposeDG           as M
import           Tct.Trs.Method.DP.DPGraph.PathAnalysis          as M
import           Tct.Trs.Method.DP.DPGraph.PredecessorEstimation as M
import           Tct.Trs.Method.DP.DPGraph.RemoveHeads           as M
import           Tct.Trs.Method.DP.DPGraph.RemoveInapplicable    as M
import           Tct.Trs.Method.DP.DPGraph.RemoveWeakSuffixes    as M
import           Tct.Trs.Method.DP.DPGraph.SimplifyRHS           as M
import           Tct.Trs.Method.DP.DPGraph.Trivial               as M
import           Tct.Trs.Method.DP.UsableRules                   as M
import           Tct.Trs.Method.Empty                            as M
import           Tct.Trs.Method.EpoStar                          as M
import           Tct.Trs.Method.InnermostRuleRemoval             as M
import           Tct.Trs.Method.Matrix.NaturalMI                 as M
import           Tct.Trs.Method.Poly.NaturalPI                   as M
import           Tct.Trs.Method.ToInnermost                      as M
import           Tct.Trs.Method.WithCertification                as M


defaultDeclarations :: [T.StrategyDeclaration TrsProblem TrsProblem]
defaultDeclarations =
  [ T.SD emptyDeclaration
  , T.SD withCertificationDeclaration

  , T.SD decomposeDeclaration
  , T.SD decomposeCPDeclaration

  , T.SD boundsDeclaration

  , T.SD innermostRuleRemovalDeclaration
  , T.SD toInnermostDeclaration

  -- Path Orders
  , T.SD epoStarDeclaration

  -- Semantic
  , T.SD polyDeclaration
  , T.SD matrixDeclaration
  , T.SD weightGapDeclaration

  -- DP
  , T.SD dependencyPairsDeclaration
  , T.SD usableRulesDeclaration

  -- DP graph
  , T.SD decomposeDGDeclaration
  , T.SD pathAnalysisDeclaration
  , T.SD predecessorEstimationDeclaration
  , T.SD removeHeadsDeclaration
  , T.SD removeInapplicableDeclaration
  , T.SD removeWeakSuffixesDeclaration
  , T.SD simplifyRHSDeclaration
  , T.SD trivialDeclaration

  -- Simplifications
  , T.SD $ T.strategy "dpsimps"                () dpsimps
  , T.SD $ T.strategy "cleanSuffix"            () cleanSuffix
  , T.SD $ T.strategy "decomposeIndependent"   () decomposeIndependent
  , T.SD $ T.strategy "decomposeIndependentSG" () decomposeIndependentSG
  , T.SD $ T.strategy "toDP"                   () toDP
  , T.SD $ T.strategy "removeLeaf"             (OneTuple CP.complexityPairArg) removeLeaf
  ]


(>>!) :: TrsStrategy -> TrsStrategy -> TrsStrategy
s1 >>! s2 = s1 >>> try empty >>> s2

(>>!!) :: TrsStrategy -> TrsStrategy -> TrsStrategy
s1 >>!! s2 = s1 >>> try empty >||> s2

successive :: [TrsStrategy] -> TrsStrategy
successive = chainWith (try empty)

whenNonTrivial :: TrsStrategy -> TrsStrategy
whenNonTrivial st = withProblem $ \p ->
  if Prob.isTrivial p then M.empty else st

-- | >tew == te . whenNonTrivial
tew :: TrsStrategy -> TrsStrategy
tew = te . whenNonTrivial

-- | Select any strict rule.
selAny :: ExpressionSelector F V
selAny = RS.selAnyOf RS.selStricts

-- | Select any strict trs rule.
selAnyRule :: ExpressionSelector F V
selAnyRule = RS.selAnyOf $ RS.selStricts `RS.selInter` RS.selRules

-- | Select all strict trs rules.
selAllRules :: ExpressionSelector F V
selAllRules = RS.selAllOf RS.selRules

--- * simplifications ------------------------------------------------------------------------------------------------

-- | Fast simplifications based on dependency graph analysis.
dpsimps :: TrsStrategy
dpsimps = force $
  try cleanSuffix
  >>> te removeHeads
  >>> te removeInapplicable
  >>> try simplifyRHS
  >>> try usableRules
  >>> try trivial

-- | Use 'predecessorEstimationOn' and 'removeWeakSuffixes' to remove leafs from the dependency graph.
-- If successful, right-hand sides of dependency pairs are simplified ('simplifyRHS')
-- and usable rules are re-computed ('usableRules').
cleanSuffix :: TrsStrategy
cleanSuffix = force $
  te (predecessorEstimation sel)
  >>> try (removeWeakSuffixes >>> try (simplifyRHS >>> try usableRules))
  where
    sel = RS.selAllOf (RS.selFromWDG f) { RS.rsName = "simple predecessor estimation selector" }
    f wdg = Prob.emptyRuleSet { Prob.sdps = Trs.fromList rs }
      where rs = [ DG.theRule nl | (n,nl) <- DG.lnodes wdg, all (not . DG.isStrict . (\(_,l,_) -> l)) (DG.lsuccessors wdg n) ]

-- | Using the decomposition processor (c.f. 'Compose.decomposeBy') this transformation
-- decomposes dependency pairs into two independent sets, in the sense that these DPs
-- constitute unconnected sub-graphs of the dependency graph. Applies 'cleanSuffix' on the resulting sub-problems,
-- if applicable.
decomposeIndependent :: TrsStrategy
decomposeIndependent =
  decompose' (RS.selAllOf RS.selIndependentSG) RelativeAdd
  >>> try simplifyRHS
  >>> try cleanSuffix

-- | Similar to 'decomposeIndependent', but in the computation of the independent sets,
-- dependency pairs above cycles in the dependency graph are not taken into account.
decomposeIndependentSG :: TrsStrategy
decomposeIndependentSG =
  decompose' (RS.selAllOf RS.selCycleIndependentSG) RelativeAdd
  >>> try simplifyRHS
  >>> try cleanSuffix

-- | Tries dependency pairs for RC, and dependency pairs with weightgap, otherwise uses dependency tuples for IRC.
-- Simpifies the resulting DP problem as much as possible.
toDP :: TrsStrategy
toDP =
  try (withProblem toDP')
  >>> try usableRules
  >>> try removeInapplicable
  >>> try cleanSuffix
  >>> te removeHeads
  >>> try usableRules
  >>> te (withProblem partIndep)
  >>> try cleanSuffix
  >>> try trivial
  >>> try usableRules
  where
    toDP' prob
      -- | Prob.isInnermostProblem prob = timeoutIn 7 (dependencyPairs >>> try usableRules >>> wgOnUsable) <|> dependencyTuples
      | Prob.isInnermostProblem prob = timeoutIn 7 (dependencyPairs >>> try usableRules >>> shift) <|> dependencyTuples
      | otherwise                    = dependencyPairs >>> try usableRules >>> try wgOnUsable

    partIndep prob
      | Prob.isInnermostProblem prob = decomposeIndependentSG
      | otherwise                    = linearPathAnalysis

    shift = matrix' 2 1 Algebraic UArgs URules (Just $ RS.selAllOf $ RS.selStricts `RS.selInter` RS.selRules) NoGreedy
    wgOnUsable = failing

-- | Tries to remove leafs in the congruence graph,
-- by (i) orienting using predecessor extimation and the given processor,
-- and (ii) using 'DPSimp.removeWeakSuffix' and various sensible further simplifications.
-- Fails only if (i) fails.
removeLeaf :: ComplexityPair -> T.Strategy TrsProblem TrsProblem
removeLeaf cp =
  predecessorEstimationCP anyStrictLeaf cp
  >>> try (removeWeakSuffixes >>> try simplifyRHS)
  >>> try usableRules
  >>> try trivial
  where anyStrictLeaf = RS.selAnyOf $ RS.selLeafCDG `RS.selInter` RS.selStricts

