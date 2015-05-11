module Tct.Trs.Processor
  ( module M

  , defaultDeclarations

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
-- import qualified Tct.Trs.Data.ComplexityPair                    as CP

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
import           Tct.Trs.Method.InnermostRuleRemoval             as M
import           Tct.Trs.Method.Matrix.NaturalMI                 as M
import           Tct.Trs.Method.Poly.NaturalPI                   as M
import           Tct.Trs.Method.WithCertification                as M


defaultDeclarations :: [T.StrategyDeclaration TrsProblem TrsProblem]
defaultDeclarations =
  [ T.SD emptyDeclaration
  , T.SD withCertificationDeclaration

  , T.SD decomposeDeclaration

  , T.SD boundsDeclaration

  , T.SD innermostRuleRemovalDeclaration

  -- Semantic
  , T.SD polyDeclaration
  , T.SD matrixDeclaration

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
  ]



--- * instances ------------------------------------------------------------------------------------------------------


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
  decompose (RS.selAllOf RS.selIndependentSG) RelativeAdd
  >>> try simplifyRHS
  >>> try cleanSuffix

-- | Similar to 'decomposeIndependent', but in the computation of the independent sets,
-- dependency pairs above cycles in the dependency graph are not taken into account.
decomposeIndependentSG :: TrsStrategy
decomposeIndependentSG =
  decompose (RS.selAllOf RS.selCycleIndependentSG) RelativeAdd
  >>> try simplifyRHS
  >>> try cleanSuffix

-- | Tries dependency pairs for RC, and dependency pairs with weightgap, otherwise uses dependency tuples for IRC.
-- Simpifies the resulting DP problem as much as possible.
toDP :: TrsStrategy
toDP =
  try (withProblem toDP')
  >>> try removeInapplicable
  >>> try cleanSuffix
  >>> te removeHeads
  >>> te (withProblem partIndep)
  >>> try cleanSuffix
  >>> try trivial
  >>> try usableRules
  where
    toDP' prob
      | Prob.isInnermostProblem prob = timeoutIn 5 (dependencyPairs >>> try usableRules >>> wgOnUsable) <|> dependencyTuples
      | otherwise = dependencyPairs >>> try usableRules >>> try wgOnUsable

    partIndep prob
      | Prob.isInnermostProblem prob = decomposeIndependentSG
      | otherwise                    = linearPathAnalysis

    wgOnUsable = failing -- TODO: weightgap `wgOn` Weightgap.WgOnTrs

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

