module Tct.Trs.Processors
  ( module M

  -- * Arguments
  , Degree
  , degreeArg
  , boundedArgs
  , araArgs
  , checkPropArgs
  , timeoutArg
  , CombineWith (..)
  , combineWithArg

  -- * Abbreviations
  , (.>>!)
  , (.>>!!)
  , successive
  , whenNonTrivial
  , tew
  , selAny
  , selAnyRule
  , selAllRules

  -- * Basic Strategies
  , matchbounds
  , matrices
  , polys
  , ints
  , araBounds
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
import qualified Tct.Trs.Data.Rules as RS

-- MS: FIXME:
-- naming of arguments/methods gets increasingly more difficult
-- should they be imported qualified?
import Tct.Trs.Processor.AmortisedAnalysis as M
import           Tct.Trs.Processor.Bounds                           as M
import           Tct.Trs.Processor.Decompose                        as M
import           Tct.Trs.Processor.ComplexityPair                   as M
import           Tct.Trs.Processor.DecreasingLoops                  as M
import           Tct.Trs.Processor.DP.DependencyPairs               as M
import           Tct.Trs.Processor.DP.DPGraph.DecomposeDG           as M
import           Tct.Trs.Processor.DP.DPGraph.PathAnalysis          as M
import           Tct.Trs.Processor.DP.DPGraph.PredecessorEstimation as M
import           Tct.Trs.Processor.DP.DPGraph.RemoveHeads           as M
import           Tct.Trs.Processor.DP.DPGraph.RemoveInapplicable    as M
import           Tct.Trs.Processor.DP.DPGraph.RemoveWeakSuffixes    as M
import           Tct.Trs.Processor.DP.DPGraph.SimplifyRHS           as M
import           Tct.Trs.Processor.DP.DPGraph.Trivial               as M
import           Tct.Trs.Processor.DP.UsableRules                   as M
import           Tct.Trs.Processor.Empty                            as M
import           Tct.Trs.Processor.EpoStar                          as M
import           Tct.Trs.Processor.InnermostRuleRemoval             as M
import           Tct.Trs.Processor.Matrix.NaturalMI                 as M
import           Tct.Trs.Processor.Poly.NaturalPI                   as M
import           Tct.Trs.Processor.ToInnermost                      as M
import           Tct.Trs.Processor.WithCertification                as M

-- processor for checking properties
import Tct.Trs.Processor.CheckProperty as M

-- TODO: MS: move to strategies?

type Degree = Int

-- | Argument for degree. @:degree nat@
degreeArg :: Argument 'Required T.Nat
degreeArg = nat "degree" ["set max degree"]

-- | Arguments for bounded degrees. @:form nat :to nat@
boundedArgs :: (Argument 'Optional T.Nat, Argument 'Optional T.Nat)
boundedArgs = (lArg `T.optional` 1, uArg `T.optional` 1)
  where
    lArg = nat "from" ["from degree"]
    uArg = nat "to"   ["to degree"]

-- | Arguments for bounded degrees. @:form nat :to nat@
araArgs :: (Argument 'Optional T.Nat, Argument 'Optional T.Nat, Argument 'Optional T.Nat)
araArgs = (lArg `T.optional` 1, uArg `T.optional` 3, tArg `T.optional` 60)
  where
    lArg = nat "from" ["from degree"]
    uArg = nat "to"   ["to degree"]
    tArg = nat "timeout" ["timeout for SMT solver"]


checkPropArgs :: (Argument 'Optional LogOp,
                  Argument 'Optional (Maybe LL), Argument 'Optional (Maybe Ctr))
checkPropArgs = ( checkPropLogOpArg `T.optional` AND
                , checkPropLLArg    `T.optional` Nothing
                , checkPropCtrArg   `T.optional` Nothing)


-- | Argument for timeout. @:timeout nat@
timeoutArg :: Argument 'Required T.Nat
timeoutArg = nat "timeout" ["set a timeout"]

-- | Parsable Flag. Usually used to dynamically select 'fastest' or 'best' combinator.
data CombineWith = Best | Fastest    deriving (Show, Enum, Bounded)

-- | Argument for combine. @combine <Best|Fastest>@
combineWithArg :: Argument 'Required CombineWith
combineWithArg = T.flag "combineWith" ["Set race conditions."]


(.>>!) :: TrsStrategy -> TrsStrategy -> TrsStrategy
s1 .>>! s2 = s1 .>>> try empty .>>> s2

(.>>!!) :: TrsStrategy -> TrsStrategy -> TrsStrategy
s1 .>>!! s2 = s1 .>>> try empty .>||> s2

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


--- * default matchbounds --------------------------------------------------------------------------------------------
matchbounds :: TrsStrategy
matchbounds = bounds Minimal Match .<||> bounds PerSymbol Match


--- * interpretations ------------------------------------------------------------------------------------------------

mxs0,mxs1,mxs2,mxs3,mxs4 :: TrsStrategy
mxs0 = mx 1 0 .<||> wg 1 0
mxs1 = mx 1 1 .<||> mx 2 1 .<||> mx 3 1 .<||> wg 2 1 .<||> wg 1 1
mxs2 = mx 2 2 .<||> mx 3 2 .<||> mx 4 2 .<||> wg 2 2
mxs3 = mx 3 3 .<||> mx 4 3 .<||> wg 3 3
mxs4 = mx 4 4 .<||> wg 4 4

mxs :: Int -> TrsStrategy
mxs 0 = mxs0
mxs 1 = mxs1
mxs 2 = mxs2
mxs 3 = mxs3
mxs 4 = mxs4
mxs n = mx n n

px :: Shape -> Restrict -> TrsStrategy
px sh res = poly' sh res UArgs URules (Just selAny)

pxs0, pxs1, pxs2 :: TrsStrategy
pxs0 = px (Mixed 0) NoRestrict
pxs1 = px StronglyLinear NoRestrict .<||> px Linear NoRestrict
pxs2 = px Quadratic NoRestrict .<||> px (Mixed 2) NoRestrict

pxs :: Int -> TrsStrategy
pxs 0 = pxs0
pxs 1 = pxs1
pxs 2 = pxs2
pxs n = px (Mixed n) Restrict

ixs :: Int -> TrsStrategy
ixs 0 = mxs 0
ixs 1 = mxs 1
ixs 2 = mxs 2 .<||> pxs 2
ixs 3 = mxs 3 .<||> pxs 3
ixs n = mxs n

shift :: (Degree -> TrsStrategy) -> Degree -> Degree -> TrsStrategy
shift s l u = chain [ tew (s n) | n <- [max 0 (min l u)..max 0 u] ]

mx,wg :: Degree -> Degree -> TrsStrategy
mx dim deg = matrix' dim deg Automaton UArgs URules (Just selAny)
wg dim deg = weightgap' dim deg Algebraic UArgs WgOnAny

-- | Like 'ints' but applies only matrix interpretations.
matrices :: Degree -> Degree -> TrsStrategy
matrices = shift mxs

-- | Like 'ints' but applies only polynomial interpretations.
polys :: Degree -> Degree -> TrsStrategy
polys = shift pxs

-- | Applies a selection of interpretations, depending on the given lower and uppper bound.
ints :: Degree -> Degree -> TrsStrategy
ints = shift ixs

araBounds :: Degree -> Degree -> Int -> TrsStrategy
araBounds = ara' NoHeuristics Nothing


--- * simplifications ------------------------------------------------------------------------------------------------

-- | Fast simplifications based on dependency graph analysis.
dpsimps :: TrsStrategy
dpsimps = force $
  try cleanSuffix
  .>>> te removeHeads
  .>>> te removeInapplicable
  .>>> try simplifyRHS
  .>>> try usableRules
  .>>> try trivial

-- | Use 'predecessorEstimationOn' and 'removeWeakSuffixes' to remove leafs from the dependency graph.
-- If successful, right-hand sides of dependency pairs are simplified ('simplifyRHS')
-- and usable rules are re-computed ('usableRules').
cleanSuffix :: TrsStrategy
cleanSuffix = force $
  te (predecessorEstimation sel)
  .>>> try (removeWeakSuffixes .>>> try (simplifyRHS .>>> try usableRules))
  where
    sel = RS.selAllOf (RS.selFromWDG f) { RS.rsName = "simple predecessor estimation selector" }
    f wdg = Prob.emptyRuleSet { Prob.sdps = RS.fromList rs }
      where rs = [ DG.theRule nl | (n,nl) <- DG.lnodes wdg, all (not . DG.isStrict . (\(_,l,_) -> l)) (DG.lsuccessors wdg n) ]

-- | Using the decomposition processor (c.f. 'Compose.decomposeBy') this transformation
-- decomposes dependency pairs into two independent sets, in the sense that these DPs
-- constitute unconnected sub-graphs of the dependency graph. Applies 'cleanSuffix' on the
-- resulting sub-problems, if applicable.
decomposeIndependent :: TrsStrategy
decomposeIndependent =
  decompose' (RS.selAllOf RS.selIndependentSG) RelativeAdd
  .>>> try simplifyRHS
  .>>> try cleanSuffix

-- | Similar to 'decomposeIndependent', but in the computation of the independent sets,
-- dependency pairs above cycles in the dependency graph are not taken into account.
decomposeIndependentSG :: TrsStrategy
decomposeIndependentSG =
  decompose' (RS.selAllOf RS.selCycleIndependentSG) RelativeAdd
  .>>> try simplifyRHS
  .>>> try cleanSuffix

-- | Tries dependency pairs for RC, and dependency pairs with weightgap, otherwise uses dependency tuples for IRC.
-- Simpifies the resulting DP problem as much as possible.
toDP :: TrsStrategy
toDP =
  try (withProblem toDP')
  .>>> try usableRules
  .>>> try removeInapplicable
  .>>> try cleanSuffix
  .>>> te removeHeads
  .>>> try usableRules
  .>>> te (withProblem partIndep)
  .>>> try cleanSuffix
  .>>> try trivial
  .>>> try usableRules
  where
    toDP' prob
      -- | Prob.isInnermostProblem prob = timeoutIn 7 (dependencyPairs .>>> try usableRules >>> wgOnUsable) .<|> dependencyTuples
      | Prob.isInnermostProblem prob = timeoutIn 7 (dependencyPairs .>>> try usableRules .>>> shiftt) .<|> dependencyTuples
      | otherwise                    = dependencyPairs .>>> try usableRules .>>> try wgOnUsable

    partIndep prob
      | Prob.isInnermostProblem prob = decomposeIndependentSG
      | otherwise                    = linearPathAnalysis

    shiftt = matrix' 2 1 Algebraic UArgs URules (Just $ RS.selAllOf $ RS.selStricts `RS.selInter` RS.selRules)
    wgOnUsable = abort

-- | Tries to remove leafs in the congruence graph,
-- by (i) orienting using predecessor extimation and the given processor,
-- and (ii) using 'DPSimp.removeWeakSuffix' and various sensible further simplifications.
-- Fails only if (i) fails.
removeLeaf :: ComplexityPair -> T.Strategy Trs Trs
removeLeaf cp =
  predecessorEstimationCP anyStrictLeaf cp
  .>>> try (removeWeakSuffixes .>>> try simplifyRHS)
  .>>> try usableRules
  .>>> try trivial
  where anyStrictLeaf = RS.selAnyOf $ RS.selLeafCDG `RS.selInter` RS.selStricts


