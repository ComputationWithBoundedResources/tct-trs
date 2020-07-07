module Raml where

import           Tct.Core
import qualified Tct.Core.Data                as T

import           Tct.Trs.Data
import qualified Tct.Trs.Data.DependencyGraph as DG
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.Rules           as RS
import           Tct.Trs.Processor.Matrix.MI  as MI (mxeda, mxida)
import           Tct.Trs.Processors


-- import Tct.Interactive
-- import Tct.Instances hiding (toDP)
-- import qualified Termlib.Repl as TR
-- import Tct.Configuration
-- import qualified Tct.Method.DP.DependencyGraph as DG
-- import Abbrevs


toDP =
  (dependencyTuples <> (dependencyPairs >>> try usableRules >>> try (wg 2 1 `wgOn` WgOnTrs)))
  >>> try removeInapplicable
  >>> try simpDP

simpDP =
  try cleanSuffix
  >>> te decomposeIndependentSG
  >>> te removeHeads
  >>> try trivial
  >>> try usableRules

semantic methods i = whenNonTrivial $
  (when (PopStar `elem` methods) (peAny (spopstarPS `withDegree` Just i)))
  <||>
  (when (Matrices `elem` methods)
   (peAny (mx i i)
    <||> peAny (mx (i + 1) i)
    <||> when (i == 1) (peAny (mx 3 1)
                        <||> peAny (mx 3 1 `withBits` 3)))
   <||> when (Polys `elem` methods && (i == 2 || i == 3)) (peAny (poly `withDegree` Just i)))
  where peAny p = p `withPEOn` selAnyOf (selLeafCWDG `selInter` selStricts) >>> try cleanUpTail

semantic' = semantic [PopStar, Matrices, Polys]


semantics methods maxdeg maybeTO = force $ te (shift maxdeg)
  where
    shift 0 = some $ rl 0
    shift n = some $ shift (n - 1) <> rl n

    rl = withTO . semantic methods

    withTO t = maybe (some t) (\ (Nat n) -> some $ timeout n t) maybeTO

semantics' = semantics [PopStar, Matrices, Polys] 2 Nothing

decomposeFC methods maxdeg maybeTO =
  timed $
  decomposeDG `solveUpperWith` (try simpDPRHS
                                >>> try simpDP
                                >>> try shiftDPs
                                >>| empty)
  >>> te decomposeIndependentSG >>> try simpDP
  where
    shiftDPs = semantics methods maxdeg maybeTO

decomposeFC' maxdeg = decomposeFC [PopStar,Matrices,Polys] maxdeg Nothing

raml (maybeTO :+: greedy :+: Nat maxdeg :+: basetechniques) =
  try toInnermost
  >>> try toDP
  >>> te (timeout 3 (decomposeAnyWith $ poly `withDegree` Just 2))
  >>> try shiftRulesSuccessively
  >>!! timed decomposing
  where
    peAny p = p `withPEOn` selAnyOf (selLeafCWDG `selInter` selStricts)
    decomposing
      | greedy = some $
                 te decomp >>> try shiftDPs >>!! empty
      | otherwise = some $
                    try shiftDPs >>!! iteProgress decomp decomposing empty
    shiftDPs = semantics basetechniques maxdeg maybeTO
    decomp   = decomposeFC basetechniques maxdeg maybeTO

