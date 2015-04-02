{-# LANGUAGE NoMonomorphismRestriction #-}
module Tct.Trs.Processor
  ( module M

  , defaultDeclarations

  , emptyDeclaration
  , empty

  , withCertificationDeclaration
  , withCertification
  , withCertification'

  -- * Strategies
  , dpsimps
  , decomposeIndependent
  , decomposeIndependentSG
  , cleanSuffix
  ) where


import           Control.Monad.Error                             (throwError)

import           Tct.Core
import qualified Tct.Core.Data                                   as T
import qualified Tct.Core.Processor.Empty                        as E

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Trs as Trs
import qualified Tct.Trs.Data.CeTA                               as CeTA
import qualified Tct.Trs.Data.Problem                            as Prob
import qualified Tct.Trs.Data.RuleSet                            as Prob
import qualified Tct.Trs.Data.RuleSelector                       as RS
import qualified Tct.Trs.Data.DependencyGraph                    as DG

import           Tct.Trs.Method.Bounds as M
import           Tct.Trs.Method.Decompose as M
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
import           Tct.Trs.Method.Poly.NaturalPI                   as M


defaultDeclarations :: [T.StrategyDeclaration TrsProblem]
defaultDeclarations =
  [ T.SD emptyDeclaration
  , T.SD withCertificationDeclaration

  , T.SD decomposeDeclaration

  , T.SD boundsDeclaration

  -- Semantic
  , T.SD polyDeclaration

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

empty :: T.Strategy TrsProblem
empty = E.empty Prob.isTrivial

emptyDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
emptyDeclaration = T.declare "empty" [desc] () empty
  where desc = "Checks if the the strict components is empty."


--- * withCertification ----------------------------------------------------------------------------------------------

data WithCertification =
  WithCertification { allowPartial :: Bool, onStrategy :: T.Strategy TrsProblem } deriving Show

-- TODO:
-- MS: the only way to stop a computation currently is using throwError;
-- we could extend the Continue type with Stop ?
instance T.Processor WithCertification where
  type ProofObject WithCertification = ()
  type Problem WithCertification     = TrsProblem

  solve p prob = do
    ret <- T.evaluate (onStrategy p) prob
    tmp <- T.tempDirectory `fmap` T.askState
    let
      toRet = case ret of
        T.Abort _    -> T.Abort
        T.Continue _ -> T.Continue
      prover
        | allowPartial p = CeTA.partialProofIO' tmp
        | otherwise      = CeTA.totalProofIO' tmp

    errM <- prover (T.fromReturn ret)
    either (throwError . userError) (return . toRet) errM

withCertificationStrategy :: Bool -> T.Strategy TrsProblem -> T.Strategy TrsProblem
withCertificationStrategy b st = T.Proc $ WithCertification { allowPartial=b, onStrategy=st }

withCertification :: Bool -> T.Strategy TrsProblem -> T.Strategy TrsProblem
withCertification = T.declFun withCertificationDeclaration

withCertification' :: T.Strategy TrsProblem -> T.Strategy TrsProblem
withCertification' = T.deflFun withCertificationDeclaration

withCertificationDeclaration :: T.Declaration(
  '[T.Argument 'T.Optional Bool
   , T.Argument 'T.Required (T.Strategy TrsProblem)]
   T.:-> T.Strategy TrsProblem)
withCertificationDeclaration = T.declare "withCertification" [desc] (apArg, T.strat) withCertificationStrategy
  where
    desc = "This processor "
    apArg = T.bool
      `T.withName` "allowPartial"
      `T.withHelp` ["Allow partial proofs."]
      `T.optional` False


--- * instances ------------------------------------------------------------------------------------------------------


-- | Fast simplifications based on dependency graph analysis.
dpsimps :: T.Strategy TrsProblem
dpsimps = force $
  try cleanSuffix
  >>> te removeHeads
  >>> te removeInapplicable
  >>> try simplifyRHS
  >>> try usableRules
  >>> try trivial

-- | Using the decomposition processor (c.f. 'Compose.decomposeBy') this transformation
-- decomposes dependency pairs into two independent sets, in the sense that these DPs
-- constitute unconnected sub-graphs of the dependency graph. Applies 'cleanSuffix' on the resulting sub-problems,
-- if applicable.
decomposeIndependent :: T.Strategy TrsProblem
decomposeIndependent =
  decomposeProc' (decomposeBy (RS.selAllOf RS.selIndependentSG))
  >>> try simplifyRHS
  >>> try cleanSuffix

-- | Similar to 'decomposeIndependent', but in the computation of the independent sets,
-- dependency pairs above cycles in the dependency graph are not taken into account.
decomposeIndependentSG :: T.Strategy TrsProblem
decomposeIndependentSG =
  decompose (RS.selAllOf RS.selCycleIndependentSG) RelativeAdd
  >>> try simplifyRHS
  >>> try cleanSuffix

-- | Use 'predecessorEstimationOn' and 'removeWeakSuffixes' to remove leafs from the dependency graph.
-- If successful, right-hand sides of dependency pairs are simplified ('simplifyRHS')
-- and usable rules are re-computed ('usableRules').
cleanSuffix :: T.Strategy TrsProblem
cleanSuffix = force $
  te (predecessorEstimation sel)
  >>> try (removeWeakSuffixes >>> try (simplifyRHS >>> try usableRules))
  where
    sel = RS.selAllOf (RS.selFromWDG f) { RS.rsName = "simple predecessor estimation selector" }
    f wdg = Prob.emptyRuleSet { Prob.sdps = Trs.fromList rs }
      where rs = [ DG.theRule nl | (n,nl) <- DG.lnodes wdg, all (not . DG.isStrict . (\(_,l,_) -> l)) (DG.lsuccessors wdg n) ]


-- | Tries to remove leafs in the congruence graph,
-- by (i) orienting using predecessor extimation and the given processor,
-- and (ii) using 'DPSimp.removeWeakSuffix' and various sensible further simplifications.
-- Fails only if (i) fails.
-- removeLeaf :: T.Strategy TrsProblem -> T.Strategy TrsProblem
-- removeLeaf  =
--   p `DPSimp.withPEOn` anyStrictLeaf -- TODO
--   >>> try (removeWeakSuffixes >>> try simplifyRHS)
--   >>> try usableRules
--   >>> try trivial
--   where anyStrictLeaf = RS.selAnyOf $ RS.selLeafCDG `RS.selInter` RS.selStricts

