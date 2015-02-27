module Tct.Trs.Processor
  (
  defaultDeclarations

  , empty
  , emptyDeclaration

  , module M
  ) where


import           Control.Monad.Error                             (throwError)

import qualified Tct.Core.Data                                   as T
import qualified Tct.Core.Processor.Empty                        as E

import           Tct.Trs.Data
import qualified Tct.Trs.Data.CeTA                               as CeTA
import           Tct.Trs.Data.Problem                            (isTrivial)

import           Tct.Trs.Method.DP.DependencyPairs               as M
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

  -- Semantic
  , T.SD polyDeclaration

  -- DP
  , T.SD dependencyPairsDeclaration
  , T.SD dependencyTuplesDeclaration
  , T.SD usableRulesDeclaration
  
  -- DP graph
  , T.SD pathAnalysisDeclaration
  , T.SD predecessorEstimationOnDeclaration
  , T.SD removeHeadsDeclaration
  , T.SD removeInapplicableDeclaration
  , T.SD removeWeakSuffixesDeclaration
  , T.SD simplifyRHSDeclaration
  , T.SD trivialDeclaration
  ]

empty :: T.Strategy TrsProblem
empty = E.empty isTrivial

emptyDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
emptyDeclaration = T.declare "empty" [desc] () empty
  where desc = "Checks if the the strict components is empty."


--- * withCertification ----------------------------------------------------------------------------------------------

data WithCertificationProcessor =
  WithCertificationProc { allowPartial :: Bool, onStrategy :: T.Strategy TrsProblem } deriving Show

-- TODO:
-- MS: the only way to stop a computation currently is using throwError;
-- we could extend the Continue type with Stop ?
instance T.Processor WithCertificationProcessor where
  type ProofObject WithCertificationProcessor = ()
  type Problem WithCertificationProcessor     = TrsProblem

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

withCertification :: Bool -> T.Strategy TrsProblem -> T.Strategy TrsProblem
withCertification b = T.Proc . WithCertificationProc b

withCertificationDeclaration :: T.Declaration(
  '[T.Argument 'T.Optional Bool
   , T.Argument 'T.Required (T.Strategy TrsProblem)]
   T.:-> T.Strategy TrsProblem)
withCertificationDeclaration = T.declare "withCertification" [desc] (apArg, T.strat) withCertification
  where
    desc = "This processor "
    apArg = T.bool
      `T.withName` "allowPartial"
      `T.withHelp` ["Allow partial proofs."]
      `T.optional` False

