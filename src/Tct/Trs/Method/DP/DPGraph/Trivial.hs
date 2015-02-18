module Tct.Trs.Method.DP.DPGraph.Trivial
  ( trivial
  , trivialDeclaration
  ) where


import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import           Tct.Trs.Data.DependencyGraph as DG (isCyclicNode, nodes, empty)
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.Trs             as Trs (empty)


data TrivialProcessor = TrivialProc deriving Show

data TrivialProof
  = TrivialProof { wdg_ :: DG F V }
  | TrivialFail
  deriving Show

instance T.Processor TrivialProcessor where
  type ProofObject TrivialProcessor = ApplicationProof TrivialProof
  type Problem TrivialProcessor     = TrsProblem

  solve p prob = return . T.resultToTree p prob $
    maybe cyclic (T.Fail . Inapplicable) (Prob.isDTProblem' prob)
    where
      cyclic
        | any (isCyclicNode cdg) (nodes cdg) = T.Fail (Applicable TrivialFail)
        | otherwise                          = T.Success (T.toId nprob) (Applicable proof) T.fromId
        where
          cdg = Prob.congruenceGraph prob

          nprob = Prob.sanitiseSignature $ prob
            { Prob.strictDPs = Trs.empty
            , Prob.weakDPs   = Trs.empty
            , Prob.dpGraph   = DG.empty }
          proof = TrivialProof { wdg_ = Prob.dependencyGraph prob }


--- * instances ------------------------------------------------------------------------------------------------------

-- | Checks whether the DP problem is trivial, i.e., does not contain any cycles.
--
-- Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'. Also
-- not applicable when @strictTrs prob \= Trs.empty@.
trivialDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
trivialDeclaration = T.declare "trivial" desc () trivial where
  desc =
    [ "Checks wether the DP problem is trivial, i.e. the dependency graph contains no loops."
    , "Only applicable if the strict component is empty."]

trivial :: T.Strategy TrsProblem
trivial = T.Proc TrivialProc


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty TrivialProof where
  pretty TrivialFail      = PP.text "The problem is not trivial."
  pretty p@TrivialProof{} = PP.vcat
    [ PP.text "Consider the dependency graph"
    , PP.empty
    , PP.pretty (wdg_ p)
    , PP.empty
    , PP.text "The dependency graph contains no loops, we remove all dependency pairs." ]

instance Xml.Xml TrivialProof where
  toXml TrivialFail      = Xml.elt "trivial" []
  toXml p@TrivialProof{} = Xml.elt "trivial" [Xml.toXml $ wdg_ p]

