module Tct.Trs.Method.DP.DPGraph.Trivial
  ( trivial
  , trivialDeclaration
  ) where


import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import           Tct.Trs.Data.DependencyGraph (isCyclicNode, nodes)
import qualified Tct.Trs.Data.Problem         as Prob


data TrivialProcessor = TrivialProc deriving Show

data TrivialProof
  = TrivialFail
  | TrivialProof
    { trivialDG  :: DG F V    -- ^ Employed dependency graph
    , trivialCDG :: CDG F V   -- ^ Employed congruence graph
  } deriving Show

instance T.Processor TrivialProcessor where
  type ProofObject TrivialProcessor = ApplicationProof TrivialProof
  type Problem TrivialProcessor     = TrsProblem
  type Forking TrivialProcessor     = T.Judgement

  solve p prob = return . T.resultToTree p prob $
    maybe cyclic (T.Fail . Inapplicable) (Prob.isDTProblem' prob)
    where
      cyclic
        | any (isCyclicNode cdg) (nodes cdg)
          = T.Success T.Judgement (Applicable $ TrivialProof wdg cdg) (T.judgement $ T.timeUBCert T.constant)
        | otherwise = T.Fail (Applicable TrivialFail)

      wdg = Prob.dependencyGraph prob
      cdg = Prob.congruenceGraph prob


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
  pretty TrivialFail    = PP.text "The problem is not trivial."
  pretty TrivialProof{} = PP.text "The dependency graph contains no loops, we remove all dependency pairs."

instance Xml.Xml TrivialProof where
  toXml = undefined

