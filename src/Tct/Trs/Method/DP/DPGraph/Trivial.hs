{- | This module provides the /Trivial/ processor.

Suppose the dependency graph contains no /non-trivial SCC/, then
@
    |- <   /      W, Q, T#> :f
  -------------------------------------
    |- <S# / W# + W, Q, T#> :f
@
-}
module Tct.Trs.Method.DP.DPGraph.Trivial
  ( trivialDeclaration
  , trivial
  ) where


import           Tct.Core                     ((.>>>))
import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import           Tct.Trs.Data.DependencyGraph as DG (isCyclicNode, nodes, empty)
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.Rules as RS
import qualified Tct.Trs.Method.Empty         as E (empty)


data Trivial = Trivial deriving Show

data TrivialProof
  = TrivialProof { wdg_ :: DG F V }
  | TrivialFail
  deriving Show

instance T.Processor Trivial where
  type ProofObject Trivial = ApplicationProof TrivialProof
  type In  Trivial         = Trs
  type Out Trivial         = Trs

  execute Trivial prob =
    maybe cyclic (\s -> T.abortWith (Inapplicable s :: ApplicationProof TrivialProof)) (Prob.isDTProblem' prob)
    where
      cyclic
        | any (isCyclicNode cdg) (nodes cdg) = T.abortWith (Applicable TrivialFail)
        | otherwise                          = T.succeedWith1 (Applicable proof) T.fromId nprob
        where
          cdg = Prob.congruenceGraph prob

          nprob = prob
            { Prob.strictDPs = RS.empty
            , Prob.weakDPs   = RS.empty
            , Prob.dpGraph   = DG.empty }
          proof = TrivialProof { wdg_ = Prob.dependencyGraph prob }


--- * instances ------------------------------------------------------------------------------------------------------

trivialStrategy :: TrsStrategy
trivialStrategy = T.Apply Trivial .>>> E.empty

-- | Checks whether the DP problem is trivial, i.e., does not contain any cycles.
--
-- Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'. Also
-- not applicable when @strictTrs prob \= RS.empty@.
trivialDeclaration :: T.Declaration ('[] T.:-> TrsStrategy)
trivialDeclaration = T.declare "trivial" desc () trivialStrategy where
  desc =
    [ "Checks wether the DP problem is trivial, i.e. the dependency graph contains no loops."
    , "Only applicable if the strict component is empty."]

trivial :: TrsStrategy
trivial = T.declFun trivialDeclaration


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty TrivialProof where
  pretty TrivialFail      = PP.text "The problem is not trivial."
  pretty p@TrivialProof{} = PP.vcat
    [ PP.text "Consider the dependency graph"
    , PP.indent 2 $ PP.pretty (wdg_ p)
    , PP.text "The dependency graph contains no loops, we remove all dependency pairs." ]

instance Xml.Xml TrivialProof where
  toXml TrivialFail      = Xml.elt "trivial" []
  toXml p@TrivialProof{} = Xml.elt "trivial" [Xml.toXml $ wdg_ p]

