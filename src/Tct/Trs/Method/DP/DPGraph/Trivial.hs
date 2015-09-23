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
import qualified Tct.Trs.Data.Trs             as Trs (empty)
import qualified Tct.Trs.Method.Empty         as E (empty)


data Trivial = Trivial deriving Show

data TrivialProof
  = TrivialProof { wdg_ :: DG F V }
  | TrivialFail
  deriving Show

instance T.Processor Trivial where
  type ProofObject Trivial = ApplicationProof TrivialProof
  type I Trivial           = TrsProblem
  type O Trivial           = TrsProblem

  solve p prob = T.resultToTree p prob `fmap`
    maybe cyclic (return . T.Fail . Inapplicable) (Prob.isDTProblem' prob)
    where
      cyclic
        | any (isCyclicNode cdg) (nodes cdg) = return $ T.Fail (Applicable TrivialFail)
        | otherwise                          = return $ T.Success (T.toId nprob) (Applicable proof) T.fromId
        where
          cdg = Prob.congruenceGraph prob

          nprob = prob
            { Prob.strictDPs = Trs.empty
            , Prob.weakDPs   = Trs.empty
            , Prob.dpGraph   = DG.empty }
          proof = TrivialProof { wdg_ = Prob.dependencyGraph prob }


--- * instances ------------------------------------------------------------------------------------------------------

trivialStrategy :: TrsStrategy
trivialStrategy = T.toStrategy Trivial .>>> E.empty

-- | Checks whether the DP problem is trivial, i.e., does not contain any cycles.
--
-- Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'. Also
-- not applicable when @strictTrs prob \= Trs.empty@.
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

