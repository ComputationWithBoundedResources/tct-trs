{-| This module provides the /Remove Inapplicable/ processor.

@
    |- <rem(S#) / rem(W#) + W, Q, T#> :f
  ------------------------------------------
          |- <S# / W# + W, Q, T#> :f
@
, where @rem(R#)@ removes DPs that can not occur in any derivation wrt to the starting terms.
-}
module Tct.Trs.Method.DP.DPGraph.RemoveInapplicable
  ( removeInapplicableDeclaration
  , removeInapplicable
  ) where


import qualified Data.Set                     as S

import qualified Data.Rewriting.Rule          as R (Rule, lhs)

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import           Tct.Trs.Data.DependencyGraph
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.ProblemKind     as Prob
import qualified Tct.Trs.Data.Trs             as Trs


data RemoveInapplicable = RemoveInapplicable deriving Show

data RemoveInapplicableProof
  = RemoveInapplicableProof
    { wdg_         :: DG F V
    , initials_    :: [(NodeId, R.Rule F V)]
    , reachable_   :: [(NodeId, R.Rule F V)]
    , unreachable_ :: [(NodeId, R.Rule F V)] }
  | RemoveInapplicableFail
  deriving Show

instance T.Processor RemoveInapplicable where
  type ProofObject RemoveInapplicable = ApplicationProof RemoveInapplicableProof
  type I RemoveInapplicable     = TrsProblem
  type O RemoveInapplicable     = TrsProblem

  solve p prob =  T.resultToTree p prob `fmap`
    maybe reminapp (return . T.Fail . Inapplicable) (Prob.isDTProblem' prob)
    where
      reminapp
        | null unreachable = return $ T.Fail (Applicable RemoveInapplicableFail)
        | otherwise        = return $ T.Success (T.toId nprob) (Applicable proof) T.fromId
        where
          wdg = Prob.dependencyGraph prob
          st  = Prob.startTerms prob

          -- compute rules whose lhs is a possible start term;
          -- compute reachable rules
          linitials   = [ (n,r) | (n,cn) <- lnodes wdg, let r = theRule cn, Prob.isStartTerm st (R.lhs r) ]
          reachable   = reachablesDfs wdg $ fst (unzip linitials)
          unreachable = filter (`S.notMember` reachableS) (nodes wdg)
            where reachableS = S.fromList reachable

          lreachable   = withNodeLabels' wdg reachable
          lunreachable = withNodeLabels' wdg unreachable

          rs = snd $ unzip lreachable
          nprob = Prob.sanitiseDPGraph $ prob
            { Prob.strictDPs = Trs.fromList [ theRule r| r <- rs, isStrict r ]
            , Prob.weakDPs   = Trs.fromList [ theRule r| r <- rs, not (isStrict r) ] }

          toRS ns = [ (n, theRule cn) | (n,cn) <- ns ]
          proof = RemoveInapplicableProof
            { wdg_         = wdg
            , initials_    = linitials
            , reachable_   = toRS lreachable
            , unreachable_ = toRS lunreachable }


--- * instances ------------------------------------------------------------------------------------------------------

removeInapplicable :: TrsStrategy
removeInapplicable = T.declFun removeInapplicableDeclaration

-- | Removes inapplicable rules in DP deriviations.
--
-- We check wether nodes are reachable from starting terms.
removeInapplicableDeclaration :: T.Declaration ('[] T.:-> TrsStrategy)
removeInapplicableDeclaration = T.declare "removeInapplicable" desc () (T.Proc RemoveInapplicable)
  where desc = ["Removes rules that are not applicable in DP derivations."]


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty RemoveInapplicableProof where
  pretty RemoveInapplicableFail      = PP.text "No dependency pair could be removed."
  pretty p@RemoveInapplicableProof{} = PP.vcat
    [ PP.text "Only the nodes"
    , ppnodes (reachable_ p)
    , PP.text "are reachable from nodes"
    , ppnodes (initials_ p)
    , PP.text "that start derivation from marked basic terms."
    , PP.text "The nodes not reachable are removed from the problem." ]
    where ppnodes = PP.indent 2 . PP.set . map (PP.int . fst)

instance Xml.Xml RemoveInapplicableProof where
  toXml RemoveInapplicableFail      = Xml.elt "removeInapplicable" []
  toXml p@RemoveInapplicableProof{} = Xml.elt "removeInapplicable"
    [ Xml.toXml (wdg_ p)
    , Xml.elt "initial"      $ map Xml.toXml (initials_ p)
    , Xml.elt "reachable"    $ map Xml.toXml (reachable_ p)
    , Xml.elt "nonreachable" $ map Xml.toXml (unreachable_ p) ]

