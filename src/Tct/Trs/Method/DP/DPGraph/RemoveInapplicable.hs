module Tct.Trs.Method.DP.DPGraph.RemoveInapplicable
  ( removeInapplicable
  , removeInapplicableDeclaration
  ) where


import qualified Data.Set as S

import qualified Data.Rewriting.Rule as R (Rule, lhs)

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Trs as Trs
import           Tct.Trs.Data.DependencyGraph
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.ProblemKind     as Prob


data RemoveInapplicableProcessor = RemoveInapplicableProc deriving Show

data RemoveInapplicableProof
  = RemoveInapplicableProof
  { wdg_         :: DG F V
  , initials_    :: [(NodeId, R.Rule F V)]
  , reachable_   :: [(NodeId, R.Rule F V)]
  , unreachable_ :: [(NodeId, R.Rule F V)] }
  | RemoveInapplicableFail
  deriving Show

instance T.Processor RemoveInapplicableProcessor where
  type ProofObject RemoveInapplicableProcessor = ApplicationProof RemoveInapplicableProof
  type Problem RemoveInapplicableProcessor     = TrsProblem

  -- ceck which lhss are startterms; wich rules can be reached
  solve p prob =  return . T.resultToTree p prob $
    maybe reminapp (T.Fail . Inapplicable) (Prob.isDTProblem' prob)
    where
      reminapp
        | null unreachable = T.Fail (Applicable RemoveInapplicableFail)
        | otherwise        = T.Success (T.toId nprob) (Applicable proof) T.fromId
        where
          wdg = Prob.dependencyGraph prob
          st  = Prob.startTerms prob

          -- MS: TODO check; for some reason the defined symbols fo BasicTerms was not integrated in tct2
          -- is this sound for path analysis; dgcompose
          linitials   = [ (n,r) | (n,cn) <- withNodeLabels' wdg (roots wdg), let r = theRule cn, Prob.isStartTerm st (R.lhs r) ]
          reachable   = reachablesDfs wdg $ fst (unzip linitials)
          unreachable = filter (`S.notMember` reachableS) (nodes wdg)
            where reachableS = S.fromList reachable

          lreachable   = withNodeLabels' wdg reachable
          lunreachable = withNodeLabels' wdg unreachable

          rs = snd $ unzip lreachable
          nprob = Prob.sanitise $ prob
            { Prob.strictDPs = Trs.fromList [ theRule r| r <- rs, isStrict r ]
            , Prob.weakTrs   = Trs.fromList [ theRule r| r <- rs, not (isStrict r) ]}

          toRS ns = [ (n, theRule cn) | (n,cn) <- ns ]
          proof = RemoveInapplicableProof
            { wdg_         = wdg
            , initials_    = linitials
            , reachable_   = toRS lreachable
            , unreachable_ = toRS lunreachable }


--- * instances ------------------------------------------------------------------------------------------------------

removeInapplicable :: T.Strategy TrsProblem
removeInapplicable = T.Proc RemoveInapplicableProc

-- | Removes inapplicable rules in DP deriviations.
--
-- We check wether nodes are reachable from starting terms.
removeInapplicableDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
removeInapplicableDeclaration = T.declare "removeInapplicable" desc () removeInapplicable
  where desc = ["Removes rules that are not applicable in DP derivations."]


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty RemoveInapplicableProof where
  pretty RemoveInapplicableFail = PP.text "No dependency pair could be removed."
  pretty p@RemoveInapplicableProof{} = PP.vcat
    [ PP.text "Only the nodes"
    , ppnodes (reachable_ p)
    , PP.text "are reachable from nodes"
    , ppnodes (initials_ p)
    , PP.text "that start derivation from marked basic terms."
    , PP.text "The nodes not reachable are removed from the problem." ]
    where ppnodes = PP.indent 2 . PP.set . map (PP.int . fst)

instance Xml.Xml RemoveInapplicableProof where
  toXml RemoveInapplicableFail = Xml.elt "removeInapplicable" []
  toXml p@RemoveInapplicableProof{} = Xml.elt "removeInapplicable"
    [ Xml.toXml (wdg_ p)
    , Xml.elt "initial"      $ map Xml.toXml (initials_ p)
    , Xml.elt "reachable"    $ map Xml.toXml (reachable_ p)
    , Xml.elt "nonreachable" $ map Xml.toXml (unreachable_ p) ]

