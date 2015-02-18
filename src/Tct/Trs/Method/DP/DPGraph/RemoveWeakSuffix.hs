module Tct.Trs.Method.DP.DPGraph.RemoveWeakSuffix
  ( removeWeakSuffix
  , removeWeakSuffixDeclaration
  ) where


import qualified Data.Set as S
import qualified Data.Graph.Inductive as Gr

import qualified Data.Rewriting.Rule as R (Rule)

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Trs as Trs
import           Tct.Trs.Data.DependencyGraph
import qualified Tct.Trs.Data.Problem         as Prob


data RemoveWeakSuffixProcessor = RemoveWeakSuffixProc deriving Show

data RemoveWeakSuffixProof
  = RemoveWeakSuffixProof
    { wdg_       :: DG F V
    , removable_ :: [(NodeId, R.Rule F V)] }
  | RemoveWeakSuffixFail
  deriving Show

instance T.Processor RemoveWeakSuffixProcessor where
  type ProofObject RemoveWeakSuffixProcessor = ApplicationProof RemoveWeakSuffixProof
  type Problem RemoveWeakSuffixProcessor     = TrsProblem

  -- strict trs rules have to be empty
  -- an scc in the congruence graph is considered weak if all rules in the scc are weak
  -- compute maximal weak suffix bottom-up
  solve p prob =  return . T.resultToTree p prob $
    maybe remtail (T.Fail . Inapplicable) (Prob.isDTProblem' prob)
    where
      remtail
        | null initials = T.Fail (Applicable RemoveWeakSuffixFail)
        | otherwise     = T.Success (T.toId nprob) (Applicable proof) T.fromId
        where
          onlyWeaks = not . any (isStrict . snd) . theSCC

          computeTails [] lfs = lfs
          computeTails (n:ns) lfs
            | n `S.member` lfs = computeTails ns lfs
            | otherwise        = computeTails (ns++preds) lfs'
              where
                (lpreds, _, cn, lsucs) = Gr.context cdg n
                sucs  = map snd lsucs
                preds = map snd lpreds
                lfs'  = if S.fromList sucs `S.isSubsetOf` lfs && onlyWeaks cn
                        then S.insert n lfs
                        else lfs

          -- congruence graph
          cdg = Prob.congruenceGraph prob
          initials = [n | (n,cn) <- withNodeLabels' cdg (leafs cdg), onlyWeaks cn]
          cdgTail  = S.toList $ computeTails initials S.empty

          -- dependency graph
          wdg = Prob.dependencyGraph prob
          wdgLabTail = fmap theRule `fmap` concatMap (theSCC . lookupNodeLabel' cdg) cdgTail

          (wdgTail, rs) = unzip wdgLabTail
          nprob = Prob.sanitiseSignature $ prob
            { Prob.weakDPs   = Prob.weakDPs prob `Trs.difference` Trs.fromList rs
            , Prob.dpGraph   = DependencyGraph
              { dependencyGraph = wdg `removeNodes` wdgTail
              , congruenceGraph = cdg `removeNodes` cdgTail }}
          proof = RemoveWeakSuffixProof { wdg_ = wdg, removable_ = wdgLabTail }


--- * instances ------------------------------------------------------------------------------------------------------

removeWeakSuffixDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
removeWeakSuffixDeclaration = T.declare "removeWeakSuffix" desc () removeWeakSuffix where
  desc =
    [ "Removes trailing paths that do not need to be oriented."
    , "Only applicable if the strict component is empty."]

-- | Removes trailing weak paths.
-- A dependency pair is on a trailing weak path if it is from the weak components and all sucessors in the dependency graph
-- are on trailing weak paths.
--
-- Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'. Also
-- not applicable when @strictTrs prob \= Trs.empty@.
removeWeakSuffix :: T.Strategy TrsProblem
removeWeakSuffix = T.Proc RemoveWeakSuffixProc


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty RemoveWeakSuffixProof where
  pretty RemoveWeakSuffixFail      = PP.text "The dependency graph contains no sub-graph of weak DPs closed under successors."
  pretty p@RemoveWeakSuffixProof{} = PP.vcat
    [ PP.text "Consider the dependency graph"
    , PP.empty
    , PP.pretty (wdg_ p)
    , PP.empty
    , PP.text $ unwords
        [ "The following weak DPs constitute a sub-graph of the DG that is closed under successors."
        , "The DPs are removed." ]
    , PP.empty
    , PP.pretty (removable_ p) ]

instance Xml.Xml RemoveWeakSuffixProof where
  toXml RemoveWeakSuffixFail      = Xml.elt "removeWeakSuffix" []
  toXml p@RemoveWeakSuffixProof{} = Xml.elt "removeWeakSuffix"
    [ Xml.toXml (wdg_ p)
    , Xml.elt "removeWeakSuffix" $ map Xml.toXml (removable_ p) ]


