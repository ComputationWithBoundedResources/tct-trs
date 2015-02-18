module Tct.Trs.Method.DP.DPGraph.RemoveHead
  ( removeHead
  , removeHeadDeclaration
  ) where


import qualified Data.Rewriting.Rule as R (Rule, rhs)
import qualified Data.Rewriting.Term as R

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Trs as Trs
import           Tct.Trs.Data.DependencyGraph
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.ProblemKind     as Prob


data RemoveHeadProcessor = RemoveHeadProc deriving Show

data RemoveHeadProof
  = RemoveHeadProof
    { wdg_       :: DG F V
    , removable_ :: [(NodeId, R.Rule F V)] }
  | RemoveHeadFail
  deriving Show

instance T.Processor RemoveHeadProcessor where
  type ProofObject RemoveHeadProcessor = ApplicationProof RemoveHeadProof
  type Problem RemoveHeadProcessor     = TrsProblem

  -- remove dp rules, where right hand sides only have starting terms
  solve p prob =  return . T.resultToTree p prob $
    maybe remhead (T.Fail . Inapplicable) (Prob.isDTProblem' prob)
    where
      remhead
        | null heads = T.Fail (Applicable RemoveHeadFail)
        | otherwise  = T.Success (T.toId nprob) (Applicable proof) T.fromId
        where
          wdg = Prob.dependencyGraph prob
          st  = Prob.startTerms prob

          heads = [ (n,r) | (n,cn) <- withNodeLabels' wdg (roots wdg), let r = theRule cn, isBasicC (R.rhs r) ]

          isBasicC (R.Var _) = True
          isBasicC (R.Fun f ts)
            | Prob.isCompoundf f = all (Prob.isStartTerm st) ts
            | otherwise          = error "Tct.Trs.Method.DP.DPGraph.RemoveHead: not a compound symbol."

          (ns,rs) = Trs.fromList `fmap` unzip heads
          nprob = Prob.sanitiseSignature $ prob
            { Prob.strictDPs = Prob.strictDPs prob `Trs.difference` rs
            , Prob.weakDPs   = Prob.weakDPs prob `Trs.difference` rs
            , Prob.dpGraph   = let ndgraph = wdg `removeNodes` ns in DependencyGraph
              { dependencyGraph = ndgraph
              , congruenceGraph = toCongruenceGraph ndgraph }}
          proof = RemoveHeadProof { wdg_ = wdg, removable_ = heads }


--- * instances ------------------------------------------------------------------------------------------------------

removeHead :: T.Strategy TrsProblem
removeHead = T.Proc RemoveHeadProc

removeHeadDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
removeHeadDeclaration = T.declare "removeHead" desc () removeHead
  where desc = ["Removes roots from the dependency graph that lead to starting terms only."]


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty RemoveHeadProof where
  pretty RemoveHeadFail      = PP.text "No dependcy pair could be removed."
  pretty p@RemoveHeadProof{} = PP.vcat
    [ PP.text "Consider the dependency graph"
    , PP.empty
    , PP.pretty (wdg_ p)
    , PP.empty
    , PP.text $ unwords
        [ "Following roots of the dependency graph are removed, as the considered set of starting terms is"
        , "closed under reduction with respect to these rules (modulo compound contexts)." ]
    , PP.empty
    , PP.pretty (removable_ p) ]

instance Xml.Xml RemoveHeadProof where
  toXml RemoveHeadFail      = Xml.elt "removeHead" []
  toXml p@RemoveHeadProof{} = Xml.elt "removeHead"
    [ Xml.toXml (wdg_ p)
    , Xml.elt "removeHeads" $ map Xml.toXml (removable_ p) ]

