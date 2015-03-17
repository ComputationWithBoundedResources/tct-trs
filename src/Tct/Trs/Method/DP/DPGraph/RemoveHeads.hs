-- | This module provides the /Remove Heads/ processor.
module Tct.Trs.Method.DP.DPGraph.RemoveHeads
  ( removeHeadsDeclaration
  , removeHeads
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


{-

remove dp rules l#->com(r1#,...,rn#) where all ri# only have starting terms

-}


data RemoveHeads = RemoveHeads deriving Show

data RemoveHeadsProof
  = RemoveHeadsProof
    { wdg_     :: DG F V
    , removed_ :: [(NodeId, R.Rule F V)] }
  | RemoveHeadsFail
  deriving Show

instance T.Processor RemoveHeads where
  type ProofObject RemoveHeads = ApplicationProof RemoveHeadsProof
  type Problem RemoveHeads     = TrsProblem

  solve p prob =  return . T.resultToTree p prob $
    maybe remhead (T.Fail . Inapplicable) (Prob.isDTProblem' prob)
    where
      remhead
        | null heads = T.Fail (Applicable RemoveHeadsFail)
        | otherwise  = T.Success (T.toId nprob) (Applicable proof) T.fromId
        where
          wdg = Prob.dependencyGraph prob
          st  = Prob.startTerms prob

          heads = [ (n,r) | (n,cn) <- withNodeLabels' wdg (roots wdg), let r = theRule cn, isBasicC (R.rhs r) ]

          isBasicC (R.Var _) = True
          isBasicC (R.Fun f ts)
            | Prob.isCompoundf f = all (Prob.isStartTerm st) ts
            | otherwise          = error "Tct.Trs.Method.DP.DPGraph.RemoveHeads: not a compound symbol."

          (ns,rs) = Trs.fromList `fmap` unzip heads
          nprob = Prob.sanitiseSignature $ prob
            { Prob.strictDPs = Prob.strictDPs prob `Trs.difference` rs
            , Prob.weakDPs   = Prob.weakDPs prob `Trs.difference` rs
            , Prob.dpGraph   = let ndgraph = wdg `removeNodes` ns in DependencyGraph
              { dependencyGraph = ndgraph
              , congruenceGraph = toCongruenceGraph ndgraph }}
          proof = RemoveHeadsProof { wdg_ = wdg, removed_ = heads }


--- * instances ------------------------------------------------------------------------------------------------------

removeHeadsDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
removeHeadsDeclaration = T.declare "removeHeads" desc () (T.Proc RemoveHeads)
  where desc = ["Removes roots from the dependency graph that lead to starting terms only."]

removeHeads :: T.Strategy TrsProblem
removeHeads = T.declFun removeHeadsDeclaration


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty RemoveHeadsProof where
  pretty RemoveHeadsFail      = PP.text "No dependcy pair could be removed."
  pretty p@RemoveHeadsProof{} = PP.vcat
    [ PP.text "Consider the dependency graph"
    , PP.empty
    , PP.pretty (wdg_ p)
    , PP.empty
    , PP.text $ unwords
        [ "Following roots of the dependency graph are removed, as the considered set of starting terms is"
        , "closed under reduction with respect to these rules (modulo compound contexts)." ]
    , PP.empty
    , PP.pretty (removed_ p) ]

instance Xml.Xml RemoveHeadsProof where
  toXml RemoveHeadsFail      = Xml.elt "removeHeads" []
  toXml p@RemoveHeadsProof{} = Xml.elt "removeHeads"
    [ Xml.toXml (wdg_ p)
    , Xml.elt "removeHead" $ map Xml.toXml (removed_ p) ]

