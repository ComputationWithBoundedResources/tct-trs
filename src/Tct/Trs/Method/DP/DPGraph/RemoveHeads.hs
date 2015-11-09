{- | This module provides the /Remove Heads/ processor.

@
    |- <rem(S#) +/ rem(W#) + W, Q, T#> :f
  ------------------------------------------
          |- <S# / W# + W, Q, T#> :f
@
, where @rem(R#)@ removes DP rules @l#->com(r1#,...,rn#)@ that occur at root positions of the DP graph and all @ri#@ are starting terms.
-}
module Tct.Trs.Method.DP.DPGraph.RemoveHeads
  ( removeHeadsDeclaration
  , removeHeads
  ) where


import qualified Data.Rewriting.Rule          as R (Rule, rhs)
import qualified Data.Rewriting.Term          as R

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import           Tct.Trs.Data.DependencyGraph
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.ProblemKind     as Prob
import qualified Tct.Trs.Data.Signature       as Sig (isDefined)
import qualified Tct.Trs.Data.Symbol          as Symb
import qualified Tct.Trs.Data.Rules           as RS


data RemoveHeads = RemoveHeads deriving Show

data RemoveHeadsProof
  = RemoveHeadsProof
    { wdg_     :: DG F V
    , removed_ :: [(NodeId, R.Rule F V)] }
  | RemoveHeadsFail
  deriving Show

instance T.Processor RemoveHeads where
  type ProofObject RemoveHeads = ApplicationProof RemoveHeadsProof
  type In RemoveHeads          = Trs
  type Out RemoveHeads         = Trs

  execute RemoveHeads prob =
    maybe remhead (\s -> T.abortWith (Inapplicable s :: ApplicationProof RemoveHeadsProof)) (Prob.isDTProblem' prob)
    where
      remhead
        | null heads = T.abortWith (Applicable RemoveHeadsFail)
        | otherwise  = T.succeedWith (Applicable proof) T.fromId (T.toId nprob) 
        where
          wdg = Prob.dependencyGraph prob

          heads = [ (n,r) | (n,cn) <- withNodeLabels' wdg (roots wdg), let r = theRule cn, isBasicC (R.rhs r) ]

          isBasicC (R.Var _)     = True
          isBasicC t@(R.Fun f ts)
            | Symb.isCompoundFun f = all isBasicC ts
            | isDefined f          = isStartTerm t
            | otherwise            = error "Tct.RS.Method.DP.DPGraph.RemoveHeads.solve.isBasicC: invalid rhs"
            where
              isStartTerm = Prob.isStartTerm (Prob.startTerms prob)
              isDefined   = flip Sig.isDefined (Prob.signature prob)

          (ns,rs) = RS.fromList `fmap` unzip heads
          nprob = prob
            { Prob.strictDPs = Prob.strictDPs prob `RS.difference` rs
            , Prob.weakDPs   = Prob.weakDPs prob `RS.difference` rs
            , Prob.dpGraph   = let ndgraph = wdg `removeNodes` ns in DependencyGraph
              { dependencyGraph = ndgraph
              , congruenceGraph = toCongruenceGraph ndgraph }}
          proof = RemoveHeadsProof { wdg_ = wdg, removed_ = heads }


--- * instances ------------------------------------------------------------------------------------------------------

removeHeadsDeclaration :: T.Declaration ('[] T.:-> TrsStrategy)
removeHeadsDeclaration = T.declare "removeHeads" desc () (T.Apply RemoveHeads)
  where desc = ["Removes roots from the dependency graph that lead to starting terms only."]

removeHeads :: TrsStrategy
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

