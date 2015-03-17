-- | This module provides the /Simplify RHS/ processor.
module Tct.Trs.Method.DP.DPGraph.SimplifyRHS 
  ( simplifyRHSDeclaration
  , simplifyRHS 
  ) where


import qualified Data.List                    as L (partition)
import           Data.Maybe                   (fromMaybe)

import qualified Data.Rewriting.Rule          as R (Rule (..))
import qualified Data.Rewriting.Term          as R

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import           Tct.Trs.Data.DependencyGraph
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.Signature       as Sig
import qualified Tct.Trs.Data.Trs             as Trs


{-
Simplify RHS;

let l#->com(r1#, ..., rn#) in S# U W#, ri# is removable if there exists no outgoing edge from l#->com(r1#, ..., rn#) labeled with i

<simp(S#)/simp(W#) U W, Q, T@> : f
<S#/W# U W, Q, T@> : f

-}

data SimplifyRHS = SimplifyRHS deriving Show

data SimplifyRHSProof
  = SimplifyRHSProof
    { wdg_        :: DG F V
    , simplified_ :: [R.Rule F V] }
  | SimplifyRHSFail
  deriving Show

instance T.Processor SimplifyRHS where
  type ProofObject SimplifyRHS = ApplicationProof SimplifyRHSProof
  type Problem SimplifyRHS     = TrsProblem

  solve p prob =  return . T.resultToTree p prob $
    maybe simpRHS (T.Fail . Inapplicable) (Prob.isDTProblem' prob)
    where
      simpRHS
        | null simplified = T.Fail (Applicable SimplifyRHSFail)
        | otherwise       = T.Success (T.toId nprob) (Applicable proof) T.fromId
        where
          wdg = Prob.dependencyGraph prob

          elims = [ (isStrict cn, (r, elimRule n r)) | (n,cn) <- lnodes wdg, let r = theRule cn ]
          elimRule n (R.Rule l (R.Fun f rs))
            | not (Prob.isCompoundf f) = error "SimplifyRHS.elim: not a compound symbol."
            | otherwise                = if length rs' == length rs then Nothing else Just $ R.Rule l (R.Fun f rs')
            where
              rs'   = [ ri | (i,ri) <- zip [1..] rs, i `elem` succs]
              succs = [ j | (_,_,j) <- lsuccessors wdg n]
          elimRule _ _ = Nothing


          (stricts,weaks) = L.partition fst elims
          toTrs rs        = Trs.fromList [ r | (_,(r1, mr2)) <- rs, let r = r1 `fromMaybe` mr2]
          simplified      = [ r | (_,(_, Just r)) <- elims ]
          nprob = Prob.sanitiseSignature $ prob
            { Prob.strictDPs = toTrs stricts
            , Prob.weakDPs   = toTrs weaks
            , Prob.signature = foldr updateCompound (Prob.signature prob) simplified }
            where
              updateCompound (R.Rule _ (R.Fun f rs)) acc = Sig.alter (const . Just $ length rs) f acc
              updateCompound _ acc                       = acc

          proof = SimplifyRHSProof
            { wdg_        = wdg
            , simplified_ = simplified }


--- * instances ------------------------------------------------------------------------------------------------------

simplifyRHSDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
simplifyRHSDeclaration = T.declare "simplifyRHS" desc () (T.Proc SimplifyRHS) where
  desc =
    [ "Simplify right hand sides of dependency pairs by removing marked subterms "
    , "whose root symbols are undefined."
    , "Only applicable if the strict component is empty." ]

-- | Simplifies right-hand sides of dependency pairs.
-- Removes r_i from right-hand side @c_n(r_1,...,r_n)@ if no instance of
-- r_i can be rewritten.
--
-- Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'. Also
-- not applicable when @strictTrs prob \= Trs.empty@.
simplifyRHS :: T.Strategy TrsProblem
simplifyRHS = T.declFun simplifyRHSDeclaration


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty SimplifyRHSProof where
  pretty SimplifyRHSFail      = PP.text "No rule was simplified."
  pretty p@SimplifyRHSProof{} = PP.vcat
    [ PP.text "Consider the dependency graph"
    , PP.empty
    , PP.pretty (wdg_ p)
    , PP.empty
    , PP.text "Due to missing edges in the depndency graph, the right-hand sides of following rules could be simplified:"
    , PP.empty
    , PP.pretty (Trs.fromList $ simplified_ p) ]

instance Xml.Xml SimplifyRHSProof where
  toXml SimplifyRHSFail      = Xml.elt "simpRHS" []
  toXml p@SimplifyRHSProof{} = Xml.elt "simpRHS"
    [ Xml.toXml (wdg_ p)
    , Xml.elt "simplified" $ map Xml.toXml (simplified_ p) ]

