{- | This module provides the /Simplify RHS/ processor.

@
    |- <simp(S#) / simp(W#) + W, Q, T#> :f
  ------------------------------------------
          |- <S# / W# + W, Q, T#> :f
@
, where @simp(R#)@ removes @ri@ from right-hand sides @c_n(r_1,...,r_n)@ if no instance of @ri@ can be rewritten, ie. if
there is no outgoing edge @i@.
-}
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
import qualified Tct.Trs.Data.Symbol          as Symb
import qualified Tct.Trs.Data.Rules as RS


data SimplifyRHS = SimplifyRHS deriving Show

data SimplifyRHSProof
  = SimplifyRHSProof
    { wdg_        :: DG F V
    , simplified_ :: [R.Rule F V] }
  | SimplifyRHSFail
  deriving Show

instance T.Processor SimplifyRHS where
  type ProofObject SimplifyRHS = ApplicationProof SimplifyRHSProof
  type In  SimplifyRHS         = Trs
  type Out SimplifyRHS         = Trs

  execute SimplifyRHS prob =
    maybe simpRHS (\s -> T.abortWith (Inapplicable s :: ApplicationProof SimplifyRHSProof)) (Prob.isDTProblem' prob)
    where
      simpRHS
        | null simplified = T.abortWith (Applicable SimplifyRHSFail)
        | otherwise       = T.succeedWith1 (Applicable proof) T.fromId nprob
        where
          wdg = Prob.dependencyGraph prob

          -- TODO: MS: this is not optimal;
          -- I assumed that all my rhs have compound symbols after the DP transformation; this is not true after the
          -- decomposeDG transformation. We can now have rhs of length one which are removed (in practice they are
          -- probably already removed before); ie which should be replaced with fresh compound symbols. Either make
          -- sure that we have the appropriate format or introduce fresh compound symbols here
          elims = [ (isStrict cn, (r, elimRule n r)) | (n,cn) <- lnodes wdg, let r = theRule cn ]
          elimRule n (R.Rule l (R.Fun f rs))
            | not (Symb.isCompoundFun f) = Nothing
            -- | not (Prob.isCompoundf f) = error $ "SimplifyRHS.elim: not a compound symbol: " ++ show f
            | otherwise                = if length rs' == length rs then Nothing else Just $ R.Rule l (R.Fun f rs')
            where
              rs'   = [ ri | (i,ri) <- zip [1..] rs, i `elem` succs]
              succs = [ j | (_,_,j) <- lsuccessors wdg n]
          elimRule _ _ = Nothing


          (stricts,weaks) = L.partition fst elims
          toTrs rs        = RS.fromList [ r | (_,(r1, mr2)) <- rs, let r = r1 `fromMaybe` mr2]
          simplified      = [ r | (_,(_, Just r)) <- elims ]
          nprob = Prob.sanitiseDPGraph $ prob
            { Prob.strictDPs = toTrs stricts
            , Prob.weakDPs   = toTrs weaks
            , Prob.signature = foldr updateCompound (Prob.signature prob) simplified }
            where
              updateCompound (R.Rule _ (R.Fun f rs)) acc = Sig.setArity (length rs) f acc
              updateCompound _ acc                       = acc

          proof = SimplifyRHSProof
            { wdg_        = wdg
            , simplified_ = simplified }


--- * instances ------------------------------------------------------------------------------------------------------

simplifyRHSDeclaration :: T.Declaration ('[] T.:-> TrsStrategy)
simplifyRHSDeclaration = T.declare "simplifyRHS" desc () (T.Apply SimplifyRHS) where
  desc =
    [ "Simplify right hand sides of dependency pairs by removing marked subterms "
    , "whose root symbols are undefined."
    , "Only applicable if the strict component is empty." ]

-- | Simplifies right-hand sides of dependency pairs.
-- Removes r_i from right-hand side @c_n(r_1,...,r_n)@ if no instance of
-- r_i can be rewritten.
--
-- Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'. Also
-- not applicable when @strictTrs prob \= RS.empty@.
simplifyRHS :: TrsStrategy
simplifyRHS = T.declFun simplifyRHSDeclaration


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty SimplifyRHSProof where
  pretty SimplifyRHSFail      = PP.text "No rule was simplified."
  pretty p@SimplifyRHSProof{} = PP.vcat
    [ PP.text "Consider the dependency graph"
    , PP.indent 2 $ PP.pretty (wdg_ p)
    , PP.text "Due to missing edges in the depndency graph, the right-hand sides of following rules could be simplified:"
    , PP.indent 2 $ PP.pretty (RS.fromList $ simplified_ p) ]

instance Xml.Xml SimplifyRHSProof where
  toXml SimplifyRHSFail      = Xml.elt "simpRHS" []
  toXml p@SimplifyRHSProof{} = Xml.elt "simpRHS"
    [ Xml.toXml (wdg_ p)
    , Xml.elt "simplified" $ map Xml.toXml (simplified_ p) ]

