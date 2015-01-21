{- |
 - This module provides the usable rules transformation.
-}
module Tct.Trs.Method.DP.UsableRules
  (
  usableRules
  , usableRulesDeclaration
  ) where


import           Control.Applicative               ((<$>))
import           Control.Monad.State.Strict
import           Data.List                         (partition)
import           Data.Maybe                        (isJust)
import qualified Data.Rewriting.Rule               as R
import qualified Data.Rewriting.Rules              as RS
import           Data.Rewriting.Substitution.Unify (unify)
import qualified Data.Rewriting.Term               as T


import qualified Tct.Core.Common.Pretty            as PP
import qualified Tct.Core.Common.Xml               as Xml
import qualified Tct.Core.Data                     as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data.Problem              (Problem, Trs)
import qualified Tct.Trs.Data.Problem              as Prob
import qualified Tct.Trs.Data.Trs                  as Trs
import qualified Tct.Trs.Data.Xml                  as Xml


-- MS: stolen from mzini/hoca

-- assumes that variables are disjoint
isUnifiableWith :: (Ord v1, Ord v2, Eq f) => T.Term f v1 -> T.Term f v2 -> Bool
isUnifiableWith t1 t2 = isJust (unify (T.rename Left t1) (T.rename Right t2))

-- cap f(t1,...,tn) == f(tcap(t1),...,tcap(tn))
cap :: (Show v2, Show f, Eq f, Ord v1, Ord v2) => [R.Rule f v1] -> T.Term f v2 -> T.Term f Int
cap rs t = evalState (capM t) 0
  where
    freshVar = T.Var <$> (modify succ >> get)
    lhss = RS.lhss rs

    capM (T.Var _) = freshVar
    capM (T.Fun f ts) = T.Fun f <$> mapM tcapM ts

    tcapM (T.Var _) = freshVar
    tcapM (T.Fun f ts) = do
      s <- T.Fun f <$> mapM tcapM ts
      if any (isUnifiableWith s) lhss then freshVar else return s

{-calls :: (Eq f, Ord v1, Ord v2) => T.Term f v1 -> [R.Rule f v2] -> [R.Rule f v2]-}
{-calls t rules = concatMap (\ ti -> filter (\ rl -> ti `isUnifiableWith` R.lhs rl) rules) caps-}
  {-where caps = [ cap rules ti | ti@T.Fun{} <- T.subterms t ]    -}

usableRulesOf :: (Show v, Show f, Ord v, Eq f) => [T.Term f v] -> [R.Rule f v] -> [R.Rule f v]
usableRulesOf ts rules | null ts || null rules = []
usableRulesOf ts rules = walk (caps ts) [] rules
  where
    walk []     ur _  = ur
    walk (s:ss) ur rs = walk (caps (RS.rhss ur') ++ ss) (ur' ++ ur) rs'
      where (ur',rs') = partition (\ rl -> s `isUnifiableWith` R.lhs rl) rs
    caps ss = [ cap rules s | si <- ss, s@T.Fun{} <- T.subterms si ]

usableRulesOf' :: (Show f, Show v, Ord v, Ord f) => [T.Term f v] -> Trs.Trs f v -> Trs.Trs f v
usableRulesOf' rhss trs = Trs.fromList $ usableRulesOf rhss (Trs.toList trs)


--- * processor ------------------------------------------------------------------------------------------------------

data UsableRulesProcessor = UsableRulesProc deriving Show

data UsableRulesProof = UsableRulesProof
  { strictUsables :: Trs       -- ^ Usable strict rules
  , weakUsables   :: Trs       -- ^ Usable weak rules
  , nonUsables    :: Trs       -- ^ Not usable rules
  } deriving Show

progress :: UsableRulesProof -> Bool
progress = not . Trs.null . nonUsables

instance T.Processor UsableRulesProcessor where
  type ProofObject UsableRulesProcessor = ApplicationProof UsableRulesProof
  type Problem UsableRulesProcessor     = Problem

  solve p prob                          = return . T.resultToTree p prob $
    maybe usables (T.Fail . Inapplicable) (Prob.isDPProblem' prob)
    where
      usables
        | progress proof = T.Success (T.toId nprob) (Applicable proof) T.fromId
        | otherwise      = T.Fail (Applicable proof)
      proof = UsableRulesProof
        { strictUsables = surs
        , weakUsables   = wurs
        , nonUsables    = nurs }
      rhss = [ R.rhs r | r  <- Trs.toList (Prob.dpComponents prob)]
      surs = usableRulesOf' rhss (Prob.strictTrs prob)
      wurs = usableRulesOf' rhss (Prob.weakTrs prob)
      nurs = Prob.trsComponents prob `Trs.difference` (surs `Trs.union` wurs)
      nprob = Prob.sanitise $ prob
        { Prob.strictTrs = surs
        , Prob.weakTrs   = wurs }


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty UsableRulesProof where
  pretty proof
    | prog && allUrs = PP.text "No rule is usable, rules are removed from the input problem."
    | prog = PP.vcat
        [ PP.text "We replace rewrite rules by usable rules:"
        , PP.empty
        , PP.text "Strict Usable Ruless"
        , PP.indent 2 $ PP.pretty (strictUsables proof)
        , PP.text "Weak Usable Rules"
        , PP.indent 2 $ PP.pretty (weakUsables proof) ]
    | otherwise = PP.text "All rules are usable."
    where
      allUrs = Trs.null (strictUsables proof) && Trs.null (weakUsables proof)
      prog = progress proof

instance Xml.Xml UsableRulesProof where
  toXml proof =
    Xml.elt "usablerules"
      [ Xml.elt "strict" [Xml.rules (strictUsables proof)]
      , Xml.elt "weak"   [Xml.rules (weakUsables proof)] ]
  toCeTA proof =
    Xml.elt "usableRules"
      [ Xml.elt "nonUsableRules" [Xml.rules (nonUsables proof)] ]


--- * instances ------------------------------------------------------------------------------------------------------

usableRules :: T.Strategy Problem
usableRules = T.Proc UsableRulesProc

usableRulesDeclaration :: T.Declaration ('[] T.:-> T.Strategy Problem)
usableRulesDeclaration = T.declare "usableRules" description () usableRules where
  description =
    [ "This processor restricts the strict- and weak-rules to usable rules with"                                                                                                              
    ,"respect to the dependency pairs." ]

