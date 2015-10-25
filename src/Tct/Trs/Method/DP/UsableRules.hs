{- | this module provides the /Usable Rules/ processor.
@
    |- <U(S# + S) / U(W# + W), Q, T#> :f
  ----------------------------------------
      |- <S# + S / W# + W, Q, T#> :f
@
, where @U(R)@ denotes an approximation of the usable rules wrt. to the starting terms.
-}
module Tct.Trs.Method.DP.UsableRules
  ( usableRulesDeclaration
  , usableRules
  ) where


import           Control.Monad.State.Strict
import           Data.List                   (partition)
import qualified Data.Rewriting.Rule         as R
import qualified Data.Rewriting.Rules        as RS
import qualified Data.Rewriting.Term         as T

import qualified Tct.Core.Common.Pretty      as PP
import qualified Tct.Core.Common.Xml         as Xml
import qualified Tct.Core.Data               as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem        as Prob
import qualified Tct.Trs.Data.Rewriting      as R
import qualified Tct.Trs.Data.Trs            as Trs


-- MS: stolen from mzini/hoca
-- following 'Certifiable Subterms and Certifiable Usable Rules. C. Sternagel, and R. Thiemann' (Definition 4.5)
-- but additionally incorporates starting rules

-- cap f(t1,...,tn) == f(tcap(t1),...,tcap(tn))
cap :: (Show v2, Show f, Eq f, Ord v1, Ord v2) => [R.Rule f v1] -> T.Term f v2 -> T.Term f (R.Fresh v2)
cap rs t = evalState (capM t) 0
  where
    capM (T.Var _)    = R.freshVar
    capM (T.Fun f ts) = T.Fun f <$> mapM (R.tcapM (RS.lhss rs) . T.rename R.Old) ts

usableRulesOf :: (Show v, Show f, Ord v, Eq f) => [T.Term f v] -> [R.Rule f v] -> [R.Rule f v]
usableRulesOf rhss rules | null rhss || null rules = []
usableRulesOf rhss rules = walk (caps rhss) [] rules
  where
    walk []     ur _  = ur
    walk (s:ss) ur rs = walk (caps (RS.rhss ur') ++ ss) (ur ++ ur') rs'
      where (ur',rs') = partition (\ rl -> s `R.isUnifiable` R.lhs rl) rs
    caps ss = [ cap rules s | si <- ss, s@T.Fun{} <- T.subterms si ]

usableRulesOf' :: (Show f, Show v, Ord v, Ord f) => Trs.Trs f v -> Trs.Trs f v -> Trs.Trs f v
usableRulesOf' start trs = start `Trs.union` steps
  where steps = Trs.fromList $ usableRulesOf (RS.rhss $ Trs.toList start) (Trs.toList trs)


--- * processor ------------------------------------------------------------------------------------------------------

data UsableRules = UsableRules deriving Show

data UsableRulesProof
  = UsableRulesProof
  { usable_    :: Trs F V
  , notUsable_ :: Trs F V }
  | UsableRulesFail
  deriving Show


instance T.Processor UsableRules where
  type ProofObject UsableRules = ApplicationProof UsableRulesProof
  type In  UsableRules         = TrsProblem
  type Out UsableRules         = TrsProblem

  execute UsableRules prob =
    maybe usables (\s -> T.abortWith (Inapplicable s :: ApplicationProof UsableRulesProof)) (Prob.isDPProblem' prob)
    where
      usables
        | progress  = T.succeedWith1 (Applicable proof) T.fromId nprob
        | otherwise = T.abortWith (Applicable UsableRulesFail)

      rules    = Prob.allComponents prob
      usable   = usableRulesOf' (Prob.startComponents prob) rules
      progress = Trs.size usable < Trs.size rules

      proof = UsableRulesProof
        { usable_    = usable
        , notUsable_ = rules `Trs.difference` usable }

      nprob = Prob.sanitiseDPGraph $ prob
        { Prob.strictDPs = Prob.strictDPs prob `Trs.intersect` usable
        , Prob.weakDPs   = Prob.weakDPs   prob `Trs.intersect` usable
        , Prob.strictTrs = Prob.strictTrs prob `Trs.intersect` usable
        , Prob.weakTrs   = Prob.weakTrs   prob `Trs.intersect` usable }


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty UsableRulesProof where
  pretty p@UsableRulesProof{}
    | Trs.null (usable_ p) = PP.text "No rule is usable, rules are removed from the input problem."
    | otherwise = PP.vcat
      [ PP.text "We replace rewrite rules by usable rules:"
      , PP.indent 2 $ PP.pretty (usable_ p) ]
  pretty UsableRulesFail = PP.text "All rules are usable."

instance Xml.Xml UsableRulesProof where
  toXml p@UsableRulesProof{} = Xml.elt "usablerules" [Xml.toXml (usable_ p)]
  toXml UsableRulesFail      = Xml.elt "usablerules" []
  toCeTA p@UsableRulesProof{} =
    Xml.elt "usableRules"
      [ Xml.elt "nonUsableRules" [Xml.toXml (notUsable_ p)]]
  toCeTA UsableRulesFail = Xml.elt "usableRules" []


--- * instances ------------------------------------------------------------------------------------------------------

usableRulesDeclaration :: T.Declaration ('[] T.:-> TrsStrategy)
usableRulesDeclaration = T.declare "usableRules" description () (T.Apply UsableRules) where
  description =
    [ "This processor restricts the strict- and weak-rules to usable rules with"
    ,"respect to the dependency pairs." ]

usableRules :: TrsStrategy
usableRules = T.declFun usableRulesDeclaration

