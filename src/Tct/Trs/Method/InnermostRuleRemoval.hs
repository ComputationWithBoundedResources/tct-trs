{- | This module implements the /Innermost Rule Removal/ transformation.

@
    |- < S# + irr(S) / W# + irr(W) , Q, T> :f
  ----------------------------------------------
        |- <S# + S / W# + W , Q, T> :f
@
, where @irr(R)@ removes rules @f(l_1,...,l_n) -> r@ for wich @l_i (1 <= i <= n)@ is not in normal form.
The processor applies only to innermost problems.
-}
module Tct.Trs.Method.InnermostRuleRemoval
  ( innermostRuleRemovalDeclaration
  , innermostRuleRemoval
  ) where


import           Data.Rewriting.Rule          (lhs)
import           Data.Rewriting.Rules.Rewrite (fullRewrite)

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem         as Prob
import           Tct.Trs.Data.Rewriting       (directSubterms)
import qualified Tct.Trs.Data.Trs             as Trs


data InnermostRuleRemoval = InnermostRuleRemoval
  deriving Show

data InnermostRuleRemovalProof
  = InnermostRuleRemovalProof { removed_ :: Trs F V }
  | InnermostRuleRemovalFail
  deriving Show


instance T.Processor InnermostRuleRemoval where
  type ProofObject InnermostRuleRemoval = ApplicationProof InnermostRuleRemovalProof
  type In InnermostRuleRemoval          = TrsProblem
  type Out InnermostRuleRemoval         = TrsProblem

  execute InnermostRuleRemoval prob =
    maybe irr (\s -> T.abortWith (Inapplicable s :: ApplicationProof InnermostRuleRemovalProof)) (Prob.isInnermostProblem' prob)
    where
      irr
        | Trs.null removed = T.abortWith (Applicable InnermostRuleRemovalFail)
        | otherwise        = T.succeedWith1 (Applicable proof) T.fromId nprob

        where
          trsRules  = Trs.toList $ Prob.trsComponents prob
          allRules  = Trs.toList $ Prob.allComponents prob

          removable = any (not . null . fullRewrite allRules) . directSubterms . lhs
          removed   = Trs.fromList $ filter removable trsRules

          nprob = Prob.sanitiseDPGraph $ prob
            { Prob.strictTrs = Prob.strictTrs prob `Trs.difference` removed
            , Prob.weakTrs   = Prob.weakTrs prob `Trs.difference` removed }
          proof = InnermostRuleRemovalProof { removed_ = removed }


--- * instances ------------------------------------------------------------------------------------------------------

description :: [String]
description =
  [ "This processor removes rules 'f(l_1,...,l_n) -> r' for which l_i (1 <= i <=n) is not a normal form."
  , "The processor applies only to innermost problems." ]

innermostRuleRemovalDeclaration :: T.Declaration ('[] T.:-> TrsStrategy)
innermostRuleRemovalDeclaration = T.declare "innermostRuleRemoval" description () (T.Apply InnermostRuleRemoval)

innermostRuleRemoval :: TrsStrategy
innermostRuleRemoval = T.declFun innermostRuleRemovalDeclaration


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty InnermostRuleRemovalProof where
  pretty InnermostRuleRemovalFail      = PP.pretty "No rules can be removed."
  pretty p@InnermostRuleRemovalProof{} = PP.vcat
    [ PP.text "Arguments of following rules are not normal-forms."
    , PP.indent 2 . PP.pretty $ removed_ p
    , PP.text "All above mentioned rules can be savely removed." ]

instance Xml.Xml InnermostRuleRemovalProof where
  toXml InnermostRuleRemovalFail      = Xml.elt "innermostRuleRemoval" []
  toXml p@InnermostRuleRemovalProof{} = Xml.elt "innermostRuleRemoval" [ Xml.toXml (removed_ p) ]
  toCeTA InnermostRuleRemovalFail      = Xml.unsupported
  toCeTA p@InnermostRuleRemovalProof{} = Xml.elt "removeNonApplicableRules" [ Xml.elt "trs" [Xml.toCeTA (removed_ p)] ]

