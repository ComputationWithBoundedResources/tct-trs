-- | This module implements the /Innermost Rule Removal/ transformation.
-- This processor removes rules 'f(l_1,...,l_n) -> r' for which l_i (1 <= i <=n) is not a normal form.
-- The processor applies only to innermost problems.
module Tct.Trs.Method.InnermostRuleRemoval
  ( innermostRuleRemovalDeclaration
  , innermostRuleRemoval
  ) where


import           Control.Applicative          ((<$>))

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
  type Problem InnermostRuleRemoval     = TrsProblem

  solve p prob = T.resultToTree p prob <$>
    maybe irr (return . T.Fail . Inapplicable) (Prob.isInnermostProblem' prob)
    where
      irr
        | Trs.null removed = return $ T.Fail (Applicable InnermostRuleRemovalFail)
        | otherwise        = return $ T.Success (T.toId nprob) (Applicable proof) T.fromId

        where
          trsRules  = Trs.toList $ Prob.trsComponents prob
          allRules  = Trs.toList $ Prob.allComponents prob

          removable = any (not . null . fullRewrite allRules) . directSubterms . lhs
          removed   = Trs.fromList $ filter removable trsRules

          nprob = prob
            { Prob.strictTrs = Prob.strictTrs prob `Trs.difference` removed
            , Prob.weakTrs   = Prob.weakTrs prob `Trs.difference` removed }
          proof = InnermostRuleRemovalProof { removed_ = removed }


--- * instances ------------------------------------------------------------------------------------------------------

description :: [String]
description =
  [ "This processor removes rules 'f(l_1,...,l_n) -> r' for which l_i (1 <= i <=n) is not a normal form."
  , "The processor applies only to innermost problems." ]

innermostRuleRemovalDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
innermostRuleRemovalDeclaration = T.declare "InnermostRuleRemoval" description () (T.Proc InnermostRuleRemoval)

innermostRuleRemoval :: T.Strategy TrsProblem
innermostRuleRemoval = T.declFun innermostRuleRemovalDeclaration


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty InnermostRuleRemovalProof where
  pretty InnermostRuleRemovalFail      = PP.pretty "No rules can be removed."
  pretty p@InnermostRuleRemovalProof{} = PP.vcat
    [ PP.text "Arguments of following rules are not not normal-forms."
    , PP.indent 2 . PP.pretty $ removed_ p
    , PP.text "All above mentioned rules can be savely removed." ]

instance Xml.Xml InnermostRuleRemovalProof where
  toXml InnermostRuleRemovalFail      = Xml.elt "innermostRuleRemoval" []
  toXml p@InnermostRuleRemovalProof{} = Xml.elt "innermostRuleRemoval" [ Xml.toXml (removed_ p) ]
  toCeTA InnermostRuleRemovalFail      = Xml.unsupported
  toCeTA p@InnermostRuleRemovalProof{} = Xml.elt "removeNonApplicableRules" [ Xml.elt "trs" [Xml.toCeTA (removed_ p)] ]

