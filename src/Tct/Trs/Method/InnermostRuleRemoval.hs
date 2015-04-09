-- | This module implements the /Innermost Rule Removal/ transformation.
-- This processor removes rules 'f(l_1,...,l_n) -> r' for which l_i (1 <= i <=n) is not a normal form.
-- The processor applies only to innermost problems.
module Tct.Trs.Method.InnermostRuleRemoval
  ( innermostRuleRemovalDeclaration
  , innermostRuleRemoval
  ) where


import           Control.Applicative          ((<$>))
import           Data.Maybe                   (catMaybes)

import qualified Data.Rewriting.Rule          as R

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.Rewriting       as R
import qualified Tct.Trs.Data.Trs             as Trs


data InnermostRuleRemoval = InnermostRuleRemoval
  deriving Show

data RuleRemoval f v = RuleRemoval
  { removed_ :: [R.Rule f v]
  , reason_  :: R.Rule f v }
  deriving Show

data InnermostRuleRemovalProof
  = InnermostRuleRemovalProof { removals_ :: [RuleRemoval F V] }
  | InnermostRuleRemovalFail
  deriving Show


instance T.Processor InnermostRuleRemoval where
  type ProofObject InnermostRuleRemoval = ApplicationProof InnermostRuleRemovalProof
  type Problem InnermostRuleRemoval     = TrsProblem

  solve p prob = T.resultToTree p prob <$>
    maybe irr (return . T.Fail . Inapplicable) (Prob.isInnermostProblem' prob)
    where
      irr
        | null removals = return $ T.Fail (Applicable InnermostRuleRemovalFail)
        | otherwise     = return $ T.Success (T.toId nprob) (Applicable proof) T.fromId

        where
          trsRules  = Trs.toList $ Prob.trsComponents prob
          allRules  = Trs.toList $ Prob.allComponents prob

          removable cause = any (not . null . R.rewrite [cause]) . R.directSubterms . R.lhs
          removals = catMaybes $ k `fmap` trsRules where
            k cause = case filter (removable cause) allRules of
              []   -> Nothing
              rems -> Just $ RuleRemoval rems cause

          removedRules = Trs.fromList $ concatMap removed_ removals
          nprob = prob
            { Prob.strictTrs = Prob.strictTrs prob `Trs.difference` removedRules
            , Prob.weakTrs   = Prob.weakTrs prob `Trs.difference` removedRules }
          proof = InnermostRuleRemovalProof { removals_ = removals }


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
    , PP.indent 2 . PP.pretty . Trs.fromList $ concatMap removed_ (removals_ p)
    , PP.text "All above mentioned rules can be savely removed." ]

instance Xml.Xml InnermostRuleRemovalProof where
  toXml InnermostRuleRemovalFail      = Xml.elt "innermostRuleRemoval" []
  toXml p@InnermostRuleRemovalProof{} = Xml.elt "innermostRuleRemoval" (xmlremoval `fmap` removals_ p)
    where
      xmlremoval r  = Xml.elt "removal" [xmlreason (reason_ r), xmlremoved (removed_ r)]
      xmlreason r   = Xml.elt "reason" [Xml.toXml r]
      xmlremoved rs = Xml.elt "removed" (Xml.toXml `fmap` rs)

