-- InfRuleIdentity.hs ---
--
-- Filename: InfRuleIdentity.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Mon Sep 15 03:42:33 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sun Apr  9 17:30:02 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 174
-- URL:
-- Doc URL:
-- Keywords:
-- Compatibility:
--
--

-- Commentary:
--
--
--
--

-- Change Log:
--
--
--

--
--

-- Code:

{-# LANGUAGE CPP #-}

-- #define DEBUG

-- | TODO: comment this module
module Tct.Trs.Processor.ARA.ByInferenceRules.InferenceRules.InfRuleIdentity
    ( identity

    )
    where

import           Data.Rewriting.Typed.Problem
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerSignature
import           Tct.Trs.Processor.ARA.ByInferenceRules.InferenceRules.InfRuleMisc
import           Tct.Trs.Processor.ARA.ByInferenceRules.InfTreeNode
import           Tct.Trs.Processor.ARA.ByInferenceRules.Operator
import           Tct.Trs.Processor.ARA.ByInferenceRules.Prove
import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures
import           Tct.Trs.Processor.ARA.Constants

#ifdef DEBUG
import           Debug.Trace
                                                                                    (trace)
#endif

-- | The identity inference rule.
identity :: (ProblemSig, CfSigs, ASigs, Int, ACondition Int Int, InfTreeNode)
         -> [(ProblemSig, CfSigs, ASigs, Int, ACondition Int Int, [InfTreeNode])]
identity (prob, cfsigs, asigs, nr, conds, InfTreeNode [pre] cst (Just post) fn his) =

  [(prob, cfsigs, asigs, nr, nConds
   , [ InfTreeNode [] [] Nothing fn (his ++ [(fst3 (last his) + 1, "identity",
                                              InfTreeNodeLeafEmpty)])])
  | fst pre == funName ]

    where condDt :: [([ADatatype Int], Comparison, [ADatatype Int])]
          condDt = [([snd pre], Geq, [snd post])]
          condCst :: [([ACostCondition Int], Comparison, [ACostCondition Int])]
          condCst = [(cst, Geq, [ACostValue 0])]
          nConds = ACondition (costCondition conds ++ condCst) (dtConditions conds ++ condDt)
                      (shareConditions conds)
          funName = termName (fst post)
identity _ = []


--
-- InfRuleIdentity.hs ends here
