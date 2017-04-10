-- InfRuleWeak.hs ---
--
-- Filename: InfRuleWeak.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Mon Sep 15 11:39:45 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sun Apr  9 17:29:58 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 108
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
module Tct.Trs.Processor.ARA.ByInferenceRules.InferenceRules.InfRuleWeak
    ( weak

    )
    where


import           Data.Rewriting.Typed.Term                                             hiding
                                                                                        (map)
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerSignature
import           Tct.Trs.Processor.ARA.ByInferenceRules.InferenceRules.InfRuleFunction
import           Tct.Trs.Processor.ARA.ByInferenceRules.InferenceRules.InfRuleMisc
import           Tct.Trs.Processor.ARA.ByInferenceRules.Prove
import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Type
import           Tct.Trs.Processor.ARA.Constants


import           Control.Arrow

#ifdef DEBUG
import           Debug.Trace
                                                                                        (trace)
#endif

weak :: (ProblemSig, CfSigs, ASigs, Int, ACondition Int Int, InfTreeNode)
         -> [(ProblemSig, CfSigs, ASigs, Int, ACondition Int Int, [InfTreeNode])]
weak (prob, cfsigs, asigs, nr, conds, InfTreeNode pre cst (Just (term, dt)) fn his) =
  -- trace ("weak")

  [(prob, cfsigs, asigs, nr, conds, [InfTreeNode pre' cst (Just (term, dt)) fn his'])
  | length pre > length varsTerm -- only if more variables left than right
  ]

  where pre' = filter (\x -> fst x `elem` varsTerm) pre
        varsTerm = vars term
        his' = his ++ [(fst3 (last his) + 1, "weak",
                        InfTreeNodeView (map (second toADatatypeVector) pre')
                        (map toACostConditionVector cst) (term, toADatatypeVector dt))]

weak _ = []

--
-- InfRuleWeak.hs ends here
