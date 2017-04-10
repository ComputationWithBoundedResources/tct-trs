{-# LANGUAGE CPP #-}
-- Pretty.hs ---
--
-- Filename: Pretty.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Tue Sep  9 15:15:02 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sun Apr  9 17:30:02 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 371
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

-- | TODO: comment this module
module Tct.Trs.Processor.ARA.ByInferenceRules.Prove.Pretty
    ( prettyProve
    )
    where

import           Data.Rewriting.Typed.Problem
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition.Pretty
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype
import           Tct.Trs.Processor.ARA.ByInferenceRules.InfTreeNode.Pretty
import           Tct.Trs.Processor.ARA.ByInferenceRules.Prove.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Pretty
import           Tct.Trs.Processor.ARA.Pretty


import           Data.List                                                       (intersperse)
import           Data.Maybe                                                      (fromMaybe)
import           Prelude                                                         hiding
                                                                                  ((<$>))
import           Text.PrettyPrint

#define DEBUG


line = text "" $+$ empty

prettyProve :: Prove -> Doc
prettyProve prove =
  hang empty 2 $
  text "InfTreeNodes To Prove:" $+$ line $+$
  vcat (intersperse line (map prettyInfTreeNode (infTreeNodesToProve prove))) $+$ line $+$
  text "Proven InfTreeNodes: " $+$line $+$
  vcat (intersperse line (map prettyInfTreeNode (provenInfTreeNodes prove))) $+$ line $+$
  text "Signature Map: " $+$line $+$
  vcat (zipWith (\nr (y, n, z) -> int nr <> text ": "<>
                               prettyAraSignature text pCst pDt y
#ifdef DEBUG
                               <+> text "\tFromRule: " <> int n
                               <+> text "\t" <> text z
#endif
                ) ([0..] :: [Int])
        (signatureMap prove)) $+$ line $+$
  text "Cost Free Signature Map: " $+$line $+$
  vcat (zipWith (\nr (y,n,z) -> int nr <> text ": "<>
                        prettyAraSignature text pCst pDt y
#ifdef DEBUG
                        <+> text "\tGroup: " <> int n
                        <+> text "\tFrom: " <> text z
#endif
                ) ([0..] :: [Int])
        (costFreeSigs prove)) $+$ line $+$
  text "Constraints:" $+$ line $+$
  prettyCond (conditions prove) $+$ line $+$
  text "Problem:" $+$ line $+$
  prettyAraProblem (problem prove) $+$
  text "Next Variable Number: " <+> int (varNr prove) $+$ line
  where pCst = prettyACost prettyVector
        pDt  = prettyADatatype pCst

prettyCond = prettyACondition (prettyACostCondition int) (prettyADatatype (prettyACost int))

--
-- Pretty.hs ends here
