-- Pretty.hs ---
--
-- Filename: Pretty.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Mon Oct  6 13:22:09 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sat Apr  8 15:22:41 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 147
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
--
--

-- Code:

-- | TODO: comment this module
module Tct.Trs.Processor.ARA.ByInferenceRules.InfTreeNode.Pretty
    ( prettyInfTreeNode
    , prettyInfTreeNodeView
    )
    where

import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition.Pretty
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost.Pretty
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype
import           Tct.Trs.Processor.ARA.ByInferenceRules.InfTreeNode.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Pretty
-- import           Prelude                                                      hiding
--                                                                                ((<$>))


import           Control.Arrow                                                   ((***))
import           Data.List                                                       (intersperse)
import           Data.Maybe
import           Text.PrettyPrint
import qualified Text.PrettyPrint.ANSI.Leijen                                    as L
line = text "" $+$ empty

prettyInfTreeNode :: InfTreeNode -> Doc
prettyInfTreeNode ctx =
  nest 2 $ hcat (intersperse (text ", ") lstPre) <+> text "|-" <>
  hcat (intersperse (text "+") $ map (prettyACostCondition int) (costs ctx))
  <> text "-" <+> prettyPostCond (postCondition ctx) $+$ line $+$ line <>
  vcat (map (text . show) (history ctx)) $+$ line -- <$>
  -- hang 4 (text "Conditions: "
  -- <$> pretty (conditions ctx))
  where lstPre = map prettyPreCond (preConditions ctx)

prettyPostCond :: Show a => Maybe (a, ADatatype Int) -> Doc
prettyPostCond Nothing = empty
prettyPostCond (Just (f,d)) =
  text (show f) <+> text ":" <+> prettyADatatype (prettyACost int) d

prettyPreCond :: (String, ADatatype Int) -> Doc
prettyPreCond (a,b) = text a <> colon <+> prettyADatatype (prettyACost int) b

prettyPreCond' (a,b) =
  text a <> colon <+> prettyADatatype (prettyACost prettyVector) b

prettyInfTreeNodeView                        :: InfTreeNodeView -> Doc
prettyInfTreeNodeView (InfTreeNodeView pre cst post) =
  hcat (intersperse (text ", ") (map prettyPreCond' pre))
  <+> text "|-" <> hcat (intersperse (text "+") $
                         map (prettyACostCondition prettyVector) cst) <>
  text "-" <+> postTerm post <> postCost post
  where -- postTerm Nothing = empty
    postTerm (a,_) = text (show (L.pretty a))
      -- postCost Nothing = empty
    postCost (_,b) = if null (show postCostDoc)
                     then empty
                     else  text ":" <> postCostDoc
      where postCostDoc = prettyADatatype (prettyACost prettyVector) b


prettyInfTreeNodeView (InfTreeNodeLeafView sig cfSig) =
  prSig False sig <>
  (if isJust cfSig then text "    " <+> prSig True (fromJust cfSig) else empty)

  where prSig isCf (FunSig n pre cst post) =
          text n <> (if isCf then text "_cf" else empty) <+> text ":: [" <>
          hcat (intersperse (text " x ")
                 (map (prettyADatatype (prettyACost prettyVector)) pre))
          <> text "] -" <> hcat (intersperse (text "+")$
                                 map (prettyACostCondition prettyVector) cst)
          <> text "->" <+> prettyADatatype (prettyACost prettyVector) post

prettyInfTreeNodeView (InfTreeNodeLeafEmpty) = empty


--
-- Pretty.hs ends here
