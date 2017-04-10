-- Pretty.hs ---
--
-- Filename: Pretty.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Wed Oct  1 15:55:48 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sat Apr  8 15:22:56 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 90
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
module Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost.Pretty
    ( prettyACost

    )
    where


import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost.Type

import           Text.PrettyPrint

prettyACost                       :: (a -> Doc) -> ACost a -> Doc
prettyACost pACst (ACost cst) = pACst cst


--
-- Pretty.hs ends here
