-- Type.hs ---
--
-- Filename: Type.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Tue Jan  3 10:27:49 2017 (+0100)
-- Version:
-- Package-Requires: ()
-- Last-Updated:
--           By:
--     Update #: 21
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

module Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerSignature.Type where

import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures

type FromRule = Int
type ASigs = [(ASignatureSig, FromRule, String)]

type CfSigGroup = Int
type CfSig = (ASignatureSig, CfSigGroup, String)
type CfSigs = [CfSig]

-- addASig :: ASigs -> ASignatureSig ->


--
-- Type.hs ends here
