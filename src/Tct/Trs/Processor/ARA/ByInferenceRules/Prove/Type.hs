-- Type.hs ---
--
-- Filename: Type.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Fri Sep  5 08:52:29 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sat Apr  8 15:22:49 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 248
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
module Tct.Trs.Processor.ARA.ByInferenceRules.Prove.Type
    ( Prove (..)
    , InfTreeNode (..)
    -- , CtxStatement (..)
    , InfTreeNodeView (..)
    )
    where


import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerSignature
import           Tct.Trs.Processor.ARA.ByInferenceRules.InfTreeNode
import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures
import           Tct.Trs.Processor.ARA.Constants


data Prove = Prove
    { infTreeNodesToProve :: [InfTreeNode]
    , provenInfTreeNodes  :: [InfTreeNode]
    , countCostVars       :: Int
    , problem             :: ProblemSig
    , costFreeSigs        :: CfSigs
    , signatureMap        :: ASigs
    , conditions          :: ACondition Int Int
    , varNr               :: Int
    } deriving (Show)


--
-- Type.hs ends here

