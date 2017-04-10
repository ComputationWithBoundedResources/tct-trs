-- Type.hs ---
--
-- Filename: Type.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Mon Oct  6 23:24:12 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sat Apr  8 15:22:37 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 75
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
module Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition.Type
    ( ACondition (..)
    , ACostCondition (..)
    , toACostConditionVector
    )
    where


import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype.Ops  ()
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.Operator
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Type

data ACondition a b = ACondition
              { costCondition   :: [([ACostCondition a], Comparison, [ACostCondition a])] -- ^
              , dtConditions    :: [([ADatatype b], Comparison, [ADatatype b])] -- ^
              , shareConditions :: [(ADatatype b, Comparison, [ADatatype b])] -- ^
              } deriving (Show, Eq)

data ACostCondition a = AVariableCondition String
                      | SigRefCst Int
                      | SigRefCstCf Int
                      | ACostValue a
                      deriving (Eq)

toACostConditionVector :: ACostCondition Int -> ACostCondition Vector
toACostConditionVector (ACostValue x)         = ACostValue (Vector1 x)
toACostConditionVector (SigRefCst x)          = SigRefCst x
toACostConditionVector (SigRefCstCf x)        = SigRefCstCf x
toACostConditionVector (AVariableCondition x) = AVariableCondition x


instance Show a => Show (ACostCondition a) where
  show (AVariableCondition x) = x
  show (SigRefCst nr)         = "k(" ++ show nr ++ ")"
  show (SigRefCstCf nr)       = "k_cf(" ++ show nr ++ ")"
  show (ACostValue nr)        = show nr


--
-- Type.hs ends here
