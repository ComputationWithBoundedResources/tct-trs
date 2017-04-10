-- Ops.hs ---
--
-- Filename: Ops.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Wed Feb 18 21:02:32 2015 (+0100)
-- Version:
-- Package-Requires: ()
-- Last-Updated:
--           By:
--     Update #: 113
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
module Tct.Trs.Processor.ARA.ByInferenceRules.InfTreeNode.Ops
    ( putValuesInInfTreeView
    )
    where


import           Data.Rewriting.Typed.Term                                hiding
                                                                           (map)
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerSignature
import           Tct.Trs.Processor.ARA.ByInferenceRules.Data.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.InfTreeNode.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.Operator
import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Type


import           Control.Lens
import           Data.List                                                (find)
import           Debug.Trace

putValuesInInfTreeView :: ASigs
                       -> CfSigs
                       -> [Data Vector]
                       -> [[InfTreeNodeView]]
                       -> [[InfTreeNodeView]]
putValuesInInfTreeView sigs cfsigs vals = map (putValuesInInfTreeView' sigs cfsigs vals)

putValuesInInfTreeView' :: ASigs
                        -> CfSigs
                        -> [Data Vector]
                        -> [InfTreeNodeView]
                        -> [InfTreeNodeView]
putValuesInInfTreeView' sigs cfsigs vals = map (putValuesInInfTreeNodeView sigs cfsigs vals)

putValuesInInfTreeNodeView :: ASigs
                           -> CfSigs
                           -> [Data Vector]
                           -> InfTreeNodeView
                           -> InfTreeNodeView
putValuesInInfTreeNodeView sigs cfsigs vs (InfTreeNodeView pre csts post) =
  InfTreeNodeView (map (putValuesInPre sigs cfsigs vs) pre) (map (putValuesInCst vs) csts)
    (putValuesInPost sigs cfsigs vs post)
putValuesInInfTreeNodeView sigs cfsigs vs (InfTreeNodeLeafView sig cfSig) =
  InfTreeNodeLeafView (inSig sig) (fmap inSig cfSig)
  where inSig (FunSig n pre csts post) =
          FunSig n (map (snd . (\x -> putValuesInPre sigs cfsigs vs ("", x))) pre)
          (map (putValuesInCst vs) csts) (putValuesInPostLeaf sigs cfsigs vs post)
putValuesInInfTreeNodeView _ _ _ InfTreeNodeLeafEmpty = InfTreeNodeLeafEmpty


putValuesInPre :: ASigs
               -> CfSigs
               -> [Data Vector]
               -> (String, ADatatype Vector)
               -> (String, ADatatype Vector)
putValuesInPre sigs cfsigs vs (n, dt)   = (n, putValuesInDt sigs cfsigs vs dt)

putValuesInCst :: [Data Vector] -> ACostCondition Vector -> ACostCondition Vector
putValuesInCst vals (AVariableCondition n) = ACostValue (getValueNr vals n)
putValuesInCst vals (SigRefCst nr) = ACostValue (getValueNr vals n)
  where n = "k(" ++ show nr ++ ")"
putValuesInCst vals (SigRefCstCf nr) = ACostValue (getValueNr vals n)
  where n = "k_cf(" ++ show nr ++ ")"
putValuesInCst vals (ACostValue x) = ACostValue x

putValuesInPost :: ASigs
                -> CfSigs
                -> [Data Vector]
                -> (Term String String, ADatatype Vector)
                -> (Term String String, ADatatype Vector)
putValuesInPost sigs cfsigs vs (t, dt) = (t, putValuesInDt sigs cfsigs vs dt)


putValuesInPostLeaf :: ASigs
                    -> CfSigs
                    -> [Data Vector]
                    -> ADatatype Vector
                    -> ADatatype Vector
putValuesInPostLeaf = putValuesInDt


putValuesInDt :: ASigs
              -> CfSigs
              -> [Data Vector]
              -> ADatatype Vector
              -> ADatatype Vector
putValuesInDt _ _ _ (ActualCost isCf dt cst) = ActualCost isCf dt cst
putValuesInDt _ _ vals (SigRefVar dt n)    = ActualCost False dt (ACost $ getValueNr vals n)
putValuesInDt sigs cfsigs vals x =
  ActualCost fromCf dt (ACost $ getValueNr vals $ show x)
  where (fromCf, dt) = (\(ActualCost isCf x _) -> (isCf,x)) $ fetchSigValue sigs cfsigs x


getValueNr :: [Data Vector] -> String -> Vector
getValueNr vals label =
  case find ((== label) . view lab) vals of
    Nothing          -> 0
    Just (Data _ nr) -> nr


-- putValuesInACost                   :: [Data Int] -> ACost Int -> ACost Int
-- putValuesInACost vals (ACost x nr) = ACost x nr


--
-- Ops.hs ends here
