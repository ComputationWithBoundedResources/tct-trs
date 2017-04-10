-- HelperFunctions.hs ---
--
-- Filename: HelperFunctions.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Fri Oct 10 15:46:17 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sun Apr  9 17:29:59 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 105
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
module Tct.Trs.Processor.ARA.ByInferenceRules.HelperFunctions where

import           Data.Rewriting.Typed.Datatype
import           Data.Rewriting.Typed.Signature
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost.Pretty
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype.Pretty
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Pretty
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Type
import           Tct.Trs.Processor.ARA.Constants
import           Tct.Trs.Processor.ARA.Exception
import           Tct.Trs.Processor.ARA.Pretty

import           Control.Exception                                              (throw)
import           Data.List                                                      (find)
import           Data.Maybe                                                     (fromMaybe)
import           Debug.Trace
import           Text.PrettyPrint


-- | @getSignatureByName sigs sigName@ checks all signatures defined in @sigs@
-- and searches for the one with the name @sigName@.
getSignatureByNameAndType :: [SignatureSig] -> String -> String -> Maybe SignatureSig
getSignatureByNameAndType sigs sig dt =
  find (\(Signature (n,_,_,_) _ (dtRhs,_)) -> dt == dtRhs && n == sig) sigs

-- | @getSignatureByName sigs sigName@ checks all signatures defined in @sigs@
-- and searches for the one with the name @sigName@.
getDefSymSignatureByName :: [SignatureSig] -> String -> Maybe SignatureSig
getDefSymSignatureByName sigs sig =
  find (\(Signature (n,_,isCtr,_) _ _) -> not isCtr && n == sig) sigs


-- | @getSignatureByName' sigs sigName@ finds the signature with the name
-- @sigName@ from the list of signatures @sigs@ and returns it. If it cannot be
-- found an exception will be throws!
getSignatureByNameAndType' :: [SignatureSig] -> String -> String -> SignatureSig
getSignatureByNameAndType' sigs sigName dt =
  fromMaybe (throw $ FatalException $ "Cannot find signature for " ++
                   show (text sigName))
            (getSignatureByNameAndType sigs sigName dt)

-- | @getSignatureByName sigs sigName@ checks all signatures defined in @sigs@
-- and searches for the one with the name @sigName@.
getDefSymSignatureByName' :: [SignatureSig] -> String -> SignatureSig
getDefSymSignatureByName' sigs sig =
  fromMaybe (throw $ FatalException $ "Cannot find signature for " ++
                   show (text sig))
  (getDefSymSignatureByName sigs sig)

-- | @getDatatypeByName dts dtName@ takes as input a list of parsed data-types
-- @dts@ and a name @dtName@ to search for in the list. It either returns the
-- data-type wrapped in a Just or it will returns Nothing.
getDatatypeByName         :: [DatatypeSig] -> String -> Maybe DatatypeSig
getDatatypeByName dts str = find ((== str) . (\(Datatype dtn _) -> fst dtn)) dts


-- | @getDatatypeByName' dts dtName@ takes as input a list of parsed data-types
-- @dts@ and a name @dtName@ to search for in the list. It returns the datatype
-- if any was found or throws an exception, if it cannot find the datatype named
-- @dtName@.
getDatatypeByName'         :: [DatatypeSig] -> String -> DatatypeSig
getDatatypeByName' dts str =
  fromMaybe (throw $ FatalException $ "Could not find datatype " ++
             str ++ ". However, you used it in the signature block!")
            (getDatatypeByName dts str)


fst3 :: (a,b,c) -> a
fst3 (a,_,_) = a
snd3 :: (a,b,c) -> b
snd3 (_,b,_) = b
thd3 :: (a,b,c) -> c
thd3 (_,_,c) = c

fst4 :: (t, t1, t2, t3) -> t
fst4 (x,_,_,_) = x
snd4 :: (t, t1, t2, t3) -> t1
snd4 (_,x,_,_) = x
thd4 :: (t, t1, t2, t3) -> t2
thd4 (_,_,x,_) = x
fth4 :: (t, t1, t2, t3) -> t3
fth4 (_,_,_,x) = x


prettyAraSignature' :: ASignatureSig -> Doc
prettyAraSignature' =
  prettyAraSignature text (prettyACost prettyVector) (prettyADatatype (prettyACost prettyVector ))

sigRefRet isCf = if isCf then SigRefRetCf else SigRefRet
sigRefParam isCf = if isCf then SigRefParamCf else SigRefParam
sigRefCst isCf = if isCf then SigRefCstCf else SigRefCst


--
-- HelperFunctions.hs ends here
