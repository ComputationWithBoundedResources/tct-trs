-- Ops.hs ---
--
-- Filename: Ops.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Fri Oct 10 14:08:54 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sun Apr  9 17:26:00 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 1324
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

{-# LANGUAGE CPP #-}

-- | TODO: comment this module
module Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerSignature.Ops
    ( insertSignature
    -- , setEqADt
    , fetchSigValue
    -- , fetchSigValueSig
    )
    where

import           Data.Rewriting.Typed.Rule
import           Data.Rewriting.Typed.Signature
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerSignature.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.HelperFunctions
import           Tct.Trs.Processor.ARA.ByInferenceRules.Operator
import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Type
import           Tct.Trs.Processor.ARA.Constants
import           Tct.Trs.Processor.ARA.Exception
import           Tct.Trs.Processor.ARA.Pretty

import           Control.Exception                                             (throw)
import           Data.Function                                                 (on)
import           Data.List                                                     (delete,
                                                                                find,
                                                                                groupBy,
                                                                                maximumBy,
                                                                                sortBy)
import           Data.Maybe                                                    (fromMaybe)
import           Text.PrettyPrint

-- #ifdef DEBUG
import           Debug.Trace                                                   (trace)
-- #end if


insertSignature :: ASignatureSig -> [ASignatureSig] -> [ASignatureSig]
insertSignature = flip (++) . return

sigCst :: ASignatureSig -> ACost Vector
sigCst (Signature x _ _) = (\(_,c,_,_) -> c) x

fetchSig :: [Signature s (ADatatype t)] -> ADatatype t -> ADatatype t
fetchSig sigs (SigRefParam _ m n)   = lhsSig (sigs !! m) !! n
fetchSig sigs (SigRefRet _ nr)      = rhsSig (sigs !! nr)
fetchSig sigs (SigRefParamCf _ m n) = lhsSig (sigs !! m) !! n
fetchSig sigs (SigRefRetCf _ nr)    = rhsSig (sigs !! nr)
fetchSig _ x                        = x


fetchSigValue :: ASigs
              -> CfSigs
              -> ADatatype Vector
              -> ADatatype Vector
fetchSigValue asigs cfsigs (SigRefParam _ m n) =
    -- trace ("fetchSigValue 1")
    -- trace ("m: " ++ show m)
    -- trace ("n: " ++ show n)
    -- trace ("asigs: " ++ show asigs)
  let asigs' = map fst3 asigs
  in fetchSig asigs' (lhsSig (asigs' !! m) !! n)
fetchSigValue asigs cfsigs (SigRefRet _ nr) =
  -- trace ("fetchSigValue 2")
  let asigs' = map fst3 asigs
  in fetchSig asigs' (rhsSig (asigs' !! nr))
fetchSigValue asigs cfsigs (SigRefParamCf _ m n) =
  -- trace ("fetchSigValue 3")
  -- (if m==4 && n==1
  --  then trace ("m: " ++ show m)
  --       trace ("n: " ++ show n)
  --       trace ("cfsigs: " ++ show cfsigs)
  --  else id)
  let cfsigs' = map fst3 cfsigs
  in fetchSig cfsigs' (lhsSig (cfsigs' !! m) !! n)
fetchSigValue asigs cfsigs (SigRefRetCf _ nr) =
  -- trace ("fetchSigValue 4")
  -- trace ("cfsigs:" ++ show cfsigs)
  -- trace ("nr: " ++ show nr)
  let cfsigs' = map fst3 cfsigs
  in fetchSig cfsigs' (rhsSig (cfsigs' !! nr))
fetchSigValue _ _ x =
  -- trace ("fetchSigValue 5")
  x


fetchCstValue :: [ASignatureSig] -> [ASignatureSig] -> ACostCondition Vector -> ACost Vector
fetchCstValue asigs cfsigs (SigRefCst nr)   = sigCst (asigs !! nr)
fetchCstValue asigs cfsigs (SigRefCstCf nr) = sigCst (cfsigs !! nr)
fetchCstValue _ _ (ACostValue b)            = ACost b


equalASig :: ASigs -> CfSigs -> ASignatureSig -> ASignatureSig -> Bool
equalASig sigs cfsigs (Signature (_,c0,_,_) lhs0 rhs0)  (Signature (_,c1,_,_) lhs1 rhs1) =
  c0 == c1 && length lhs0' == length lhs1' && and (zipWith (==) lhs0' lhs1') && rhs0' == rhs1'

    where lhs0' = map (fetchSigValue sigs cfsigs) lhs0
          rhs0' = fetchSigValue sigs cfsigs rhs0
          lhs1' = map (fetchSigValue sigs cfsigs)  lhs1
          rhs1' = fetchSigValue sigs cfsigs rhs1


--
-- Ops.hs ends here
