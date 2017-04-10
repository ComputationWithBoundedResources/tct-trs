-- TypeSignatures.hs ---
--
-- Filename: TypeSignatures.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Wed Oct  1 16:02:50 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sun Apr  9 17:30:01 2017 (+0200)
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
module Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures where

import           Data.Rewriting.Typed.Datatype
import           Data.Rewriting.Typed.Problem
import           Data.Rewriting.Typed.Signature
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Type

import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype.Ops

import           Text.PrettyPrint


type ASignatureSig = Signature (String, ACost Vector, Bool, Bool) (ADatatype Vector)
type SignatureSig = Signature (String, ACost Int, Bool,Bool) (String, [ACost Int])
type ProblemSig  = Problem String String (String, ACost Int, Bool,Bool)
                   (String,[ACost Int]) (String, [ACost Int]) (String, ACost Int)

type DatatypeSig = Datatype (String, [ACost Int]) (String, ACost Int)
type ConstructorSig = Constructor (String, [ACost Int]) (String, ACost Int)
type ConstructorChildSig = ConstructorChild (String, [ACost Int])

--
-- TypeSignatures.hs ends here
