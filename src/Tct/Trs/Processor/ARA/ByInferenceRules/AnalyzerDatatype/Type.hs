-- Type.hs ---
--
-- Filename: Type.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Wed Oct  1 15:42:45 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sat Apr  8 15:22:48 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 109
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
module Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype.Type
    ( ADatatype (..)
    , toADatatypeVector
    , getDt
    )
    where

import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.Operator
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Type

data ADatatype a = ActualCost Bool String (ACost a) -- ^ was Cf, data-type and costs
                 | SigRefParam String Int Int -- ^ m n: the same as the n'th element of the m'th sig
                 | SigRefRet String Int       -- ^ same return data-type as the m'th signature
                 | SigRefVar String String -- ^ datatype and variable name for share rule
                 | SigRefParamCf String Int Int -- ^ m n: the same as the n'th element of the m'th sig
                 | SigRefRetCf String Int       -- ^ same return data-type as the m'th signature

toADatatypeVector :: ADatatype Int -> ADatatype Vector
toADatatypeVector (ActualCost cf dt (ACost cst)) = ActualCost cf dt (ACost (Vector1 cst))
toADatatypeVector (SigRefRet dt x)     = SigRefRet dt x
toADatatypeVector (SigRefParam dt m n) = SigRefParam dt m n
toADatatypeVector (SigRefVar dt v)  = SigRefVar dt v
toADatatypeVector (SigRefRetCf dt x) = SigRefRetCf dt x
toADatatypeVector (SigRefParamCf dt m n) = SigRefParamCf dt m n


getDt :: ADatatype t -> String
getDt (ActualCost _ d _)     = d
getDt (SigRefRet dt x)       = dt
getDt (SigRefParam dt m n)   = dt
getDt (SigRefVar dt v)       = dt
getDt (SigRefRetCf dt x)     = dt
getDt (SigRefParamCf dt m n) = dt


instance Show a => Show (ADatatype a) where
  show (SigRefRet _ x)        = "r(" ++ show x ++ ")"
  show (SigRefParam _ m n)    = "p(" ++ show m ++ "," ++ show n ++ ")"
  show (SigRefVar dt v)       = v -- ++ ":" ++ dt
  show (SigRefRetCf _ x)      = "r_cf(" ++ show x ++ ")"
  show (SigRefParamCf _ m n)  = "p_cf(" ++ show m ++ "," ++ show n ++ ")"
  show (ActualCost cf dt cst) = show cst -- ++ ":" ++ dt


--
-- Type.hs ends here
