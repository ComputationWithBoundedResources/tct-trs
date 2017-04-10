-- ConvertSolutionToData.hs ---
--
-- Filename: ConvertSolutionToData.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Tue May 24 11:48:32 2016 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sun Apr  9 17:27:30 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 272
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

module Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.SMT.ConvertSolutionToData
    ( convertToData
    , replList'
    ) where

import           Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.SMT.Type

import           Data.Rewriting.Typed.Signature
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerSignature
import           Tct.Trs.Processor.ARA.ByInferenceRules.CmdLineArguments
import           Tct.Trs.Processor.ARA.ByInferenceRules.Data.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.HelperFunctions
import           Tct.Trs.Processor.ARA.ByInferenceRules.Operator
import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Pretty
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Type
import           Tct.Trs.Processor.ARA.Exception

import           Control.Arrow
import           Control.Exception
                                                                                   (throw)
import           Control.Lens                                                     hiding
                                                                                   (use)
import           Control.Monad
import           Control.Monad.State
import           Data.Function
                                                                                   (on)
import           Data.List
import qualified Data.Map.Strict                                                  as M
import           Data.Maybe
                                                                                   (fromJust,
                                                                                   fromMaybe,
                                                                                   isNothing)
import qualified Data.Text                                                        as T
import           Debug.Trace
import           Text.PrettyPrint                                                 hiding
                                                                                   (empty)


convertToData :: Int -> M.Map String Int -> ([Data Int], [Data Vector])
convertToData vecLen m =
  let -- m = M.mapKeys fromEncoding m'
      isNs k _ = head k == 'n'
      mNs = M.filterWithKey isNs m
      mVs = M.filterWithKey (\k v -> not (isNs k v)) m
      ns = M.toList mNs         -- fromEncoding needed?
      sortFun [] = error "not possible"
      sortFun str@(x:_)
        | x == 'v' = drop 3 str
        | otherwise = str
      vsData =
        map toVector                          -- sort: [[v1_X, v2_X,...], ...]
        $ groupBy ((==) `on` sortFun . fst)   -- group same vars
        $ sortBy (compare `on` sortFun . fst) -- sort for grouping same vars
        $ M.toList mVs
      fromList = map (uncurry Data)
      nsData = fromList ns
  in
    -- trace ("plain ns data: " ++ unlines (map show nsData))
    -- trace ("plain vs data: " ++ unlines (map show vsData))

    (nsData, vsData)

toVector :: [(String, Int)] -> Data Vector
toVector xs
  | length xs == 1 = Data name (Vector1 (v 0))
  | length xs == 2 = Data name (Vector2 (v 0) (v 1))
  | length xs == 3 = Data name (Vector3 (v 0) (v 1) (v 2))
  | length xs == 4 = Data name (Vector4 (v 0) (v 1) (v 2) (v 3))
  | length xs == 5 = Data name (Vector5 (v 0) (v 1) (v 2) (v 3) (v 4))
  | length xs == 6 = Data name (Vector6 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
  | length xs == 7 = Data name (Vector7 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
  | otherwise = error "Vector length > 7 is not availabe yet"
  where sorted = sortBy (compare `on` fst) xs
        v x = snd $ sorted !! x
        name = fromEncoding (fst $ head xs)

remUnderscore :: Char -> Char
remUnderscore '_' = ','
remUnderscore x   = x

replCommaNr :: Int -> String -> String
replCommaNr nr = replFirstComma' 1 []
  where replFirstComma' _ acc [] = acc
        replFirstComma' i acc (c:cs)
          | nr == i && c == ',' = acc ++ '_' : cs
          | c == ',' = replFirstComma' (i+1) (acc ++ [c]) cs
          | otherwise = replFirstComma' i (acc ++ [c]) cs

replFirstComma = replCommaNr 1


fromEncoding       :: String -> String
fromEncoding str
  | head str == 'v' = fromEncoding (drop 3 str)         -- exp.: v1_k_cf2 ...recurse!
  | "rictr" `isInfixOf` str = str
  | take 5 str == "kctr_" && "cf_" `isInfixOf` str =    -- exp.: kctr_NAT_cf_cons_2
      "k_cf(" ++ tail str ++ ")"
  | take 4 str == "k_cf" = "k_cf(" ++ drop 4 str ++ ")" -- exp.: k_cf2
  | head str == 'k' = "k(" ++ tail str ++ ")"           -- exp.: k3
  | take 5 str == "rctr_" && "cf_" `isInfixOf` str =    -- exp.: rctr_LIST_cf_pair_1
      "r_cf(" ++ tail str ++ ")"
  | take 4 str == "r_cf" = "r_cf(" ++ drop 4 str ++ ")" -- exp.: r_cf2
  | head str == 'r' = "r(" ++ tail str ++ ")"           -- exp.: r2
  | take 5 str == "pctr_" && "cf" `isInfixOf` str =     -- exp.: pctr_A_cf_cons_0_1
      let typeName = takeWhile (/= '_') (drop 5 str)
          rest = drop (9+length typeName) str
      in "p_cf(ctr_" ++ typeName ++ "_cf_" ++
         replFirstComma (convertFromSMTString (map remUnderscore rest))
         ++ ")"
  | head str == 'p' && "ctr" `isInfixOf` str =          -- exp.: pctr_A_cons_1_1
      let typeName = takeWhile (/= '_') (drop 5 str)
          rest = drop (6+length typeName) str
      in "p(ctr_" ++ typeName ++ "_" ++
         replFirstComma (convertFromSMTString (map remUnderscore rest))
         ++ ")"
  | head str == 'p' && "cf" `isInfixOf` str =           -- exp.: p_cf2_0
      "p_cf(" ++
      convertFromSMTString (map remUnderscore (drop 4 str))
      ++ ")"
  | head str == 'p' =                                   -- exp.: p6_0
      "p(" ++ map remUnderscore (tail str) ++ ")"
  | otherwise = str                                     -- ipvar* or similar


--
-- ConvertSolutionToData.hs ends here

