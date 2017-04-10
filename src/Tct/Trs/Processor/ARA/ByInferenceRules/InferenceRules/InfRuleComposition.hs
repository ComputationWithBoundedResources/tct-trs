-- InfRuleComposition.hs ---
--
-- Filename: InfRuleComposition.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Tue Sep 16 01:46:07 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sun Apr  9 17:41:44 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 642
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

{-# LANGUAGE CPP #-}

#ifndef DEBUG
#define DEBUG
#endif

-- | TODO: comment this module
module Tct.Trs.Processor.ARA.ByInferenceRules.InferenceRules.InfRuleComposition
    ( composition

    )
    where

import           Data.Rewriting.Typed.Datatype
import           Data.Rewriting.Typed.Problem
import           Data.Rewriting.Typed.Rule
import           Data.Rewriting.Typed.Signature
import           Data.Rewriting.Typed.Term
                                                                                        (isVar)
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerSignature
import           Tct.Trs.Processor.ARA.ByInferenceRules.HelperFunctions
import           Tct.Trs.Processor.ARA.ByInferenceRules.InferenceRules.InfRuleFunction
import           Tct.Trs.Processor.ARA.ByInferenceRules.InferenceRules.InfRuleMisc
import           Tct.Trs.Processor.ARA.ByInferenceRules.Operator
import           Tct.Trs.Processor.ARA.ByInferenceRules.Prove
import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Type
import           Tct.Trs.Processor.ARA.Constants
import           Tct.Trs.Processor.ARA.Exception

import           Control.Arrow
import           Control.Exception
                                                                                        (throw)
import           Data.List
                                                                                        (find,
                                                                                        sort,
                                                                                        sortBy,
                                                                                        zip4)
import           Data.Maybe
                                                                                        (fromJust,
                                                                                        fromMaybe)
import           Text.PrettyPrint

#ifdef DEBUG
import           Debug.Trace
#endif


composition :: (ProblemSig, CfSigs, ASigs, Int, ACondition Int Int, InfTreeNode)
         -> [(ProblemSig, CfSigs, ASigs, Int, ACondition Int Int, [InfTreeNode])]
composition (prob, cfsigs, asigs, nr, conds, InfTreeNode pre cst (Just (Fun f fc, dt))
              i@(_,ruleStr,isCtrDeriv,cstsStart,_,_) his) =

 [ (prob, cfsigs, asigs, nr'+1, conds', funParNode : funChildNodes)
 | length pre == length fcVars &&             -- 1. number of variables fit
   any (not . isVar) fc &&                     -- 2. function is not applicable
   and (zipWith (==) preDtSorted fcDtSorted) -- 3. datatypes match
 ]

  where fcVars = concatMap getTermVars fc

        preDtSorted :: [String]
        preDtSorted = sort (map ((\(_, x) -> actCostDt (fetchSigValue asigs cfsigs x))
                                 . second toADatatypeVector) pre)

        fcDtSorted :: [String]
        fcDtSorted = sort dtFunChld

        actCostDt (ActualCost _ dt' _) = dt'
        actCostDt (SigRefVar dt' _)    = dt'
        actCostDt _                    = error "should not happen"

        sig = getSig f (getDt dt)          -- signature of function f
        getSig :: String -> String -> SignatureSig
        getSig = getSignatureByNameAndType' (fromJust $ signatures prob)

        dtFunChld :: [String]
        dtFunChld = map fst $ concatMap getDtsRhs (zip fc (lhsSig sig))

        getDtsRhs (Var _, dt') = [dt']
        -- getDtsRhs (Fun _ [], dt') = [dt']
        getDtsRhs (Fun f' ch, dt') = concatMap getDtsRhs (zip ch (lhsSig sigF))
          where sigF = getSig f' (fst dt')

        nr' = nr + length fc + length fc

        conds' = ACondition (costCondition conds ++ nCostCond) (dtConditions conds ++ nDtCond)
                   (shareConditions conds ++ nShareCond)

        nCostCond = [(cst, if isCtrDeriv then Eq else Geq,
                      map AVariableCondition strVarsCost)]
        nDtCond = []
        nShareCond = []

        newVars :: [String]
        newVars = map ((varPrefix ++) . show) [nr..nr']

        strVarsCost = drop (length fc) newVars
        strVarsNode = take (length fc) newVars
        -- varsCost = map Var (drop (length fc) newVars)
        varsNode = map Var (take (length fc) newVars)


        funParNode :: InfTreeNode
        funParNode = InfTreeNode funParNodeParams funParNodeCsts funParNodeFunc i hisFunParNode
          where
            funParNodeParams :: [(String, ADatatype Int)]
            funParNodeParams = zip strVarsNode (zipWith SigRefVar (map fst $ lhsSig sig) strVarsNode)
            funParNodeCsts :: [ACostCondition a]
            funParNodeCsts = [AVariableCondition (head strVarsCost)]
            funParNodeFunc = Just (Fun f varsNode, dt)


            hisFunParNode = his ++ [(fst3 (last his) + 1, "comp fun",
                                     InfTreeNodeView
                                     (map (second toADatatypeVector) funParNodeParams)
                                     funParNodeCsts
                                     (second toADatatypeVector $ fromJust funParNodeFunc))]


        funChildNodes :: [InfTreeNode]
        funChildNodes = fst $ foldl funChildNodes' ([], pre)
                        (zip4 fc (tail strVarsCost) strVarsNode (map fst $ lhsSig sig))
          where
            funChildNodes' :: ([InfTreeNode], [(String, ADatatype Int)])
                           -> (Term String String, String, String, String)
                           -> ([InfTreeNode], [(String, ADatatype Int)])
            funChildNodes' (acc, pres) (term, costVar, varName, dtStr) =
              (acc ++ [chldNode], restPres)
                where chldNode :: InfTreeNode
                      chldNode = -- trace ("his: " ++ show hisChld) $
                        InfTreeNode chldPres [AVariableCondition costVar]
                                   (Just (term, SigRefVar dtStr varName)) i hisChld
                      (chldPres, restPres) = foldl fun ([],[]) pres

                      hisChld = his ++ [(fst3 (last his) + 1, "comp chld",
                                         InfTreeNodeView
                                         (map (second toADatatypeVector) chldPres)
                                         [AVariableCondition costVar]
                                         (term, SigRefVar dtStr varName))]

                      fun :: ([(String, ADatatype Int)], [(String, ADatatype Int)])
                          -> (String, ADatatype Int)
                          -> ([(String, ADatatype Int)], [(String, ADatatype Int)])
                      fun (good, bad) var = if fst var `elem` varsTerm
                                              then (good  ++ [var], bad)
                                              else (good, bad ++ [var])

                      varsTerm = map fromVar $ getTermVars term

            fromVar (Var v) = v

composition _ = []


--
-- InfRuleComposition.hs ends here
