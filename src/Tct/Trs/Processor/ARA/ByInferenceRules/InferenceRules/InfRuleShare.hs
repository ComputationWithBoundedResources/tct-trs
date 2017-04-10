-- InfRuleShare.hs ---
--
-- Filename: InfRuleShare.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Sun Sep 14 17:35:09 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sun Apr  9 17:30:00 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 419
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

#define DEBUG

-- | TODO: comment this module
module Tct.Trs.Processor.ARA.ByInferenceRules.InferenceRules.InfRuleShare
    ( share
    )
    where

import           Data.Rewriting.Typed.Datatype
import           Data.Rewriting.Typed.Problem
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerSignature
import           Tct.Trs.Processor.ARA.ByInferenceRules.InferenceRules.InfRuleMisc
import           Tct.Trs.Processor.ARA.ByInferenceRules.Operator
import           Tct.Trs.Processor.ARA.ByInferenceRules.Prove
import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures
import           Tct.Trs.Processor.ARA.Constants
import           Tct.Trs.Processor.ARA.Exception


import           Control.Arrow
import           Control.Exception
                                                                                    (throw)
import           Data.Function
                                                                                    (on)
import           Data.List
                                                                                    (delete,
                                                                                    find,
                                                                                    foldl',
                                                                                    group,
                                                                                    groupBy,
                                                                                    sort,
                                                                                    sortBy,
                                                                                    (\\))
import           Data.Maybe
                                                                                    (fromMaybe)
import           Data.Ord
                                                                                    (compare)

import           Text.PrettyPrint


#ifdef DEBUG
import           Debug.Trace
                                                                                    (trace)
#endif

share :: (ProblemSig, CfSigs, ASigs, Int, ACondition Int Int, InfTreeNode)
         -> [(ProblemSig, CfSigs, ASigs, Int, ACondition Int Int, [InfTreeNode])]
share (prob, cfsigs, asigs, nr, conds, InfTreeNode pre cst (Just (Fun f fc, dt)) fn his) =
  -- trace ("share")

  -- trace ("pre:" ++ show groupedPre)
  -- trace ("post:" ++ show groupedPostVars)
  -- trace ("pre':" ++ show (concat pre'))
  -- trace ("shareConds:" ++ show shareConds)
  -- trace ("post':" ++ show post')
  -- trace ("nr':" ++ show nr')

    -- trace ("help: " ++ show (pretty (InfTreeNode pre cst (Just (Fun f fc, dt)) fn [])))

    -- trace ("\n\nfunctionName: " ++ show f)
    -- -- trace ("varPostGroups: " ++ show varPostGroups)
    -- -- trace ("any ((>1) . length) varPostGroups: " ++ show (any ((>1) . length) varPostGroups))
    -- trace ("before: " ++ show (InfTreeNode pre cst (Just $ (Fun f fc, dt)) fn []))
    -- trace ("after: " ++ show (InfTreeNode (concat pre') cst (Just (post', dt)) fn []))

    -- trace ("varsPost: " ++ show varsPost)
    -- trace ("varsToReplace: " ++ show varsToReplace)
    -- trace ("subs: " ++ show subs)
    -- trace ("groupedPre: " ++ show groupedPre )
    -- trace ("groupedPostVars: " ++ show groupedPostVars)
    -- trace ("pre: " ++ show pre)
    -- trace ("pre': " ++ show pre')

  [ (prob, cfsigs, asigs, nr', conds', [InfTreeNode (concat pre') cst (Just (post', dt)) fn his'])
  | any ((>1) . length) varPostGroups
  ]

  where varsPost :: [String]
        varsPost = map (\(Var x) -> x) (concatMap getTermVars fc)

        varPostGroups = group $ sort varsPost
        -- varsToReplace = concat $ filter ((>1) . length) varPostGroups

        groupedPre :: [(String, ADatatype Int)]
        groupedPre =
          -- groupBy ((==) `on` fst) $
          sortBy (compare `on` fst) $ -- grouped pre vars
          filter ((`elem` varsPost) . fst) pre

        groupedPostVars :: [[String]]
        groupedPostVars = group (sort varsPost)

        hisNr | null his = 0
              | otherwise = fst3 (last his) + 1
        his' = his ++ [(hisNr, "share",
                        InfTreeNodeView
                        (map (second toADatatypeVector) $
                         concat pre')
                        (map toACostConditionVector cst)
                        (post', toADatatypeVector dt))]


        conds' = conds { shareConditions = shareConditions conds ++ shareConds }

        shareConds = foldl shareConds' [] (zip pre pre')
        shareConds' :: [(ADatatype Int, Comparison, [ADatatype Int])]
                    -> ((String, ADatatype Int), [(String, ADatatype Int)])
                    -> [(ADatatype Int, Comparison, [ADatatype Int])]
        shareConds' acc (_, [_]) = acc
        shareConds' acc (preDt, postDts) = acc ++ [(snd preDt, Geq, map snd postDts)]

        origPreOrd ((a,_),_)=
          snd $
          fromMaybe (error "should not happen")
          (find ((== a) . fst . fst) (zip pre [0..]))

        (pre', nr') =
          -- trace ("(zip groupedPre groupedPostVars): " ++ show (zip groupedPre groupedPostVars)) $
          foldl createPre' ([], nr) $
          sortBy (compare `on` origPreOrd) --revert original order
          (zip groupedPre groupedPostVars)


        createPre' :: ([[(String, ADatatype Int)]], Int)
                   -> ((String, ADatatype Int), [String])
                   -> ([[(String, ADatatype Int)]], Int)
        createPre' (p', nrTmp) (pres, [_]) = (p' ++ [[pres]], nrTmp)
        createPre' (p', nrTmp) (pres, posts) = (p' ++ [p''], nrTmp')
          where (p'', nrTmp') = foldl fun ([], nrTmp) posts
                fun :: ([(String, ADatatype Int)], Int)
                    -> String
                    -> ([(String, ADatatype Int)], Int)
                fun (pres', nr'') _ = (pres' ++ [(varName, SigRefVar dtVar varName)], nr''+1)
                  where varName = varPrefix ++ show nr''
                        dtVar = actCostDt $ fetchSigValue asigs cfsigs (toADatatypeVector $ snd pres)
                        actCostDt (ActualCost _ dt' _) = dt'
                        actCostDt (SigRefVar dt' _) = dt'
                        actCostDt _ = error "should not be possible"

        subs =
          concat $
          zipWith (\a b -> if length b == 1
                          then []
                          else [(fst a, map fst b)]
                  ) (filter ((`elem` varsPost) . fst) pre) pre'


        post' :: Term String String
        post' = Fun f (snd $ foldl putVarsIntoTerm (subs, []) fc)

        putVarsIntoTerm :: ([(String, [String])], [Term String String])
                        -> Term String String
                        -> ([(String, [String])], [Term String String])
        putVarsIntoTerm (vs, acc) (Var v) =
          case find (\x -> v == fst x) vs of
            Nothing -> (vs, acc ++ [Var v])
            Just (x,ls) -> if length ls == 1
                          then (delete (x,ls) vs, acc ++ [Var (head ls)])
                          else ((x, tail ls) : delete (x,ls) vs, acc ++ [Var (head ls)])
        putVarsIntoTerm (vs, acc) (Fun f ch) = (vs', acc ++ [Fun f ch'])
          where (vs', ch') = foldl putVarsIntoTerm (vs, []) ch

share _ = []


--
-- InfRuleShare.hs ends here
