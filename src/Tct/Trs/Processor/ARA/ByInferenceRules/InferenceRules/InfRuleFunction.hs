-- InfRuleFunction.hs ---
--
-- Filename: InfRuleFunction.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Mon Sep 15 15:05:19 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Tue Apr 11 14:11:39 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 1214
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
module Tct.Trs.Processor.ARA.ByInferenceRules.InferenceRules.InfRuleFunction
    ( function

    )
    where


import           Data.Rewriting.Typed.Problem
import           Data.Rewriting.Typed.Rule
import           Data.Rewriting.Typed.Signature
import           Data.Rewriting.Typed.Term                                         hiding
                                                                                    (map)
import           Tct.Trs.Processor.ARA.ByInferenceRules.Analyzer.StartingProve
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerSignature
import           Tct.Trs.Processor.ARA.ByInferenceRules.CmdLineArguments
import           Tct.Trs.Processor.ARA.ByInferenceRules.HelperFunctions
import           Tct.Trs.Processor.ARA.ByInferenceRules.InferenceRules.InfRuleMisc
import           Tct.Trs.Processor.ARA.ByInferenceRules.InfTreeNode.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.Operator
import           Tct.Trs.Processor.ARA.ByInferenceRules.Prove
import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Type
import           Tct.Trs.Processor.ARA.Constants
import           Tct.Trs.Processor.ARA.Exception
import           Tct.Trs.Processor.ARA.Pretty

import           Control.Arrow
import           Control.Exception
                                                                                    (throw)
import           Data.Function
                                                                                    (on)
import           Data.List
                                                                                    (find,
                                                                                    sort,
                                                                                    sortBy,
                                                                                    transpose)
import           Data.Maybe
import           Text.PrettyPrint

#ifdef DEBUG
import           Debug.Trace
#endif


-- | This includes 3 different types of function applications:
-- 1. Application of non-cost free types.
-- 2. Application of cost-free types.
-- 3. Application for the constructor well-typedness inference (using Eq instead of Geq).
function :: ArgumentOptions
         -> [(String,Integer)]
         -> [String]
         -> (ProblemSig,  CfSigs, ASigs, Int, ACondition Int Int, InfTreeNode)
         -> [(ProblemSig, CfSigs, ASigs, Int, ACondition Int Int, [InfTreeNode])]
function args reachability noCfDefSyms (prob, cfsigs, asigs, nr, conds,
               InfTreeNode pre cst (Just (Fun f fc, dt))
               i@(fn,ruleStr,isCtrDeriv,startCsts,sigNr,mCfSigIdx) his) =

  [(prob, cfsigs', asigs', nr', conds', InfTreeNode [] cst Nothing i his' : infTreesCf)
  | (fst . rhsSig) sig == dtName &&    -- 1. datatypes need to match
    all isVar fc &&                    -- 2. children are variables
    length pre == length varsRhs &&    -- 3. number of variables correlate
    length pre == length (lhsSig sig)  -- 4. the signature corresponds
  ]

  where sig = getSignatureByNameAndType' (fromJust $ signatures prob) f (getDt dt)
        -- signature of function f

        dtsChld = map fst (lhsSig sig)

        dtName :: String
        dtName = getDt (fetchSigValue asigs cfsigs $ toADatatypeVector dt)

        varsRhs = concatMap getTermVars fc

        allRls = allRules (rules prob)
        funName (Fun f' _) = f'
        funName _          = error "Lhs root symbol must be a function"

        fRules = filter (\r -> funName (lhs r) == f) allRls


        sigSCCNr name = snd $ head $ filter ((== name) . fst) reachability
        isInSCCOfStartSig
          | allowLowerSCC args = sigSCCNr f <= sigSCCNr fn
          | otherwise = sigSCCNr f == sigSCCNr fn

        isInNoCfDefSyms = f `elem` noCfDefSyms
        isCfBranch = isJust mCfSigIdx
        mCfSigLst | isJust mCfSigIdx = mCfSigIdx
                  | otherwise = Just []
        nonCfHasCfBranches = not (isConstructor f) && not isCtrDeriv &&
                             not isCfBranch && (f == fn || isInSCCOfStartSig) &&
                             not isInNoCfDefSyms
        cfBranchNeedSig = isCfBranch && (f /= fn || isInSCCOfStartSig)
        newSigToASig = not isCfBranch && (isConstructor f || f /= fn)
        newDefFunSigToASig = newSigToASig && not (isConstructor f)
        newSigToCfSig = (nonCfHasCfBranches || cfBranchNeedSig) &&
                        not recursiveCfDeriv
        recursiveCfDeriv
          | isJust mCfSigIdx = any ((==f) . fst) (fromJust mCfSigIdx)
          | otherwise = False

        emptyACond = ACondition [] [] []

        (cfsigs',infTreesCf,conds'')
          | not newSigToCfSig = (cfsigs, [], emptyACond)
          | otherwise =
            foldl
            (\(curCfSigs,curInfTrees,curConds) (rule@(Rule (Fun f ch) rhs)) ->
              let dts = fromMaybe [] (datatypes prob)
                  sigs = fromMaybe [] (signatures prob)
                  (_, (infTreeNds,newCfSigs,conds',_)) =
                    createInfTreeNodes (Right cfGrp) True (Just cfSigIdx) args dts sigs True
                    (rule, ([],curCfSigs,emptyACond,[]))

                  setCfHistory (InfTreeNode pre cst post (_,_,ch,cstRoot,_,lst) _) =
                    InfTreeNode pre cst post
                    (fn,ruleStr,ch,cstRoot,sigNr, lst)
                    (his ++ [(fst3 (last his) + 1, "function cf"
                             , InfTreeNodeView (map (second toADatatypeVector) pre)
                               (map toACostConditionVector cst)
                               (second toADatatypeVector (fromJust post)))])

                  setCfOrigin (InfTreeNode pre cst post (_,_,ch,cstRoot,_,_) his) =
                    InfTreeNode pre cst post
                    (fn,ruleStr,ch,cstRoot,sigNr,Just ((f,cfSigIdx):) <*> mCfSigLst) his
              in
                (newCfSigs
                 ,curInfTrees ++
                  (setCfHistory.setCfOrigin) (head infTreeNds) :
                  map setCfOrigin (tail infTreeNds)
                 ,curConds `addConditions` conds')

            ) (cfsigs ++ [(sig2ASig True args sig,cfGrp,"new cfSigs")],[],emptyACond) fRules

        cfSigIdx
          | newSigToCfSig = length cfsigs
          | otherwise = snd $ head (filter ((==f) . fst) (fromJust mCfSigIdx))

        cfGrp
          | not isCfBranch = maximum ((-1) : map snd3 cfsigs)+1
          | otherwise = snd3 (cfsigs !! snd (head $ fromJust mCfSigIdx))


        fromRule = snd3 (asigs !! sigNr)

        asigs' = asigs ++ [(sig2ASig False args sig, fromRule, "new aSigs from root: " ++
                            show sigNr ++ show his) |  newSigToASig ]

        asigIdx | isCfBranch = cfSigIdx       -- use CfSigIdx
                | newSigToASig = length asigs -- use ASigIdx & add new Signature
                | otherwise = baseSigNr       -- use ASigIdx, but baseSigIdx

        isConstructor f =
          case find ((== f) . fst4 . lhsRootSym . fst3) asigs of
            Nothing -> True
            Just x  -> (thd4 . lhsRootSym . fst3) x

        -- get base signature (that is the first signature in the set of
        -- signatures of this function)
        baseSig = fromJust $ find ((== f) . fst4 . lhsRootSym . fst3 . snd) (zip [0..] asigs)
        baseSigNr = fst baseSig

        -- cfBaseSig = find ((== f) . fst4 . lhsRootSym . fst3 . snd) (zip [0..] cfsigs)
        -- cfBaseSigNr = fmap fst cfBaseSig

        nPre :: [ADatatype Int]
        nPre = map (\(a,b) -> sigRefParam isCfBranch a asigIdx b) (zip dtsChld [0..])
        nPreVector :: [ADatatype Vector]
        nPreVector = map (\(a,b) -> sigRefParam isCfBranch a asigIdx b) (zip dtsChld [0..])

        fromVar (Var n) = n
        fromVar _       = error "programming error. Should not be possible."

        postVarOrder (a,_) =
          snd $ fromMaybe (error "not possible")
          (find ((== a) . fst) (zip (map fromVar varsRhs) [0..]))

        preSorted = sortBy (compare `on` postVarOrder) pre

        getRetCst (InfTreeNode _ _ (Just (_,cst)) _ _) = cst
        getRetCst _ = error "should not happen"


        -- create new variable c for costs
        (nr', nCVar)
          | isCfBranch || nonCfHasCfBranches = getNewVariableName nr 1
          | otherwise = (nr, [])

        conds' = conds { costCondition = costCondition conds ++ newCstCond
                                         ++ costCondition conds''
                       , dtConditions = dtConditions conds ++ newDtCond
                                        ++ dtConditions conds''
                       , shareConditions = shareConditions conds ++ newShareCond
                                           ++ shareConditions conds''
                       }

        -- sigRefCst | isCfBranch = SigRefCstCf
        --           | otherwise = SigRefCst
        -- sigRefParam | isCfBranch = SigRefParamCf
        --             | otherwise = SigRefParam
        -- sigRefRet | isCfBranch = SigRefRetCf
        --           | otherwise = SigRefRet

        newCstCond =
          -- ensure the costs are not growing too much
          [(cst, if isCtrDeriv then Eq else Geq
            , sigRefCst isCfBranch asigIdx :
             [SigRefCstCf cfSigIdx | nonCfHasCfBranches] ++
              fmap AVariableCondition nCVar)] ++
          [ ([SigRefCst asigIdx], Eq, [SigRefCst baseSigNr]) | newDefFunSigToASig ]

        newDtCond =
          zipWith (\r n -> ([snd r], Geq, sigRefParam isCfBranch "" asigIdx n:
                            [SigRefParamCf "" cfSigIdx n | nonCfHasCfBranches])) preSorted [0..]
          ++ [(sigRefRet isCfBranch "" asigIdx : [SigRefRetCf "" cfSigIdx | nonCfHasCfBranches], Geq, [dt])]
          ++ concatMap (\x ->
                           [([SigRefParam "" asigIdx x], Eq,
                             [SigRefParam "" baseSigNr x])
                           | newDefFunSigToASig ]
                       ) [0..length pre-1]
          ++ [([SigRefRet "" baseSigNr], Eq, [SigRefRet "" asigIdx]) | newDefFunSigToASig ]

        newShareCond
          | nonCfHasCfBranches =
            (dt, Eq, [SigRefRet "" asigIdx, SigRefRetCf "" cfSigIdx]) :
            map (\(a,b,c) -> (snd a, Eq, [b,c]))
            (zip3 preSorted nPre (map (SigRefParamCf "" cfSigIdx) [0..]))
          | otherwise = []

        his' = his ++ [(fst3 (last his) + 1, "function",
                        InfTreeNodeLeafView
                        (FunSig f nPreVector [sigRefCst isCfBranch asigIdx]
                          (sigRefRet isCfBranch "" asigIdx))
                       (if nonCfHasCfBranches
                         then Just $
                          FunSig f
                          (map (SigRefParamCf "" cfSigIdx) [0..length nPreVector-1])
                          [SigRefCstCf cfSigIdx]
                          (SigRefRetCf "" cfSigIdx)
                         else Nothing))]

function _ _ _ _ = []

--
-- InfRuleFunction.hs ends here

