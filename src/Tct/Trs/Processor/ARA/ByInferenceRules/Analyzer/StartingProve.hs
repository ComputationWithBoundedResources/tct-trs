-- StartingProve.hs ---
--
-- Filename: StartingProve.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Sun Sep 14 10:10:23 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Tue Apr 11 13:40:46 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 1572
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

-- | TODO: comment this module
module Tct.Trs.Processor.ARA.ByInferenceRules.Analyzer.StartingProve
    ( convertSig
    , convertDt
    , insertConstraints
    , updateDatatypesChildCost
    , createCtrSig
    , createInfTreeNodes
    , addConditions
    )
    where

import           Data.Rewriting.Typed.Datatype
import           Data.Rewriting.Typed.Problem
import           Data.Rewriting.Typed.Rule
import           Data.Rewriting.Typed.Signature

import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerSignature
import           Tct.Trs.Processor.ARA.ByInferenceRules.CmdLineArguments.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.HelperFunctions
import           Tct.Trs.Processor.ARA.ByInferenceRules.InferenceRules.InfRuleMisc
import           Tct.Trs.Processor.ARA.ByInferenceRules.Operator
import           Tct.Trs.Processor.ARA.ByInferenceRules.Prove
import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Type
import           Tct.Trs.Processor.ARA.Constants
import           Tct.Trs.Processor.ARA.Exception
import           Tct.Trs.Processor.ARA.Pretty

-- #ifdef DEBUG
import           Debug.Trace
                                                                                    (trace)
-- #endif

import           Control.Arrow
                                                                                    (first,
                                                                                    second,
                                                                                    (***))
import           Control.Exception
                                                                                    (throw)
import           Data.Function
                                                                                    (on)
import           Data.List
import qualified Data.Map.Strict                                                   as Map
import           Data.Maybe
import           Text.PrettyPrint
import qualified Text.PrettyPrint.ANSI.Leijen                                      as L

-- | @convertSig (Maybe sig)@ convert the signature form @(Signature String
-- String)@ to a @SignatureSig@, which is used inside of this program.
convertSig :: Maybe [Signature String String] -> Maybe [SignatureSig]
convertSig Nothing  = Nothing
convertSig (Just x) = Just $ map convertSig' x
  where convertSig' (Signature n lhs' rhs') =
          Signature (n, ACost 0, False,False) (map convertSigCh lhs') (convertSigCh rhs')
        convertSigCh str = (str, [])


-- | @convertSig (Maybe sig)@ convert the signature form @(Datatype String
-- String)@ to a @DatatypeSig@, which is used inside of this program.
convertDt :: Maybe [Datatype String String] -> Maybe [DatatypeSig]
convertDt Nothing  = Nothing
convertDt (Just x) = Just $ map convertDt' x
  where convertDt' (Datatype n ctr) = Datatype (n,[]) (map convertCtr ctr)
        convertCtr (Constructor n ch) = Constructor (n, ACost 0) (map convertCtrCh ch)
        convertCtrCh ConstructorRecursive    = ConstructorRecursive
        convertCtrCh (ConstructorDatatype n) = ConstructorDatatype (n,[])


createCtrSig    :: Prove -> Prove
createCtrSig = mapDatatypes const accessor updater createCtrSig'
 where accessor = accessorMaybe signatures . problem
       updater p x =
         -- trace ("oldSigs: " ++ show (signatures (problem p)))
         -- trace ("newSigs: " ++ show (p { problem = (problem p)
         --                 { signatures = if null x
         --                                then Nothing
         --                                else Just x }}))

         p { problem = (problem p)
                         { signatures = if null x
                                        then Nothing
                                        else Just x }}


createCtrSig' :: (DatatypeSig, [SignatureSig]) -> (DatatypeSig, [SignatureSig])
createCtrSig' x@(Datatype dt ctrs, acc) =
  -- trace ("datatypes dt ctrs, acc: " ++ show x)
  -- trace ("nSig: " ++ show nSig)

  (undefined, acc ++ nSig)
  where nSig :: [SignatureSig]
        nSig = map (createSigFromCtr dt) ctrs

        createSigFromCtr :: (String, [ACost Int]) -> ConstructorSig -> SignatureSig
        createSigFromCtr rhs' (Constructor (n,_) ch) =
          Signature (n,ACost 0,True,False) (map (createLhs rhs') ch) rhs'

        createLhs :: (String, [ACost Int]) -> ConstructorChildSig -> (String, [ACost Int])
        createLhs rhs' ConstructorRecursive   = rhs'
        createLhs _ (ConstructorDatatype dt') = dt'


insertConstraints :: ArgumentOptions -> Prove -> Prove
insertConstraints args pr =
  mapProveAsB rulesWeak const accessor updater (fun True) $
  mapProveAsB rulesStrict const accessor updater (fun False) pr

  where dts = fromMaybe [] ((datatypes . problem) pr)
        sigs = fromMaybe [] ((signatures . problem) pr)
        rulesStrict pr' = (strictRules . rules) (problem pr')
        rulesWeak pr' = (weakRules . rules) (problem pr')

        accessor pr' = (infTreeNodesToProve pr', signatureMap pr'
                       , conditions pr', lhsArgDefSyms pr')
        updater pr' (n, s, c, noCf) = pr' { signatureMap = s
                                          , infTreeNodesToProve = n
                                          , conditions = c
                                          , lhsArgDefSyms = noCf
                                    }

        rls = (allRules . rules) (problem pr)
        fun = createInfTreeNodes (Left rls) False Nothing args dts sigs


updateDatatypesChildCost :: Prove -> Prove
updateDatatypesChildCost p = p { problem = prob {datatypes = res }}
  where fun = updateDatatypeChildCost sigs
        sigs = fromMaybe [] (signatures prob)
        prob = problem p
        res = if isNothing (datatypes prob) || null (fromJust (datatypes prob))
                then Nothing
                else Just (map fun (fromJust $ datatypes prob))


updateDatatypeChildCost :: [SignatureSig] -> DatatypeSig -> DatatypeSig
updateDatatypeChildCost sigs (Datatype dt ctrs) = Datatype dt (map updateCtr ctrs)
  where updateCtr (Constructor cn chld) =
          Constructor cn (map (updateCtrChld (fst cn)) (zip [0..] chld))
        updateCtrChld _ (_,ConstructorRecursive)       = ConstructorRecursive
        updateCtrChld cn (nr,ConstructorDatatype (dt',_)) =
          let sig = lhsSig $ getSignatureByNameAndType' sigs cn dt'
          in ConstructorDatatype (dt',snd (sig !! nr))


postInfTreeNode :: Bool
                -> Int
                -> Rule String String
                -> String
                -> Maybe (Term String String, ADatatype Int)
postInfTreeNode isCf nr (Rule _ term) dt = Just (term, sigRefRet isCf dt nr)


-- | @createConstraints (rule, ctxs)@ creates a starting constraint from the given
-- problem and saves it to the tuple. The returning rule is undefined due to not
-- using it in mapDatatypes.
createInfTreeNodes :: Either [Rule String String] Int
                   -> Bool
                   -> Maybe Int
                   -> ArgumentOptions
                   -> [DatatypeSig]
                   -> [SignatureSig]
                   -> Bool
                   -> (Rule String String, ([InfTreeNode], ASigs, ACondition Int Int, [String]))
                   -> (Rule String String, ([InfTreeNode], ASigs, ACondition Int Int, [String]))
createInfTreeNodes rlsGrpNr isCf mSigIdx args dts sigs weak
  (rule, (nodes, aSigs, conds, noCfDefSyms)) =
  -- trace ("aSigs': " ++ unlines (map (show . prettyAraSignature') aSigs'))
  -- trace ("pre: " ++ show pre)
  -- trace ("condsCtr: " ++ show condsCtr)
  -- trace ("csts: " ++ show csts)
  -- trace ("isCf: " ++ show isCf)
  -- trace ("chInfTreeNodes: " ++ show chInfTreeNodes)
  -- trace ("rule: " ++ show rule) $
  -- trace ("pre: " ++ show pre)
  -- trace ("isLeftLinear: " ++ show isLeftLinear)
  -- undefined

  (undefined,
   (nodes ++ [InfTreeNode
              preLinear
              csts
              (postInfTreeNode isCf aSigNr rule dt)
              (fn, ruleStr, False, csts, aSigNr,Nothing)
              []
             ] ++ chInfTreeNodes
  , aSigs'
  , conds'
  , noCfDefSyms ++ noCfDefSyms'
  ))

  where fn = (\(Fun f _) -> f) (lhs rule)
        ch = (\(Fun _ ch') -> ch') (lhs rule)


        -- isLeftLinear = all ((==1) . length) (group $ sort $ map fst pre)

        (preLinear,shareConds) =
          first reverse $
          foldl mergeMultiple ([],[]) (groupBy ((==) `on` fst) $
                                       sortBy (compare `on` fst) pre)
          where mergeMultiple (preLin, shares) [x] = (x:preLin,shares)
                mergeMultiple (preLin, shares) xs@(x:rest)
                  | any (/= getDt (snd x)) (map (getDt.snd) rest) =
                    throw $ FatalException $
                    "Non-linear lhs over different types are not allowed: " ++
                    show (fst x) ++ " of types " ++ show (map snd xs)
                  | otherwise =
                  let varName = "ipvar_ll_sigIdx" ++ show aSigNr ++ "_" ++ fst x ++
                        if isCf then "_cf" else ""
                      var = SigRefVar (getDt (snd x)) varName
                      list = map snd xs
                      shareCond = (var, Eq, list)
                      -- shareCond = (list, Eq, [var])
                  in ((fst x, var):preLin, shareCond:shares)

        ruleStr = show (prettyRule
                        (L.pretty (L.text $ if weak
                                            then "->="
                                            else "->")) L.pretty L.pretty rule)

        aSigNr | isJust mSigIdx = fromJust mSigIdx
               | otherwise = length aSigs

        startCtrSigNr | isJust mSigIdx = length aSigs
                      | otherwise = length aSigs + 1

        sig = getDefSymSignatureByName' sigs fn
        dt = fst (rhsSig sig)
        aSig = (sig2ASig isCf args sig, fromRuleOrGrpNr, "createInfTreeNodes")

        fromRuleOrGrpNr = case rlsGrpNr of
          Left rls -> snd $ fromJust $ find ((== rule) . fst) (zip rls [1..])
          Right nr -> nr

        chInfTreeNodes = map (\(InfTreeNode _ a b c d) ->
                                InfTreeNode pre a b c d) chInfTreeNds

        pre :: [(String, ADatatype Int)]
        aSigsCtr :: ASigs
        condsCtr :: ACondition Int Int
        (pre,aSigsCtr,condsCtr,kis,chInfTreeNds,noCfDefSyms',_) =
          foldl (getVarsWithDt ruleStr fromRuleOrGrpNr True isCf args sigs)
          ([],[],ACondition [] [] [],[],[],[],startCtrSigNr)
          (zip3 ch params dts)
        params = map (\(a,b) -> sigRefParam isCf a aSigNr b) (zip dts [0..])
        dts = map fst (lhsSig sig)


        aSigs' = aSigs ++ [ aSig | isNothing mSigIdx ] ++ aSigsCtr
        conds' = conds { shareConditions = shareConditions conds ++ shareConds}
                 `addConditions` condsCtr
        -- conds' = conds { dtConditions = dtConditions conds ++ shareConds}
        --          `addConditions` condsCtr
        csts = sigRefCst isCf aSigNr : [ACostValue (-1) | not weak] ++ kis


getVarsWithDt :: String
              -> Int
              -> Bool
              -> Bool
              -> ArgumentOptions
              -> [SignatureSig]
              -> ([(String, ADatatype Int)], ASigs,ACondition Int Int
                 , [ACostCondition Int],[InfTreeNode], [String], Int)
              -> (Term String String, ADatatype Int, String)
              -> ([(String, ADatatype Int)], ASigs,ACondition Int Int
                , [ACostCondition Int],[InfTreeNode], [String], Int)
getVarsWithDt _ _ _ _ _ _ (accPre,accSigs,accConds,csts,infTreeNds,noCfDefSyms,sigNr) (Var v, dtN, dt) =
  (accPre ++ [(v, dtN)], accSigs,accConds,csts,infTreeNds,noCfDefSyms,sigNr)
getVarsWithDt ruleStr ruleGrpNr isRoot isCf args sigs
  (accPre,accSigs,accConds,csts,infTreeNds,noCfDefSyms,sigNr) (Fun f ch,dtN,dt) =
  foldl
  (getVarsWithDt ruleStr ruleGrpNr False isCf args sigs)
  (accPre, accSigs `mappend` [aSig],accConds `addConditions` nConds,csts++nCsts,
    take (length infTreeNds-1) infTreeNds++nInfTreeNds,
    noCfDefSyms ++ [f | not (isCtr sig)],sigNr+1)
  (zip3 ch dt' dts)

          where dt' = map (\(a,b) -> sigRefParam isCf a sigNr b) (zip dts [0..])
                sig = getSignatureByNameAndType' sigs f dt
                isCtr (Signature (_,_,c,_) _ _) = c
                dts = map fst (lhsSig sig)
                aSig = (sig2ASig isCf args sig, ruleGrpNr, "getVarsWithDt")
                nConds = ACondition [] [([dtN], Eq, [sigRefRet isCf dt sigNr])] []
                nCsts = [sigRefCst isCf sigNr | isRoot]
                nInfTreeNds =
                  [InfTreeNode
                    undefined -- need to be replaced after collecting them (which
                    -- must happen in the calling function)
                    [sigRefCst isCf sigNr]
                    (Just (Fun f ch, dtN))
                    (f,ruleStr, True,[sigRefCst isCf sigNr], sigNr,Nothing)
                    [] | isRoot ]
                addCosts csts' (InfTreeNode _ csts t i x) =
                  InfTreeNode undefined (csts++csts') t i x
                curInfTreeNode = last infTreeNds


addConditions :: ACondition a b -> ACondition a b -> ACondition a b
addConditions conds condsNew =
  ACondition
  (costCondition conds ++ costCondition condsNew)
  (dtConditions conds ++ dtConditions condsNew)
  (shareConditions conds ++ shareConditions condsNew)


--
-- StartingProve.hs ends here


