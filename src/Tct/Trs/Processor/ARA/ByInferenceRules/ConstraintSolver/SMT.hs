{-# LANGUAGE OverloadedStrings #-}
-- SMT.hs ---
--
-- Filename: SMT.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Sat May 21 13:53:19 2016 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sun Apr  9 17:27:31 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 1470
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

module Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.SMT
    ( solveProblem
    ) where


import           Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.Heuristic
import           Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.Inserts
import           Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.SMT.ConvertSolutionToData
import           Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.SMT.ConvertToSMTProblem
import           Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.SMT.IO
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


import           Control.Arrow                                                                     hiding
                                                                                                    ((+++))
import           Control.Exception
import           Control.Lens                                                                      hiding
                                                                                                    (use)
import           Control.Monad
import qualified Control.Monad.Parallel                                                            as Par
import           Control.Monad.State
import           Control.Parallel.Strategies
import           Data.Function
                                                                                                    (on)

import           Data.List
import qualified Data.Map.Strict                                                                   as M
import           Data.Maybe
                                                                                                    (fromJust,
                                                                                                    fromMaybe,
                                                                                                    isJust,
                                                                                                    isNothing)
import qualified Data.Set                                                                          as S

import qualified Data.Text                                                                         as T
import           Debug.Trace
import           Text.PrettyPrint                                                                  hiding
                                                                                                    (empty)


use :: SMTProblem
use = z3

z3 :: SMTProblem
z3 = emptySMTProblem "z3" ["-smt2"]

emptySMTProblem :: T.Text -> [T.Text] -> SMTProblem
emptySMTProblem name args = SMTProblem S.empty [] [] [] M.empty name args undefined


solveProblem :: ArgumentOptions
             -> [SignatureSig]
             -> ACondition Int Int
             -> ASigs
             -> CfSigs
             -> IO ([ASignatureSig], [ASignatureSig], [Data Int], [Data Vector]
                  , [ASignatureSig], [ASignatureSig], Int)
solveProblem ops probSigs conds aSigs cfSigs = do

  let maxNrVec = maxVectorLength ops
  let minNrVec = minVectorLength ops
  let eqZero = concatMap constantToZero
               (zip [0..] (map fst3 aSigs) ++ zip [0..] (map fst3 cfSigs))
  let prob0 = execState (addEqZeroConstraints eqZero) use
  let vecLens = [minNrVec..maxNrVec]
  when (maxNrVec < 1 || maxNrVec > maximumVectorLength)
    (throw $ FatalException $
     "vector length must be in [1.." ++ show maximumVectorLength ++ "]")
  let catcher :: IOError -> IO (Either String b)
      catcher e = return (Left (show e))

  let sols = parMap rpar
        (\nr -> handle catcher (Right <$>
                               evalStateT (solveProblem' ops probSigs conds aSigs cfSigs nr)
                               prob0)) vecLens

  let getSol :: [IO (Either String a)] -> IO a
      getSol (xIO:xs) = do
        x <- xIO
        case x of
          Left x -> if null xs
                    then throw $ UnsolveableException x
                    else getSol xs
          Right sol -> return sol

  getSol sols

baseCtrSigDefFun f x y = fst4 (lhsRootSym x) `f` fst4 (lhsRootSym y) &&
                         getDt (rhsSig x) `f` getDt (rhsSig y)


solveProblem' :: (Show a, Show a1) =>
                ArgumentOptions
              -> [SignatureSig]
              -> ACondition a1 a
              -> ASigs
              -> CfSigs
              -> Int
              -> StateT SMTProblem IO ([ASignatureSig]
                                     , [ASignatureSig]
                                     , [Data Int]
                                     , [Data Vector]
                                     , [ASignatureSig]
                                     , [ASignatureSig]
                                     , Int)
solveProblem' ops probSigs conds aSigsTxt cfSigsTxt vecLen = do

  let aSigs = map fst3 aSigsTxt
  let cfSigs = map fst3 cfSigsTxt


  -- add constraints with specified length
  addCostConditions vecLen (costCondition conds)
  addDtConditions vecLen (dtConditions conds)
  addShareConditions vecLen (shareConditions conds)

  unless (shift ops) $ do
    -- multiplication-constraints (ctr must be linear combination of base ctr)
    let mConstr = concatMap (toMConstraints ops probSigs) (zip [0..] aSigs ++ zip [0..] cfSigs)
    addMultConstraints vecLen mConstr

    -- bound growth of constructors
    let growthConstraints =
          concatMap (toGrowBoundConstraints ops) (zip [0..] aSigs ++ zip [0..] cfSigs)
    let constr =
          nubBy (baseCtrSigDefFun (==)) $
          filter (thd4 . lhsRootSym) (aSigs++cfSigs)
    let growthConstraintsBaseCtr =
          concatMap (toGrowBoundConstraintsBaseCtr ops probSigs vecLen) constr

    -- needed because addition of base ctr can cause problems
    addConstructorGrowthConstraints vecLen growthConstraints
    addConstructorGrowthConstraints vecLen growthConstraintsBaseCtr

    -- independence constraints:
    -- let indepConstr = concatMap (independencyBaseConstr ops vecLen) constr
    -- addIndependenceBaseCtrConstraints vecLen indepConstr -- !!!
    -- let constrDt = concatMap (baseConstructors ops vecLen) constr
    -- addIndependenceConstraints vecLen constrDt -- !!!


    let baseCtrs = map (\x -> (convertToSMTStringText (fst4 (lhsRootSym x))
                              , thd4 (lhsRootSym x)
                              , length (lhsSig x)
                              , getDt (rhsSig x))) constr
    setBaseCtrMaxValues ops probSigs vecLen baseCtrs

  when (shift ops) $ do

    let ctrSigs = filter (thd4 . lhsRootSym) probSigs
    let isRecursive x = let rhsDt = fst (rhsSig x)
                            lhsDts = map fst (lhsSig x)
                        in rhsDt `elem` lhsDts
    let isConstant = null . lhsSig
    let recCtrSigs = filter isRecursive ctrSigs
    let nonRecCtrSigs = filter (not . isRecursive) ctrSigs

    let shiftConstr = concatMap (shiftConstraints recCtrSigs nonRecCtrSigs)
                      (zip [0..] aSigs ++ zip [0..] cfSigs)
    addHeuristics vecLen shiftConstr


  -- set cf groups to ==0 or >0
  let (grpsDt,_) = foldl (groupVars variablesCfDt) ([],-1) (zip [0..] cfSigsTxt)
  let (grpsCst,_) = foldl (groupVars variablesCfCst) ([],-1) (zip [0..] cfSigsTxt)
  let grps = combineGroupVars grpsDt grpsCst
  addCfGroupsConstraints vecLen grps

  let tempDir = tempFilePath ops
  let kf = keepFiles ops
  let shft = shift ops

  sol <- solveSMTProblem shft kf tempDir

  let sortAndGroup = groupBy (baseCtrSigDefFun (==)) .
                     sortBy (\x y -> mconcat
                              [ fst4 (lhsRootSym x) `compare` fst4 (lhsRootSym y)
                              , getDt (rhsSig x) `compare` getDt (rhsSig y)])


  let (solVarsNs, solVars) = convertToData vecLen sol
      ctrSigs = map head $ sortAndGroup $
                filter (thd4 . lhsRootSym) aSigs
      cfCtrSigs =
        if any (\x -> "rctr" `isInfixOf` x && "_cf_" `isInfixOf` x) (M.keys sol)
        then map head $ sortAndGroup $
             filter (thd4 . lhsRootSym) cfSigs
        else []

  return ( insertIntoSigs aSigs solVars
         , insertIntoSigs cfSigs solVars
         , solVarsNs
         , solVars
         , insertIntoSigsCtr ops probSigs vecLen ctrSigs solVars
         , insertIntoSigsCtr ops probSigs vecLen cfCtrSigs solVars
         , vecLen)


constantToZero :: (Int, Signature (t1, t2, Bool,Bool) t) -> [ACostCondition Int]
constantToZero (nr, Signature (n,_,True,False) [] rhs) = [SigRefCst nr]
constantToZero (nr, Signature (n,_,True,True) [] rhs)  = [SigRefCstCf nr]
constantToZero _                                       = []

uniqueBaseCtr :: Int
              -> ASignatureSig
              -> [((ADatatype Vector, ADatatype Vector)
                 , [(ADatatype Vector, ADatatype Vector)]
                 , [(ACostCondition Vector, ACostCondition Vector)])]
uniqueBaseCtr vecLen (Signature (n,_,_,_) lhs _) =
  map (\(x,y) ->
         (( SigRefVar undefined $ "rctr_" ++ convertToSMTString n ++ "_" ++ show x
          , SigRefVar undefined $ "rctr_" ++ convertToSMTString n ++ "_" ++ show y)
         , map (\pNr ->
                  (SigRefVar undefined $ "pctr_" ++ convertToSMTString n ++
                    "_" ++ show pNr ++ "_" ++ show x
                  , SigRefVar undefined $ "pctr_" ++ convertToSMTString n ++
                    "_" ++ show pNr ++ "_" ++ show y)) [0..length lhs -1]
         , [(AVariableCondition $ "kctr_" ++ convertToSMTString n ++ "_" ++ show x
            ,AVariableCondition $ "kctr_" ++ convertToSMTString n ++ "_" ++ show y)]
         )

      ) (tuples [1..vecLen]) -- over tuples of all base constructors


uniqueSigConstr :: Bool
                -> Bool
                -> [ASignatureSig]
                -> (Int, Int)
                -> [((ADatatype Vector, ADatatype Vector)
                  , [(ADatatype Vector, ADatatype Vector)]
                  , [(ACostCondition Vector, ACostCondition Vector)])]
uniqueSigConstr isCf uniqueFunConstr sigs (l, r) =
  [((sigRefRet isCf "" l,
     sigRefRet isCf "" r)
  , zipWith (\a _ -> (sigRefParam isCf "" l a, sigRefParam isCf "" r a)) [0..] (lhsSig lSig)
  , [(sigRefCst isCf l, sigRefCst isCf r)])
  | uniqueFunConstr
  ]

  where lSig = sigs !! l
        rSig = sigs !! r
        lIsCtr = (thd4 . lhsRootSym) lSig
        rIsCtr = (thd4 . lhsRootSym) rSig


uniqueSignaturesConstr :: [(Int, ASignatureSig)]
                       -> [(Int, Int)]
uniqueSignaturesConstr sigs =
  concatMap (tuples . map fst) (groupsCSnd sigs)
  where groupsCSnd sig =
          groupBy (equalsFunConstr `on` snd) $ sortBy (compareFun `on` snd) sig

equalsFunConstr :: (Eq a1, Eq a) =>
                  Signature (a, t, t1,d) a1
                -> Signature (a, t2, t3,d) a1
                -> Bool
equalsFunConstr (Signature (n1,_,_,_) _ rhs1 ) (Signature (n2,_,_,_) _ rhs2 )  =
  n1 == n2 && rhs1 == rhs2

compareFun :: (Ord a1, Ord a) =>
             Signature (a, t, t1,d) a1
           -> Signature (a, t2,t3,d) a1
           -> Ordering
compareFun (Signature (n1,_,_,_) _ rhs1 ) (Signature (n2,_,_,_) _ rhs2)  =
  case compare n1 n2 of
    EQ -> compare rhs1 rhs2
    LT -> LT
    GT -> GT


shiftConstraints :: [Signature (String,ACost Int,Bool,Bool) (String, [ACost Int])]
                 -> [Signature (String,ACost Int,Bool,Bool) (String, [ACost Int])]
                 -> (Int, ASignatureSig)
                 -> [([(ADatatype Int, Heuristic (ADatatype Int))],
                      (ACostCondition Int, Heuristic (ADatatype Int)))]
shiftConstraints recCtrs nonRecCtrs (nr, Signature (n,_,False,isCf) _ _) = []
shiftConstraints recCtrs nonRecCtrs (nr, Signature (n,_,_,isCf) [] _) = []
shiftConstraints recCtrs nonRecCtrs sig@(nr, Signature (n,_,True,isCf) lhs rhs)
  | null (lhsSig (snd sig)) = []
  | forceInterl && length lhsDts < 2 =
      throw $ FatalException "Not enough parameter types for interleaving!"
  | length lhsCount == 1 =
    [(zipWith (curry toShiftPar) [0..] lhsBools,
                             (sigRefCst isCf nr, Diamond (sigRefRet isCf "" nr)))]
  | otherwise =                 -- take the first to recursive occurrences for
                                -- interleaving
      [([(sigRefRet isCf "" nr, Interleaving (sigRefParam isCf "" nr (head lhsNrs2))
        (sigRefParam isCf "" nr (head (tail lhsNrs2))))], (sigRefCst isCf nr, Zero))]
  where ctrSig = fromJust $ find ((==n) . fst4 . lhsRootSym) (recCtrs ++ nonRecCtrs)
        rhsDt = fst (rhsSig ctrSig)
        lhsDts = map fst (lhsSig ctrSig)
        lhsBools = map (== rhsDt) lhsDts
        lhsCount = filter id lhsBools
        lhsNrs = map fst $ filter snd $ zip [0..] lhsBools
        lhsNrs2
          | forceInterl = [0,1] -- take the first two
          | otherwise = take 2 lhsNrs
        toShiftPar (parNr, isRec)
          | isRec = (sigRefParam isCf "" nr parNr, Shift (sigRefRet isCf "" nr))
          | otherwise = (sigRefParam isCf "" nr parNr, Zero)
        forceInterl = ctrSig `elem` nonRecCtrs


tuples :: [t] -> [(t, t)]
tuples []     = []
tuples [_]    = []
tuples (x:xs) = [(x, b) | b <- xs] ++ tuples xs


toMConstraints :: (Show t, Show a) => ArgumentOptions
               -> [SignatureSig]
               -> (Int, Signature (String, t, Bool,Bool) (ADatatype a))
               -> [((ACostCondition Int, T.Text, ACostCondition Int)
                   ,[(ADatatype Int, T.Text, ADatatype Int)])]
toMConstraints _ sigs (_, Signature (n,_,False,_) _ _)   = []
toMConstraints args sigs (nr, Signature (n,_,True,isCf) lhs rhs) =
  [((sigRefCst isCf nr, T.pack ns,
     AVariableCondition $ "kctr_" ++ baseCf ++ convertToSMTString n)
   , zip3
     (sigRefRet isCf "" nr : map (sigRefParam isCf "" nr) [0..length lhs-1])
     (repeat $ T.pack ns)
     ([SigRefVar undefined $ "rctr_" ++ baseCf ++ convertToSMTString n] ++
      map (\lhsNr ->
             SigRefVar undefined $ "pctr_" ++ baseCf ++ convertToSMTString n ++ "_" ++ show lhsNr)
      [0..length lhs-1])
   )]

  where ctrType = getDt rhs
        baseCf = if isCf && separateBaseCtr args then ctrType ++ "_cf_" else ctrType ++ "_"
        cf = if isCf then "cf_" else ""
        ns = "n" ++ cf ++ show nr

-- To bound growth of constructors potentials
toGrowBoundConstraints :: ArgumentOptions
                       -> (Int, Signature (String, t, Bool,Bool) a4)
                       -> [(T.Text, ADatatype Int, Int, ADatatype Int,
                            ACostCondition Int, ADatatype Int)]
toGrowBoundConstraints args (_, Signature (_,_,False,_) _ _) = []
toGrowBoundConstraints args (nr, Signature (n,p,True,isCf) lhs _) =
    map (\y ->
           ( T.pack cf +++ T.pack (show nr)
           , sigRefParam isCf "" nr y
           , y
           , SigRefVar undefined $ "rictr_" ++ cf ++ show nr ++ "_" ++ show y ++
             "_" ++ convertToSMTString n
           , sigRefCst isCf nr
           , sigRefRet isCf "" nr)
        ) [0..length lhs-1]

  where cf = if isCf then "cf_" else ""


-- Base constructor looks like: [pctr_l_0 x pctr_l_1] -kctr_l-> rctr_l
-- Output quadruple: (p(3,0),rictr_3_0_s,k(3),r(3))
toGrowBoundConstraintsBaseCtr :: ArgumentOptions
                              -> [SignatureSig]
                              -> Int
                              -> Signature (String, t, Bool,Bool) (ADatatype a)
                              -> [(T.Text, ADatatype Int, Int, ADatatype Int,
                                  ACostCondition Int, ADatatype Int)]
toGrowBoundConstraintsBaseCtr args sigs vecLen (Signature (n,_,_,isCf) lhs rhs)
  | isCf && not (separateBaseCtr args) = []
  | otherwise =
    concatMap (\v ->
         map (\y ->
                ( convertToSMTStringText $ n ++ "_basectr" ++ cf ++ show v
                , SigRefVar undefined $ "pctr_" ++ baseCf ++ convertToSMTString n ++
                  "_" ++ show y ++ "_" ++ show v
                , y
                , SigRefVar undefined $ "rictr_base_" ++ cf ++ convertToSMTString n
                  ++ "_" ++ show y ++ "_" ++ show v
                , AVariableCondition $ "kctr_" ++ baseCf ++ convertToSMTString n
                  ++ "_" ++ show v
                , SigRefVar undefined $ "rctr_" ++ baseCf ++ convertToSMTString n ++
                  "_" ++ show v)
             ) [0..length lhs-1]
      ) [1..vecLen]
  where cf = if isCf then "cf_" else ""
        ctrType = getDt rhs
        baseCf = if isCf && separateBaseCtr args then ctrType ++ "_cf_" else ctrType ++ "_"

independencyBaseConstr :: ArgumentOptions
                       -> [SignatureSig]
                       -> Int
                       -> Signature (String, t, Bool,Bool) (ADatatype a)
                       -> [(String,
                           String,
                           String,
                           String,
                           ADatatype Int,
                           ADatatype Int,
                           ACostCondition Int,
                           ACostCondition Int,
                           [ADatatype Int],
                           [ADatatype Int])]
independencyBaseConstr args sigs vecLen (Signature (n,_,_,isCf) lhs rhs)
  | isCf && not (separateBaseCtr args) = []
  | otherwise =
      map (\(x,y) ->
         let varXName1 = "ipvar_indep_" ++ cf ++ convertToSMTString n ++ "_" ++ show x ++
                         "_" ++ show y ++ "_X1"
             varXName2 = "ipvar_indep_" ++ cf ++ convertToSMTString n ++ "_" ++ show x ++
                         "_" ++ show y ++ "_X2"
             varYName1 = "ipvar_indep_" ++ cf ++ convertToSMTString n ++ "_" ++ show x ++
                         "_" ++ show y ++ "_Y1"
             varYName2 = "ipvar_indep_" ++ cf ++ convertToSMTString n ++ "_" ++ show x ++
                         "_" ++ show y ++ "_Y2"
         in ( varXName1, varXName2
            , varYName1, varYName2
            , SigRefVar undefined $ "rctr_" ++ baseCf ++ convertToSMTString n ++ "_" ++ show x
            , SigRefVar undefined $ "rctr_" ++ baseCf ++ convertToSMTString n ++ "_" ++ show y
            , AVariableCondition $ "kctr_" ++ baseCf ++ convertToSMTString n ++ "_" ++ show x
            , AVariableCondition $ "kctr_" ++ baseCf ++ convertToSMTString n ++ "_" ++ show y
            , map (\pNr ->
                     SigRefVar undefined $ "pctr_" ++ baseCf ++ convertToSMTString n ++
                    "_" ++ show pNr ++ "_" ++ show x) [0..length lhs -1]
            , map (\pNr ->
                     SigRefVar undefined $ "pctr_" ++ baseCf ++ convertToSMTString n ++
                    "_" ++ show pNr ++ "_" ++ show y) [0..length lhs -1]
            )


      ) (tuples [1..vecLen]) -- over tuples of all base constructors
  where cf = if isCf then "cf_" else ""
        ctrType = getDt rhs
        baseCf = if isCf && separateBaseCtr args then ctrType ++ "_cf_" else ctrType ++ "_"

baseConstructors :: ArgumentOptions
                 -> [SignatureSig]
                 -> Int
                 -> Signature (String, t, s,Bool) (ADatatype a)
                 -> [(Int, ADatatype Int)]
baseConstructors args sigs vecLen (Signature (n,_,_,isCf) _ rhs)
  | isCf && not (separateBaseCtr args) = []
  | otherwise =
      map (\nr ->
         (nr, SigRefVar undefined $ "rctr_" ++ baseCf ++ convertToSMTString n ++ "_" ++ show nr)
        ) [1..vecLen] -- over all base constructors
  where cf = if isCf then "cf_" else ""
        ctrType = getDt rhs
        baseCf = if isCf && separateBaseCtr args then ctrType ++ "_cf_" else ctrType ++ "_"

combineGroupVars :: [([ADatatype Int],[ADatatype Int])]
                 -> [([ACostCondition Int],[ACostCondition Int])]
                 -> [([ADatatype Int],[ACostCondition Int],
                       [ADatatype Int],[ACostCondition Int])]
combineGroupVars = zipWith (\(dtMain, dtRest) (cstMain, cstRest) ->
                              (dtMain, cstMain, dtRest, cstRest))


groupVars :: ((Int, CfSig) -> [varType])
          -> ([([varType],[varType])],Int)
          -> (Int, CfSig)
          -> ([([varType],[varType])],Int)
groupVars f ([],lastNr) sig@(sigNr,cfSig) = ([(f sig,[])],snd3 cfSig)
groupVars f (hd@(main,acc):accs,lastNr) sig@(sigNr,cfSig)
  | lastNr == snd3 cfSig = ((main,acc ++ f sig):accs,lastNr)
  | otherwise = ((f sig,[]):hd:accs,snd3 cfSig)


variablesCfDt :: (Int, (Signature s a, t, t2)) -> [ADatatype x]
variablesCfDt (nr,(sig,_,_)) = SigRefRetCf "" nr :
                             map (SigRefParamCf "" nr) [0..length (lhsSig sig)-1]

variablesCfCst :: (Int, (Signature s a, t, t2)) -> [ACostCondition x]
variablesCfCst (nr,(sig,_,_)) = [SigRefCstCf nr]


--
-- SMT.hs ends here
