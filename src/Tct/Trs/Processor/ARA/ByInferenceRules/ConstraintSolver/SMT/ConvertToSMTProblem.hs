{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
-- ConvertToSMTProblem.hs ---
--
-- Filename: ConvertToSMTProblem.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Sun May 22 19:09:14 2016 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sun Apr  9 17:27:30 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 983
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

module Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.SMT.ConvertToSMTProblem where

import           Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.SMT.Type

import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCondition
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerSignature
import           Tct.Trs.Processor.ARA.ByInferenceRules.CmdLineArguments
import           Tct.Trs.Processor.ARA.ByInferenceRules.HelperFunctions
import           Tct.Trs.Processor.ARA.ByInferenceRules.Operator
import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Pretty
import           Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.Heuristic
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.Data.Type
import           Tct.Trs.Processor.ARA.Exception
import           Data.Rewriting.Typed.Signature


import           Control.Arrow hiding ((+++))
import           Control.Exception                                             (throw)
import           Control.Lens                                                  hiding (use)
import           Control.Monad
import           Control.Monad.State
import           Data.Function                                                 (on)
import           Data.List
import qualified Data.Text as T
import qualified Data.Map.Strict                                               as M
import qualified Data.Set as S
import           Data.Maybe                                            (fromJust,
                                                                        fromMaybe,
                                                                        isJust,
                                                                        isNothing)
import           Debug.Trace
import           Text.PrettyPrint                                      hiding
                                                                        (empty)


-- Monadic insert into state for set from list
(<>=+) :: (Ord a, MonadState SMTProblem m) =>
          ASetter' SMTProblem (S.Set a)
       -> [a]
       -> m ()
infix 4 <>=+
field <>=+ strs = field %= (\x -> foldl (flip S.insert) x strs)


addEqZeroConstraints :: (Show a, MonadState SMTProblem m) =>
                       [ACostCondition a]
                     -> m ()
addEqZeroConstraints eqZero = do
  mapM_ (addVars . fromCostCond) eqZero
  mapM_ (\x -> addConstraint (head (fromCostCond x), Eq, "0")) eqZero


addUniqueSigConstraints :: (Monad m, Show a) =>
                          Int
                        -> [((ADatatype a, ADatatype a)
                          , [(ADatatype a, ADatatype a)]
                          , [(ACostCondition a, ACostCondition a)])]
                        -> StateT SMTProblem m ()
addUniqueSigConstraints vecLen uSigConstr = do

  let tupleDt = fromADatatype vecLen *** fromADatatype vecLen
  let tupleCst = fromCostCond *** fromCostCond

  let uSig' =
        map (\(a,b,c) ->
              let (lconds, rconds) = tupleDt a
              in ( zip lconds rconds
                 , (let thenDt = map tupleDt b
                    in concatMap (uncurry zip) thenDt
                   ) ++
                   (let thenCst = map tupleCst c
                    in concatMap (uncurry zip) thenCst
                   )
                 )

            ) uSigConstr

  let vars  = concatMap (\(a,b,c) ->
                           fromADatatype vecLen (fst a) ++
                           fromADatatype vecLen (snd a) ++
                           concatMap (\(a,b) -> fromADatatype vecLen a ++
                                                fromADatatype vecLen b) b ++
                           concatMap (\(a,b) -> fromCostCond a ++
                                                fromCostCond b) c
                  ) uSigConstr

  addVars vars                  -- add variables
  ifs %= (uSig' ++)             -- add if constraints


addMultConstraints :: (Monad m) =>
                     Int
                   -> [((ACostCondition Int, T.Text, ACostCondition Int)
                      ,[(ADatatype Int, T.Text, ADatatype Int)])]
                   -> StateT SMTProblem m ()
addMultConstraints vecLen multConstr = do

  let makeAdd = T.concat . fromListBy return

  let toConstr ((l,n,r),xs) =
        (head (fromCostCond l), Eq,
                    makeAdd
                    (map (\idx ->
                            "(* " +++ n +++ "_" +++ T.pack (show idx)  +++ " " +++
                            head (fromCostCond r) +++ "_" +++ T.pack (show idx) +++ ")")
                    [1..vecLen])) :
        -- (head (fromCostCond l), Eq,
        --  "(* " ++ n ++ " " ++ head (fromCostCond r) ++ ")") :
        concatMap toConstr' xs
      toConstr' (l,n,r) =
        map (\(lhs,rhs) ->
               (lhs,Eq,
                 makeAdd $ map (\idx -> "(* " +++ n +++ "_" +++ T.pack (show idx) +++ " " +++
                                       rhs +++ "_" +++ T.pack (show idx) +++ ")") [1..vecLen]))
        $ zip (fromADatatype vecLen l) (fromADatatype vecLen r)

  let constr = concatMap toConstr multConstr
  let getVars (l,n,r) =
        fromADatatype vecLen l ++
        map (((n+++"_")+++) . T.pack . show) [1..vecLen] ++
        concatMap (\nm-> map (((nm+++"_")+++) . T.pack . show) [1..vecLen])
        (fromADatatype vecLen r)

  mapM_ (\((l,n,r),xs) ->
           addVars
           (fromCostCondM l ++
            map (((n+++"_")+++) . T.pack . show) [1..vecLen] ++
            concatMap (\nm-> map (((nm+++"_")+++) . T.pack . show) [1..vecLen]) (fromCostCondM r) ++
            concatMap getVars xs)
        ) multConstr

  -- trace ("constr: " ++ show constr) undefined

  mapM_ addConstraint constr


addShareConditions :: (Show a, Monad m) =>
                     Int
                   -> [(ADatatype a, Comparison, [ADatatype a])]
                   -> StateT SMTProblem m ()
addShareConditions vecLen shareCond = do
  mapM_ (\(a,_,c) -> addVarsBy (fromADatatype vecLen) [a]) shareCond
  mapM_ (\(a,_,c) -> addVarsBy (fromADatatype vecLen) c) shareCond
  mapM_ (addConstraintBy2 (fromADatatype vecLen)
         (fromListBy (fromADatatype vecLen))) shareCond


addDtConditions :: (Show a, Monad m) =>
                  Int
                -> [([ADatatype a], Comparison, [ADatatype a])]
                -> StateT SMTProblem m ()
addDtConditions vecLen dtCond = do
  mapM_ (\(a,_,c) -> addVarsBy (fromADatatype vecLen) (a++c)) dtCond
  mapM_ (addConstraintBy (fromListBy (fromADatatype vecLen))) dtCond


fromADatatype :: Int -> ADatatype t -> [T.Text]
fromADatatype vecLen ActualCost{} = error "not possible"
fromADatatype vecLen (SigRefParam _ m n) =
  map (\nr -> "v" +++ T.pack (show nr) +++ "_p" +++ T.pack (show m)
        +++ "_" +++ T.pack (show n)) [1..vecLen]
fromADatatype vecLen (SigRefRet _ r) =
  map (\nr -> "v" +++ T.pack (show nr) +++ "_r" +++ T.pack (show r)) [1..vecLen]
fromADatatype vecLen (SigRefParamCf _ m n) =
  map (\nr -> "v" +++ T.pack (show nr) +++ "_p_cf" +++ T.pack (show m) +++ "_"
        +++ T.pack (show n)) [1..vecLen]
fromADatatype vecLen (SigRefRetCf _ r) =
  map (\nr -> "v" +++ T.pack (show nr) +++ "_r_cf" +++ T.pack (show r)) [1..vecLen]
fromADatatype vecLen (SigRefVar _ n) =
  map (\nr -> "v" +++ T.pack (show nr) +++ "_" +++ T.pack n) [1..vecLen]

fromCostCondM :: ACostCondition t -> [T.Text]
fromCostCondM (AVariableCondition str) = [T.pack str]
fromCostCondM (SigRefCst nr) = ["k" +++ T.pack (show nr)]
fromCostCondM (SigRefCstCf nr) = ["k_cf" +++ T.pack (show nr)]
fromCostCondM (ACostValue _) = [] -- numbers like: -1

fromCostCond :: Show a => ACostCondition a -> [T.Text]
fromCostCond (AVariableCondition str) = [T.pack str]
fromCostCond (SigRefCst nr) = ["k" +++ T.pack (show nr)]
fromCostCond (SigRefCstCf nr) = ["k_cf" +++ T.pack (show nr)]
fromCostCond (ACostValue nr) = [T.pack (show nr)]


addCostConditions :: (Show a, Monad m) =>
                    Int
                  -> [([ACostCondition a], Comparison, [ACostCondition a])]
                  -> StateT SMTProblem m ()
addCostConditions vecLen costCond = do


  mapM_ (\(a,_,c) -> addVarsBy fromCostCondM a >>
                    addVarsBy fromCostCondM c) costCond -- add variables

  mapM_ (addConstraintBy (fromListBy fromCostCond)) costCond -- add constraints


addVars  :: (MonadState SMTProblem m) =>
           [T.Text]
          -> m ()
addVars = addVarsBy return

addVarsBy :: (Foldable t, MonadState SMTProblem m) =>
            (a -> [T.Text])
          -> t a
          -> m ()
addVarsBy f strs = vars <>=+ concatMap f strs


addConstraint :: MonadState SMTProblem m =>
                (T.Text, Comparison, T.Text)
              -> m ()
addConstraint = addConstraintBy return


addConstraintBy :: MonadState SMTProblem m =>
                  (t -> [T.Text])
                -> (t, Comparison, t)
                -> m ()
addConstraintBy f = addConstraintBy2 f f


addConstraintBy2 :: MonadState SMTProblem m =>
                  (t1 -> [T.Text])
                -> (t2 -> [T.Text])
                -> (t1, Comparison, t2)
                -> m ()
addConstraintBy2 f1 f2 (lhs, Eq, rhs) = do
  let lhss = f1 lhs
      rhss = f2 rhs
  let xs = zipWith (\l r -> (l, Eq, r)) lhss rhss
  assertions %= (xs ++)

addConstraintBy2 f1 f2 (lhs, Geq, rhs) = do

  let lhss = f1 lhs
      rhss = f2 rhs
  let before = T.concat (replicate (length lhss-1) "(and ")
      after = T.concat (replicate (length lhss-1) ")")

  let xs = T.concat $ zipWith (\a b -> "(>= " +++ a +++ " "  +++ b +++ ") ") lhss rhss

  let ass = before +++ xs +++ after
  assertionsStr %= (ass :)

addConstructorGrowthConstraints :: (Monad m) =>
                                  Int
                                -> [(T.Text, ADatatype Int, Int, ADatatype Int,
                                     ACostCondition Int, ADatatype Int)]
                                -> StateT SMTProblem m ()
addConstructorGrowthConstraints vecLen = mapM_ addConstructorGrowthConstraints'
  where addConstructorGrowthConstraints' :: (Monad m) =>
                                           (T.Text, ADatatype Int, Int, ADatatype Int,
                                            ACostCondition Int, ADatatype Int)
                                         -> StateT SMTProblem m ()
        addConstructorGrowthConstraints' (name,ui,uiNr,ri,p,w) = do

          let uis = fromADatatype vecLen ui
          let ris = fromADatatype (vecLen-1) ri ++ ["0"]
          let ks =  fromCostCond p
          let ws = fromADatatype vecLen w
          let baseVarI = "ipvar_th32_" +++ name +++ "_" +++ T.pack (show uiNr) +++ "_"

          let mkLengthConstr nr =
                "(or " +++ "(= 0 " +++ ris !! nr +++ ") " +++
                T.concat (fromListByFun "(or "  (\x -> ["(> " +++ x +++ " 0)"])
                        (drop (nr+1) ws))
                +++ ")"
          let lengthConstr = map mkLengthConstr [0..vecLen-2]
          -- trace ("lengthConstr:\n" ++ unlines lengthConstr) $
          assertionsStr %= (lengthConstr ++)


          let wRiVars :: [T.Text]
              wRiVars = fromADatatype vecLen $
                SigRefVar undefined (T.unpack $ baseVarI +++ "wri")

          let wRiConstr =
                map (\(v,w,r) -> "(= " +++ v +++ " (+ " +++ w +++ " " +++ r +++ "))" )
                (zip3 wRiVars ws ris)

          -- save sum w + ri in new vector
          -- trace ("w + ri: " ++ show wRiConstr)
          assertionsStr %= (wRiConstr ++)

          -- ensure w+ri >= ui
          -- trace ("w+ri >= ui: " ++ show (wRiVars,Geq,uis))
          addConstraintBy id (wRiVars,Geq,uis)


          let wsMaxFun = fromListByFun "(max " return ws
              wsMaxV = baseVarI +++ "wsmax"
              wsMaxConstr = "(= " +++ wsMaxV +++ " " +++ T.concat wsMaxFun +++ ")"
          let riMaxFun = fromListByFun "(max " return ris
              riMaxV = baseVarI +++ "rimax"
              riMaxConstr = "(= " +++ riMaxV +++ " " +++ T.concat riMaxFun +++ ")"

          -- fetch the maximum
          -- trace ("wsMaxConstr: " ++ show wsMaxConstr)
          assertionsStr %= (wsMaxConstr :)
          -- trace ("riMaxConstr: " ++ show riMaxConstr)
          assertionsStr %= (riMaxConstr :)

          -- ensure max w >= max ri
          -- trace ("w>=max ri: " ++ show (wsMaxV, Geq, riMaxV))
          addConstraint (wsMaxV, Geq, riMaxV)

          -- ensure max w >= p
          -- trace ("w >= p: " ++ show (wsMaxV, Geq, head ks))
          addConstraint (wsMaxV, Geq, head ks)


          -- add variables
          let newVars = take (length ris-1) ris ++ wRiVars ++ [wsMaxV, riMaxV]
          vars <>=+ newVars

addIndependenceConstraints :: (Monad m) =>
                             Int
                           -> [(Int, ADatatype Int)]
                           -> StateT SMTProblem m ()
addIndependenceConstraints vecLen = mapM_ addIndependenceConstraints'
  where addIndependenceConstraints' (nr, rDt) = do
          let rs = fromADatatype vecLen rDt
          let rsDel = delete (rs!!(nr-1)) rs
          let zero x = "(>= 0 " +++ x +++ ") "
          let andList = T.concat . fromListByFun "(and " return
          let rsZero = andList (map zero rsDel)
          unless (T.null rsZero)
            (assertionsStr %= (rsZero :))
          -- -- trace ("rs: " ++ show rsZero)

addHeuristics :: (Monad m) =>
                 Int
              -> [([(ADatatype Int, Heuristic (ADatatype Int))],
                   (ACostCondition Int, Heuristic (ADatatype Int)))]
              -> StateT SMTProblem m ()
addHeuristics vecLen = mapM_ addHeuristics'
  where addHeuristics' (dtHeuristics, cstHeuristic) = do
          mapM_ addDtHeuristics dtHeuristics
          addCstHeuristics cstHeuristic
        addDtHeuristics (this, other) =
          let lhsVec = fromADatatype vecLen this
              rhsVec = fmap (fromADatatype vecLen) other
          in addHeur (lhsVec, rhsVec)
        addCstHeuristics (this, other) =
          let lhsVec = fromCostCond this
              rhsVec = fmap (fromADatatype vecLen) other
          in addHeur (lhsVec, rhsVec)

        addHeur (this, Shift other) = do
          assertions <>= map (\(t,p1,p2) -> (t, Eq,"(+ " +++ p1 +++ " " +++ p2 +++ ")" ))
                         (zip3 this other (tail other ++ ["0"]))
          vars <>=+ concatMap (\(t,p1,p2) -> [t,p1,p2]) (zip3 this other other)
        addHeur (this, Diamond other) = do
          assertions <>= [(head this, Eq, head other)]
          vars <>=+ [head this, head other]
        addHeur (this, Interleaving other1 other2) = do
          let fun (acc,p1,p2) t
                | length p1 + length p2 <= vecLen =
                  (acc ++ [(head p1, Eq, "0"), (head p2,Eq,"0")], tail p1, tail p2)
                | length p1 >= length p2 = (acc ++ [(t, Eq, head p1)],tail p1,p2)
                | otherwise = (acc ++ [(t, Eq, head p2)],p1,tail p2)
          assertions <>= fst3 (foldl fun ([],other1,other2) this)
          vars <>=+ other1 ++ other2 ++ this
        addHeur (this, Zero) = do
          assertions <>= map (\x -> (x, Eq, "0")) this
          vars <>=+ this


setBaseCtrMaxValues :: (Monad m) =>
                       ArgumentOptions
                    -> [SignatureSig]
                    -> Int
                    -> [(T.Text,Bool,Int,String)]
                    -> StateT SMTProblem m ()
setBaseCtrMaxValues args sigs vecLen constrNames =
  mapM_ (\baseNr -> do
            mapM_ (setRetValuesToIdentiyMatrix baseNr) constrNames
            mapM_ (setMaxOfCosts baseNr) constrNames
            mapM_ (setMaxOfParams baseNr) constrNames
        )
  [1..vecLen]
  where setRetValuesToIdentiyMatrix baseNr (ctrName,isCf,_,ctrType) = do
          let baseCf = if isCf && separateBaseCtr args then ctrType ++ "_cf_" else ctrType ++ "_"

          let var = SigRefVar undefined $
                    "rctr_" ++ baseCf ++ T.unpack (convertToSMTText ctrName) ++ "_"
                    ++ show baseNr
          let rs = zip [1..] (fromADatatype vecLen var)
          let constrFun acc (nr,var) =
                -- acc ++ if nr == baseNr
                --        then []
                --        else [("0", Eq, var)]
                acc ++ [(if nr == baseNr then "1" else "0", Eq, var)]
          let constr = foldl constrFun [] rs
          assertions <>= constr

        setMaxOfCosts baseNr (ctrName,isCf,_,ctrType) = do
          let baseCf = if isCf && separateBaseCtr args then ctrType ++ "_cf_" else ctrType ++ "_"
          let var :: ACostCondition Int
              var = AVariableCondition $
                    "kctr_" ++ baseCf ++ T.unpack (convertToSMTText ctrName) ++ "_"
                    ++ (show baseNr)
          let k = head (fromCostCond var)
          let constr = [("1",Geq,k)]
          assertions <>= constr

        setMaxOfParams baseNr (ctrName,isCf,paramLen,ctrType) = do
          let baseCf = if isCf && separateBaseCtr args then ctrType ++ "_cf_" else ctrType ++ "_"
          let var x = SigRefVar undefined $
                "pctr_" ++ baseCf ++ T.unpack ctrName ++ "_" ++ show x ++ "_"
                ++ show baseNr

          let ps = concatMap (fromADatatype  vecLen . var ) [0..paramLen-2]
          let ps' = concatMap (fromADatatype  vecLen . var)
                    [paramLen-1 | paramLen > 0]
          let constr = map (\x -> ("2",Geq,x)) ps
          let constr' = map (\x -> ("1",Geq,x)) ps'
          assertions <>= -- trace ("constr: " ++ show constr)
            constr
          assertions <>= -- trace ("constr': " ++ show constr')
            constr'

addCfGroupsConstraints :: (Monad m) =>
                         Int
                       -> [([ADatatype Int],[ACostCondition Int],
                            [ADatatype Int],[ACostCondition Int])]
                       -> StateT SMTProblem m ()
addCfGroupsConstraints 1 = mapM_ makeAllZero
  where makeAllZero (grplDt, grplCst, grprDt, grprCst) = do
          let vars' = concatMap (fromADatatype 1) grplDt ++
                    concatMap fromCostCond grplCst ++
                    concatMap (fromADatatype 1) grprDt ++
                    concatMap fromCostCond grprCst

          let constr = T.concat (fromListByFun "(and " (\x -> ["(= 0 " +++ x +++ ") "]) vars')
          vars <>=+ vars'
          assertionsStr <>= [constr]

addCfGroupsConstraints vecLen = mapM_ addCfGroupsConstraints'
  where addCfGroupsConstraints' (grplDt, grplCst, grprDt,grprCst) = do
          let vsl = concatMap (fromADatatype vecLen) grplDt ++
                    concatMap fromCostCond grplCst
          let vsr = concatMap (fromADatatype vecLen) grprDt ++
                    concatMap fromCostCond grprCst

          let constr = "(or " +++
                       T.concat (fromListByFun "(and " (\x -> ["(= 0 " +++ x +++ ") "])
                               (vsl ++ vsr))
                       +++
                       T.concat (fromListByFun "(or " (\x -> ["(> " +++ x +++ " 0) "]) vsl)
                       +++ ")"

          -- trace ("vsl: " ++ show constr)
          vars <>=+ vsl ++ vsr
          assertionsStr <>= [constr]


addIndependenceBaseCtrConstraints :: (Monad m) =>
                                    Int
                                  -> [(T.Text,
                                      T.Text,
                                      T.Text,
                                      T.Text,
                                      ADatatype Int,
                                      ADatatype Int,
                                      ACostCondition Int,
                                       ACostCondition Int,
                                      [ADatatype Int],
                                      [ADatatype Int])]
                                  -> StateT SMTProblem m ()
addIndependenceBaseCtrConstraints vecLen = mapM_ addIndependenceBaseCtrConstraints'
  where addIndependenceBaseCtrConstraints' (x1,x2,y1,y2,r1Dt,r2Dt,k1Dt,k2Dt,p1sDt,p2sDt) = do

          let r1s = fromADatatype vecLen r1Dt
          let r2s = fromADatatype vecLen r2Dt
          -- let k1 = fromCostCond k1Dt
          -- let k2 = fromCostCond k2Dt
          -- let p1s = map (fromADatatype vecLen) p1sDt
          -- let p2s = map (fromADatatype vecLen) p2sDt

          let mult fac = map (\r -> "(* " +++ fac +++ " " +++ r +++ ") ")
          let x1R1 = mult x1 r1s
          let y1R2 = mult y1 r2s
          -- let x2R1 = mult x2 r1s
          -- let y2R2 = mult y2 r2s

          -- let x1K1 = mult x1 k1
          -- let y1K2 = mult y1 k2
          -- let x2K1 = mult x2 k1
          -- let y2K2 = mult y2 k2

          -- let x1P1s = map (mult x1) p1s
          -- let y1P2s = map (mult y1) p2s
          -- let x2P1s = map (mult x2) p1s
          -- let y2P2s = map (mult y2) p2s

          let zipping = zipWith4 (\x1r1 y1r2 x2r1 y2r2 ->
                                    "(= (+ " +++ x1r1 +++ " " +++ y1r2 +++ ") " +++
                                       "(+ " +++ x2r1 +++ " " +++ y2r2 +++ "))")
          let andList = T.concat . fromListByFun "(and " return
          -- let r = andList $ zipping x1R1 y1R2 x2R1 y2R2
          -- let k = andList $ zipping x1K1 y1K2 x2K1 y2K2
          -- let ps = concat $ fromListByFun "(and " return $
          --          zipWith4 (\x1P1 y1P2 x2P1 y2P2 -> andList $ zipping x1P1 y1P2 x2P1 y2P2)
          --          x1P1s y1P2s x2P1s y2P2s


          let r1xEqyr2 =
                andList $
                zipWith (\x1r1 y1r2 ->  "(= " +++ x1r1 +++ " " +++ y1r2 +++ ")") x1R1 y1R2
          let eqList r1 r2 = "(= " +++ r1 +++ " " +++ r2 +++ ")"
          let r1Eqr2 = andList $ zipWith eqList r1s r2s
          -- let k1Eqk2 = andList $ zipWith eqList k1 k2
          -- let p1Eqp2 = andList $ map andList $ zipWith (zipWith eqList) p1s p2s
          -- let geq1Constr n = "(>= " +++ n +++ " 1) " --  (< " +++ n +++ " 10)) "
          let geq1Constr n = "(< " +++ n +++ " 1) " --  (< " +++ n +++ " 10)) "
          let name (SigRefVar _ n) =  n

          let constr =
                "(forall ((" +++ x1 +++ " Int) (" +++ y1
                +++ " Int)) " +++ "(or (or " +++ geq1Constr x1
                +++ geq1Constr y1 +++ ")" +++ "(or " +++
                r1Eqr2 +++ " (not " +++ r1xEqyr2 +++ "))))"

          -- trace ("constr: "++ show constr) $
          assertionsStr %= (constr:)

fromListBy :: (Show a) => (a -> [T.Text]) -> [a] -> [T.Text]
fromListBy = fromListByFun "(+ "

fromListByFun :: (Show a) => T.Text -> (a -> [T.Text]) -> [a] -> [T.Text]
fromListByFun str _ [] = []
fromListByFun str f xs =
  map (\idx ->
        if length xs > 1
        then bef +++ head (conv idx) +++
             T.intercalate ")" (tail $ conv idx) +++ ")"
        else T.concat (conv idx)) [0..vecLen-1]

  where numPlus = length xs - 1
        bef     = T.concat $ map (const str) [1..numPlus]

        conv   :: Int -> [T.Text]
        conv idx = insertSpaces (map (!! idx) vars)

        vars :: [[T.Text]]
        vars = map f xs

        vecLen = length (head vars)

        insertSpaces []     = []
        insertSpaces [x]    = [x]
        insertSpaces (x:xs) = x : map (' ' `T.cons`) xs


--
-- ConvertToSMTProblem.hs ends here
