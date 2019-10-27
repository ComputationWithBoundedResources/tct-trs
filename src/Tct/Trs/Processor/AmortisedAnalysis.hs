{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
-- Implementation details can be found in the technical report '@tba@'.
-- | This module provides the \AmortisedAnalysis\ processor.
module Tct.Trs.Processor.AmortisedAnalysis
  ( araDeclaration
  , ara
  , ara'
  , araBestCase'
  , araFull'
  ) where

import System.Exit
import           Control.Monad
import qualified Data.Set                     as S
import qualified Control.Exception            as E
import           Control.Monad.State
import           Data.Maybe
import Data.List (nub, sortBy,find)
import Data.Function (on)

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Common.SemiRing        as SR
import qualified Tct.Core.Data                as T

import qualified Data.Rewriting.Rule          as R
import qualified Data.Rewriting.Typed.Rule    as RT
import qualified Data.Rewriting.Typed.Problem as RT
import qualified Data.Rewriting.Typed.Signature as RT


import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import Tct.Trs.Data.Symbol
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.ProblemKind     as Prob
import qualified Tct.Trs.Data.Signature       as Sig
import qualified Tct.Trs.Data.Rules as RS

import Data.Rewriting.ARA.InferTypes
import           Data.Rewriting.ARA.ByInferenceRules.Analyzer
import           Data.Rewriting.ARA.ByInferenceRules.CmdLineArguments
import           Data.Rewriting.ARA.ByInferenceRules.ConstraintSolver.SMT
import           Data.Rewriting.ARA.ByInferenceRules.Graph.Ops
import           Data.Rewriting.ARA.ByInferenceRules.Prove
import Data.Rewriting.ARA.ByInferenceRules.HelperFunctions
import           Data.Rewriting.ARA.ByInferenceRules.TypeSignatures
import           Data.Rewriting.ARA.Exception
import           Data.Rewriting.ARA.Exception.Pretty                       ()

data Ara = Ara { minDegree  :: Int            -- ^ Minimal degree to look for
               , maxDegree  :: Int            -- ^ Maximal degree to look for
               , araTimeout :: Int            -- ^ Timeout
               , araRuleShifting :: Maybe Int -- ^ Min nr of strict rules to orient strict.
               , isBestCase :: Bool           -- ^ perform best-case analysis
               , mkCompletelyDefined :: Bool  -- ^ make TRS completely defined
               }
         deriving Show


defaultArgs :: ArgumentOptions
defaultArgs = ArgumentOptions { filePath = ""
                              , minVectorLength = 1
                              , maxVectorLength = 3
                              , uniqueConstrFuns = False
                              , separateBaseCtr = False
                              , tempFilePath = "/tmp"
                              , noHeur = False
                              , helpText = False
                              , keepFiles = False
                              , printInfTree = False
                              , verbose = False
                              , shift = False
                              , allowLowerSCC = False
                              , allowCf = False
                              , lowerbound = False
                              , lowerboundArg = Nothing
                              , lowerboundNoComplDef = False
                              , constructorArgSelection = []
                              , timeout = Nothing
                              , smtSolver = Z3
                              , findStrictRules = Nothing
                              , directArgumentFilter = False
                              , nrOfRules = Nothing
                              }

type DT = String

data AraProof f v = AraProof
  { signatures        :: [ASignatureSig F DT]      -- ^ Signatures used for the
                                                   -- proof
  , cfSignatures      :: [ASignatureSig F DT]      -- ^ Cost-free signatures used
                                                   -- for the proof
  , baseCtrSignatures :: [ASignatureSig String DT] -- ^ Base constructors used for
                                                   -- the proof (cf. Superposition
                                                   -- of constructors)
  , strictlyTyped :: [RT.Rule F V]
  , weaklyTyped :: [RT.Rule F V]
  } deriving Show


instance T.Processor Ara where
  type ProofObject Ara = ApplicationProof (OrientationProof (AraProof F V))
  type In Ara = Prob.Trs
  type Out Ara = Prob.Trs
  type Forking Ara = T.Optional T.Id
  execute p probTcT = maybe araFun (\s -> T.abortWith (Inapplicable s :: ApplicationProof (OrientationProof (AraProof F V)))) maybeApplicable
    where
      maybeApplicable = Prob.isInnermostProblem' probTcT -- check innermost Prob.isRCProblem' probTcT <|> -- check left linearity
      defSyms = S.toList (Sig.defineds (Prob.signature probTcT))
      probIn = inferTypesAndSignature defSyms (convertProblem probTcT)
      araFun :: T.TctM (T.Return Ara)
      araFun =
        join $
        liftIO $
        E.catch -- set arguments
          (do let args =
                    defaultArgs
                      { minVectorLength = minDegree p
                      , maxVectorLength = maxDegree p
                      , timeout = Just $ araTimeout p
                      , findStrictRules = araRuleShifting p
                      , lowerboundArg =
                          if isBestCase p
                            then Just 1
                            else Nothing
                      , lowerboundNoComplDef = not (mkCompletelyDefined p)
                      , nrOfRules = Just $ length (Prob.strictTrs probTcT) + length (Prob.weakTrs probTcT) + length (Prob.strictDPs probTcT) + length (Prob.weakDPs probTcT)
                      }
              let isMainFun (RT.Fun f _) = f == fun "main"
                  isMainFun _ = False
              let mainFun = filter (isMainFun . RT.lhs) (RT.allRules $ RT.rules probIn)
              let stricts = RT.strictRules (RT.rules probIn)
              prob <-
                if (lowerbound args || isJust (lowerboundArg args)) && null mainFun && not (null stricts)
                  then do
                    let (RT.Fun f ch) = RT.lhs $ last stricts
                    let sigF = fromMaybe (E.throw $ FatalException $ "Could not find signature of " ++ show f) $ find ((== f) . RT.lhsRootSym) (fromJust $ RT.signatures probIn)
                    let mainArgs = map (\nr -> var ("x" ++ show nr)) [1 .. length ch]
                    let rule = RT.Rule (RT.Fun (fun "main") (map RT.Var mainArgs)) (RT.Fun f (map RT.Var mainArgs))
                    return $
                      probIn
                        { RT.rules = (RT.rules probIn) {RT.strictRules = RT.strictRules (RT.rules probIn) ++ [rule]}
                        , RT.signatures = fmap (++ [sigF {RT.lhsRootSym = fun "main"}]) (RT.signatures probIn)
                        }
                  else return probIn
                     -- Find out SCCs
              let reachability = analyzeReachability prob
              (prove, _) <- analyzeProblem args reachability prob
                     -- Solve cost constraints
              let cond = conditions prove
              let probSig = RT.signatures (problem prove)
                     -- Solve datatype constraints
              (sigs, cfSigs, _, _, baseCtrs, _, bigO, (strictRls, weakRls)) <- solveProblem args (fromJust probSig) cond (signatureMap prove) (costFreeSigs prove)
              print prob
              print bigO
              print args
              let strictRules = Prob.strictTrs probTcT
              let strictRules' = RS.filter ((`notElem` strictRls) . convertRule) strictRules
              let weakRulesAdd' = RS.filter ((`elem` strictRls) . convertRule) strictRules
              let strictDPs = Prob.strictDPs probTcT
              let strictDPs' = RS.filter ((`notElem` strictRls) . convertRule) strictDPs
              let weakDPsAdd' = RS.filter ((`elem` strictRls) . convertRule) strictDPs
              let newProb' :: Trs
                  newProb' =
                    probTcT
                      { Prob.strictDPs = strictDPs'
                      , Prob.strictTrs = strictRules'
                      , Prob.weakDPs = Prob.weakDPs probTcT `RS.union` weakDPsAdd'
                      , Prob.weakTrs = Prob.weakTrs probTcT `RS.union` weakRulesAdd'
                      }
              let compl :: T.Complexity
                  compl = T.Poly (Just bigO)
              let cert
                    | isBestCase p = T.timeBCLBCert
                    | otherwise = T.timeUBCert
                  cert'
                    | isBestCase p = certificationBCLB
                    | otherwise = certification
              return $
                T.succeedWith
                  (Applicable . Order $ AraProof sigs cfSigs baseCtrs strictRls weakRls)
                  (if null weakRls
                     then const (cert compl) -- prove done
                     else cert' compl -- only a step in the proof
                  -- TODO: best-case lowerbound vs worst-case lowerbound
                  -- TODO: elaborate to completely defined throws an error
                  -- TODO: error wrong BC output
                   )
                  (if null weakRls || -- could be dis/enabled (but hides/shows empty processor)
                      isNothing (araRuleShifting p) -- always finished
                     then T.Null
                     else T.Opt $ T.toId newProb'))
          (\(_ :: ProgException) -> return $ T.abortWith (Applicable (Incompatible :: OrientationProof (AraProof F V))))

certification :: T.Complexity -> T.Optional T.Id T.Certificate -> T.Certificate
certification comp cert = case cert of
  T.Null         -> T.timeUBCert comp
  T.Opt (T.Id c) -> T.updateTimeUBCert c (`SR.add` comp)

certificationBCLB :: T.Complexity -> T.Optional T.Id T.Certificate -> T.Certificate
certificationBCLB comp cert = case cert of
  T.Null         -> T.timeBCLBCert comp
  T.Opt (T.Id c) -> T.updateTimeBCLBCert c (`SR.add` comp)


convertProblem :: Prob.Problem F V -> RT.Problem F V F dt dt F
convertProblem inProb =
  RT.Problem { RT.startTerms = convertStartTerms $ Prob.startTerms inProb
             , RT.strategy = convertStrategy $ Prob.strategy inProb
             , RT.theory = Nothing
             , RT.datatypes = Nothing
             , RT.signatures = Nothing
             , RT.rules = RT.RulesPair
                          (fmap convertRule $ RS.toList (Prob.strictTrs inProb) ++
                            RS.toList (Prob.strictDPs inProb))
                          (fmap convertRule $ RS.toList (Prob.weakTrs inProb) ++
                            RS.toList (Prob.weakDPs inProb))
             , RT.variables = S.toList $ RS.vars (Prob.strictTrs inProb `RS.union`
                                                  Prob.weakTrs inProb)
             , RT.symbols = S.toList (Sig.defineds (Prob.signature inProb)) ++
                            S.toList (Sig.constructors (Prob.signature inProb))
             , RT.comment = Nothing
             }

convertStartTerms :: StartTerms t -> RT.StartTerms
convertStartTerms Prob.AllTerms{} = RT.AllTerms
convertStartTerms Prob.BasicTerms{} = RT.BasicTerms
convertStrategy :: Strategy -> RT.Strategy
convertStrategy Prob.Innermost = RT.Innermost
convertStrategy Prob.Full = RT.Full
convertStrategy Prob.Outermost = RT.Outermost
convertRule :: R.Rule F V -> RT.Rule F V
convertRule (R.Rule lhs rhs) = RT.Rule (convertTerm lhs) (convertTerm rhs)
convertTerm :: R.Term F V -> RT.Term F V
convertTerm (R.Var v) = RT.Var v
convertTerm (R.Fun f ch) = RT.Fun f (fmap convertTerm ch)


-- instances

minDimArg :: T.Argument 'T.Required Int
minDimArg = T.flag "min"
  [ "Minimum degree to be looked for (minimal length of vectors in signatures).",
    "Default is 1."]

maxDimArg :: T.Argument 'T.Required Int
maxDimArg = T.flag "max"
  [ "Maximum degree to be looked for (maximal length of vectors in signatures). ",
    "Default is 3." ]

araTimeoutArg :: T.Argument 'T.Required Int
araTimeoutArg =
  T.flag "t"
  [ "Timeout for the SMT solver. ",
    "Default is 15." ]

orientStrictArg :: T.Argument 'T.Required Int
orientStrictArg = T.flag "nr"
  [ "Nr specifies the amount of rules to at least orient strictly.",
    "If not set, all strict rules must be oriented strictly. ",
    "If activated, but no value given, then default is 1." ]

araBestCaseArg :: T.Argument 'T.Required Bool
araBestCaseArg =
  T.flag "bc"
  [ "Perform a best case analysis. Default is False." ]

araBestCaseCompletelyDefinedArg :: T.Argument 'T.Required Bool
araBestCaseCompletelyDefinedArg =
  T.flag "cd"
  [ "Introduce rules s.t. TRS is completely defined. Only useful for best-case analysis! Default is False." ]


description :: [String]
description = [ unwords
  [ "This processor implements the amortised resource analysis."] ]

araStrategy :: Maybe Int -> Int -> Int -> Int -> Bool -> Bool -> TrsStrategy
araStrategy oS minD maxD to bc cd = T.Apply (Ara minD maxD to oS bc cd) 

araDeclaration :: Maybe Int -> T.Declaration ('[T.Argument 'T.Optional Int
                                               ,T.Argument 'T.Optional Int
                                               ,T.Argument 'T.Optional Int
                                               ,T.Argument 'T.Optional Bool
                                               ,T.Argument 'T.Optional Bool
                                               ] T.:-> TrsStrategy)
araDeclaration orientStrict = T.declare "ara" description (minDim, maxDim, to, bestCase, complDef) (araStrategy orientStrict)
  where
    minDim = minDimArg `T.optional` 1
    maxDim = minDimArg `T.optional` 3
    to = araTimeoutArg `T.optional` 15
    bestCase = araBestCaseArg `T.optional` False
    complDef = araBestCaseCompletelyDefinedArg `T.optional` False


ara :: TrsStrategy
ara = T.deflFun (araDeclaration Nothing)

ara' :: Maybe Int -> Int -> Int -> Int -> TrsStrategy
ara' oS minDim maxDim t = T.declFun (araDeclaration oS) minDim maxDim t False False

araBestCase' :: Maybe Int -> Int -> Int -> Int -> TrsStrategy
araBestCase' oS minDim maxDim t = T.declFun (araDeclaration oS) minDim maxDim t True False


araFull' :: Maybe Int -> Int -> Int -> Int -> Bool -> Bool -> TrsStrategy
araFull' oS = T.declFun (araDeclaration oS) 


--- * proofdata
--------------------------------------------------------------------------------

instance (Ord f, PP.Pretty f, PP.Pretty v) => PP.Pretty (AraProof f v) where
  pretty proof =
    -- Signatures
    PP.text "Signatures used:" PP.<$>
    PP.text "----------------" PP.<$>
    PP.vcat (fmap (PP.text . show . prettyAraSignature') (sorted $ signatures proof)) PP.<$>
    PP.line PP.<$>
    PP.text "Cost-free Signatures used:" PP.<$>
    PP.text "--------------------------" PP.<$>
    PP.vcat (fmap (PP.text . show . prettyAraSignature') (sorted $ cfSignatures proof)) PP.<$>
    PP.line PP.<$>
    PP.text "Base Constructor Signatures used:" PP.<$>
    PP.text "---------------------------------" PP.<$>
    PP.vcat (fmap (PP.text . show . prettyAraSignature') (sorted' $ baseCtrSignatures proof)) PP.<$>
    if null (strictlyTyped proof ++ weaklyTyped proof)
    then PP.empty
    else PP.line PP.<$>
         PP.text "Following Still Strict Rules were Typed as:" PP.<$>
         PP.text "-------------------------------------------" PP.<$>
         PP.nest 2 (PP.text "1. Strict:" PP.<$>
                    PP.vcat (fmap PP.pretty (strictlyTyped proof))) PP.<$>
         PP.nest 2 (PP.text "2. Weak:" PP.<$>
                    PP.vcat (fmap PP.pretty (weaklyTyped proof)))

    where sorted = nub . sortBy (compare `on` fst4 . RT.lhsRootSym)
          sorted' = nub . sortBy (compare `on` fst4 . RT.lhsRootSym)

instance Xml.Xml (AraProof f v) where
  toXml _ = Xml.empty

