{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- Implementation details can be found in the technical report '@tba@'.
-- | This module provides the \AmortisedAnalysis\ processor.
module Tct.Trs.Processor.AmortisedAnalysis
  ( araDeclaration
  , ara
  , ara'

  , Heuristics (..)
  , heuristicsArg
  ) where


import           Control.Applicative
import           Control.Monad
import qualified Data.Set                     as S
import qualified Control.Exception            as E
import           Control.Monad.State
import           Data.Maybe                                                (fromJust)
import Data.List (nub, sortBy)
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
import Tct.Trs.Data.Symbol (unV, unF)
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


-- TODO's (it currently works but there are optimizations):
-- --------------------------------------------------------
-- 1. Problem F V ... shall be used instead of Problem String String String ...
-- 2. Use SMT solver as other strategies do
-- 3. Get rid of the warnings
-- 4. Use the same PrettyPrinting library
-- 5. Cleanup of unused modules/code
-- 6. Implement type inference for heuristics
-- 7. Possibly: Add argument options, e.g. for printing the inference trees.


data Ara = Ara { heuristics_ :: Heuristics -- ^ Use heuristics. TODO: Heuristics
                                           -- not yet functional as type inference
                                           -- only infers a single datatype.
               , minDegree  :: Int         -- ^ Minimal degree to look for
               , maxDegree  :: Int         -- ^ Maximal degree to look for
               , araTimeout :: Int         -- ^ Timeout
               , araFindStrictRules :: Maybe Int -- ^ Min nr of strict rules to
                                                 -- orient strict.
               }
         deriving Show


defaultArgs :: ArgumentOptions
defaultArgs = ArgumentOptions {filePath = ""
                              , minVectorLength = 1
                              , maxVectorLength = 3
                              , uniqueConstrFuns = False
                              , separateBaseCtr = False
                              , tempFilePath = "/tmp"
                              , helpText = False
                              , keepFiles = False
                              , printInfTree = False
                              , verbose = False
                              , shift = False
                              , allowLowerSCC = False
                              , lowerbound = False
                              , timeout = Nothing
                              , smtSolver = Z3
                              , findStrictRules = Nothing
                              }


data Heuristics = Heuristics | NoHeuristics deriving (Bounded, Enum, Eq, Show)

data AraProof f v = AraProof
  { signatures        :: [ASignatureSig] -- ^ Signatures used for the proof
  , cfSignatures      :: [ASignatureSig] -- ^ Cost-free signatures used for the proof
  , baseCtrSignatures :: [ASignatureSig] -- ^ Base constructors used for the proof
                                         -- (cf. Superposition of constructors)
  , strictlyTyped :: [RT.Rule String String]
  , weaklyTyped :: [RT.Rule String String]
  } deriving Show


instance T.Processor Ara where
  type ProofObject Ara = ApplicationProof (OrientationProof (AraProof F V))
  type In  Ara         = Prob.Trs
  type Out Ara         = Prob.Trs
  type Forking Ara     = T.Optional T.Id

  execute p probTcT =

    maybe araFun (\s -> T.abortWith (Inapplicable s :: ApplicationProof
                                   (OrientationProof (AraProof F V)))) maybeApplicable

    where maybeApplicable = -- Prob.isRCProblem' probTcT <|>    -- check left linearity
                            Prob.isInnermostProblem' probTcT -- check innermost
                            -- <|> RS.isConstructorTrs' sig trs -- not needed

          prob = inferTypesAndSignature (convertProblem probTcT)

          araFun :: T.TctM (T.Return Ara)
          araFun =
            join $ liftIO $ E.catch
                 (do
                     -- set arguments
                     let args = defaultArgs { minVectorLength = minDegree p
                                            , maxVectorLength = maxDegree p
                                            , timeout = Just $ araTimeout p
                                            , findStrictRules = araFindStrictRules p
                                            }

                     -- Find out SCCs
                     let reachability = analyzeReachability prob


                     (prove, infTrees) <- analyzeProblem args reachability prob
                     -- Solve cost constraints
                     let cond = conditions prove
                     let probSig = RT.signatures (problem prove)

                     -- check if it lowerbound problem
                     when (lowerbound args) $
                       E.throw $ FatalException "Lowerbound analysis not yet implemented!"

                     -- Solve datatype constraints
                     (sigs, cfSigs, valsNs, vals, baseCtrs, cfBaseCtrs, bigO, (strictRls,weakRls)) <-
                       solveProblem args (fromJust probSig) cond (signatureMap prove)
                       (costFreeSigs prove)

                     let strictRules = Prob.strictTrs probTcT
                     let strictRules' = RS.filter ((`notElem` strictRls) . convertRule) strictRules
                     let weakRulesAdd' = RS.filter ((`elem` strictRls) . convertRule) strictRules
                     let strictDPs = Prob.strictDPs probTcT
                     let strictDPs' = RS.filter ((`notElem` strictRls) . convertRule) strictDPs
                     let weakDPsAdd' = RS.filter ((`elem` strictRls) . convertRule) strictDPs

                     let newProb' :: Problem F V
                         newProb' = probTcT { Prob.strictDPs = strictDPs'
                                            , Prob.strictTrs = strictRules'
                                            , Prob.weakDPs = Prob.weakDPs probTcT
                                                             `RS.union` weakDPsAdd'
                                            , Prob.weakTrs = Prob.weakTrs probTcT
                                                             `RS.union` weakRulesAdd'
                                            }

                     let newProb :: Trs
                         newProb = newProb'

                     let compl :: T.Complexity
                         compl = T.Poly (Just bigO)

                     return $
                       T.succeedWith
                       (Applicable . Order $ AraProof sigs cfSigs baseCtrs strictRls weakRls)
                       -- type: CertificateFn p = Forking p C.Certificate -> C.Certificate
                       (if null weakRls
                        then const (T.timeUBCert compl) -- prove done
                        else certification compl)       -- only a step in the proof
                       (T.Opt $ T.toId newProb)


                 ) (\(e :: ProgException) ->
                      -- do
                      --  case (e :: ProgException) of
                      --    ShowTextOnly txt -> do
                      --      putStrLn "MAYBE"
                      --      putStrLn txt
                      --    WarningException txt -> do
                      --      putStrLn "MAYBE"
                      --      putStrLn txt
                      --    FatalException txt -> do
                      --      putStr "ERROR:"
                      --      putStrLn txt
                      --    ParseException txt -> do
                      --      putStr "ERROR:"
                      --      putStrLn txt
                      --    UnsolveableException txt -> do
                      --      putStrLn "MAYBE"
                      --      putStrLn "UNSAT"
                      --      putStrLn txt
                      --    SemanticException txt -> do
                      --      putStr "ERROR:"
                      --      putStrLn txt
                       return $
                         T.abortWith (Applicable (Incompatible :: OrientationProof (AraProof F V))))

certification :: T.Complexity -> T.Optional T.Id T.Certificate -> T.Certificate
certification comp cert = case cert of
  T.Null         -> T.timeUBCert comp
  T.Opt (T.Id c) -> T.updateTimeUBCert c (`SR.add` comp)


convertProblem :: Prob.Problem F V -> RT.Problem String String String String String String
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
             , RT.variables = fmap unV $
                              S.toList $ RS.vars (Prob.strictTrs inProb `RS.union`
                                                  Prob.weakTrs inProb)
             , RT.symbols = fmap unF $
                            S.toList (Sig.defineds (Prob.signature inProb)) ++
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
convertRule :: R.Rule F V -> RT.Rule String String
convertRule (R.Rule lhs rhs) = RT.Rule (convertTerm lhs) (convertTerm rhs)
convertTerm :: R.Term F V -> RT.Term String String
convertTerm (R.Var v) = RT.Var (unV v)
convertTerm (R.Fun f ch) = RT.Fun (unF f) (fmap convertTerm ch)


-- --- * instances ------------------------------------------------------------------------------------------------------

heuristicsArg :: T.Argument 'T.Required Heuristics
heuristicsArg = T.flag "Wether to use heuristics or not."
  [ "WARNING: Not yet functional, as type inference not yet implemented." ]

minDimArg :: T.Argument 'T.Required Int
minDimArg = T.flag "minimum Degree"
  [ "Minimum degree to be looked for (minimal length of vectors in signatures).",
    "Default is 1."]

maxDimArg :: T.Argument 'T.Required Int
maxDimArg = T.flag "maximum Degree"
  [ "Maximum degree to be looked for (maximal length of vectors in signatures). ",
    "Default is 3." ]

araTimeoutArg :: T.Argument 'T.Required Int
araTimeoutArg =
  T.flag "maximum Degree"
  [ "Timeout for the SMT solver. ",
    "Default is 15." ]

orientStrictArg :: T.Argument 'T.Required Int
orientStrictArg = T.flag "nr"
  [ "Nr specifies the amount of rules to at least orient strictly.",
    "If not set, all strict rules must be oriented strictly. ",
    "If activated, but no value given, then default is 1." ]

description :: [String]
description = [ unwords
  [ "This processor implements the amortised resource analysis."] ]

araStrategy :: Maybe Int -> Heuristics -> Int -> Int -> Int -> TrsStrategy
araStrategy oS h minD maxD to = T.Apply (Ara h minD maxD to oS)

araDeclaration :: Maybe Int -> T.Declaration ('[T.Argument 'T.Optional Heuristics
                                  ,T.Argument 'T.Optional Int
                                  ,T.Argument 'T.Optional Int
                                  ,T.Argument 'T.Optional Int
                                  ] T.:-> TrsStrategy)
araDeclaration orientStrict =
  T.declare "ara" description (hArg,minDim,maxDim,timeout) (araStrategy orientStrict)
  where hArg = heuristicsArg `T.optional` NoHeuristics
        minDim = minDimArg `T.optional` 1
        maxDim = minDimArg `T.optional` 3
        timeout = araTimeoutArg `T.optional` 15


ara :: TrsStrategy
ara = T.deflFun (araDeclaration Nothing)

ara' :: Heuristics -> Maybe Int -> Int -> Int -> Int ->  TrsStrategy
ara' h oS = T.declFun (araDeclaration oS) h


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
    PP.vcat (fmap (PP.text . show . prettyAraSignature') (sorted $ baseCtrSignatures proof)) PP.<$>
    if null (strictlyTyped proof ++ weaklyTyped proof)
    then PP.empty
    else PP.line PP.<$>
         PP.text "Following Still Strict Rules were Typed as:" PP.<$>
         PP.text "-------------------------------------------" PP.<$>
         PP.nest 2 (PP.text "1. Strict:" PP.<$>
                    PP.vcat (fmap PP.pretty (strictlyTyped proof))) PP.<$>
         PP.nest 2 (PP.text "2. Weak:" PP.<$>
                    PP.vcat (fmap PP.pretty (weaklyTyped proof)))


  -- PP.vcat
  --   [ PP.text "Strict Rules in Predicative Notation:"
  --   , ppind (SM.prettySafeTrs (safeMapping_ proof) (stricts_ proof))
  --   , PP.text "Safe Mapping:"
  --   , ppind (safeMapping_ proof)
  --   , PP.text "Argument Permuation:"
  --   , ppind (argumentPermutation_ proof)
  --   , PP.text "Precedence:"
  --   , ppind (precedence_ proof) ]
  --   where ppind a = PP.indent 2 $ PP.pretty a
    where sorted = nub . sortBy (compare `on` fst4 . RT.lhsRootSym)

instance Xml.Xml (AraProof f v) where
  toXml _ = Xml.empty

