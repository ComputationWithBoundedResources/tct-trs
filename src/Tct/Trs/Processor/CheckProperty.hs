{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
-- Implementation details can be found in the technical report '@tba@'.
-- | This module provides the \CheckProperty\ processor, which will only check for
-- a certain property.
module Tct.Trs.Processor.CheckProperty
  ( checkPropDeclaration
  , checkProp
  , checkProp'
  , checkPropLLArg
  , checkPropCtrArg
  , LL (..)
  , Ctr (..)
  ) where


import           Control.Monad
import qualified Data.Set                     as S
import qualified Control.Exception            as E
import           Control.Monad.State
import           Data.Maybe
import Data.List (nub, sortBy, intersperse)
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

-- Possible Improvements (it currently works but there may be optimizations):
-- --------------------------------------------------------------------------
-- 1. Problem F V ... shall be used instead of Problem String String String ...
--    ... DONE except that show is used for generating SMT strings
-- 2. Use SMT solver as other strategies do
-- 3. Get rid of the warnings
-- 4. Use the same PrettyPrinting library
-- 5. Cleanup of unused modules/code
-- 6. Implement type inference for heuristics
-- 7. Possibly: Add argument options, e.g. for printing the inference trees.


data CheckProp = CheckProp { ll :: Maybe LL   -- ^ Check for left-linearity
                           , ctr :: Maybe Ctr -- ^ Check for constructor TRS
                           }
               deriving Show


data LL = IsLL | IsNotLL        -- left linearity
        deriving (Bounded, Enum, Eq, Show)
data Ctr = IsCtr | IsNotCtr     -- constructor TRS
         deriving (Bounded, Enum, Eq, Show)

class Pos x where
  pos :: x
  inv :: x -> x

instance Pos LL where
  pos = IsLL
  inv IsLL = IsNotLL
instance Pos Ctr where
  pos = IsCtr
  inv IsCtr = IsNotCtr

data CheckPropProof f v = CheckPropProof
  { -- results of checks
    proofLL :: Maybe Bool
  , proofCtr   :: Maybe Bool

    -- what was checked for
  , checkLL :: Maybe LL
  , checkCtr :: Maybe Ctr

  } deriving Show


instance T.Processor CheckProp where
  type ProofObject CheckProp = ApplicationProof (OrientationProof (CheckPropProof F V))
  type In  CheckProp         = Prob.Trs
  type Out CheckProp         = Prob.Trs
  type Forking CheckProp     = T.Optional T.Id

  execute p probTcT =
    let rules = Prob.allComponents probTcT
        sigs = Prob.signature probTcT
        checkLL _ = RS.isLeftLinear rules
        checkCtr _ = RS.isConstructorTrs sigs rules

        -- checkFun IsLL = retFun IsLL IsNotLL $ RS.isLeftLinear rules
        -- checkFun IsNotLL = retFun IsNotLL IsLL $ not (RS.isLeftLinear rules)

        chkLL = ll p
        prLL = maybe Nothing (Just . checkLL) chkLL

        chkCtr = ctr p
        prCtr = maybe Nothing (Just . checkCtr) chkCtr

    in T.succeedWith (Applicable . Order $ CheckPropProof prLL prCtr chkLL chkCtr)
       certification
       T.Null

    where ll' p = maybe Nothing (const $ Just $ RS.isLeftLinear) (ll p)


certification :: T.Optional T.Id T.Certificate -> T.Certificate
certification cert = T.Certificate T.Unknown T.Unknown T.Unknown T.Unknown


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
             , RT.variables = -- fmap unV $
                              S.toList $ RS.vars (Prob.strictTrs inProb `RS.union`
                                                  Prob.weakTrs inProb)
             , RT.symbols = -- fmap unF $
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
convertRule :: R.Rule F V -> RT.Rule F V
convertRule (R.Rule lhs rhs) = RT.Rule (convertTerm lhs) (convertTerm rhs)
convertTerm :: R.Term F V -> RT.Term F V
convertTerm (R.Var v) = RT.Var v
convertTerm (R.Fun f ch) = RT.Fun f (fmap convertTerm ch)


-- instances

checkPropLLArg :: T.Argument 'T.Required (Maybe LL)
checkPropLLArg = T.some $ T.flag
  "left-linear"
  ["Check for (non)-left-linarity"]

checkPropCtrArg :: T.Argument 'T.Required (Maybe Ctr)
checkPropCtrArg = T.some $ T.flag
  "constructorTRS"
  ["Check whether the TRS is a constructor TRS or not."]

description :: [String]
description = [ unwords
  [ "This processor only checks for one or more properties and the exits the program."] ]

propStrategy :: Maybe LL -> Maybe Ctr -> TrsStrategy
propStrategy ll ctr = T.Apply (CheckProp ll ctr)

checkPropDeclaration :: T.Declaration ('[T.Argument 'T.Optional (Maybe LL)
                                   ,T.Argument 'T.Optional (Maybe Ctr)
                                   ] T.:-> TrsStrategy)
checkPropDeclaration =
  T.declare "checkprop" description (llArg',ctrArg') propStrategy
  where llArg' = checkPropLLArg `T.optional` Nothing
        ctrArg' = checkPropCtrArg `T.optional` Nothing

checkProp :: TrsStrategy
checkProp = T.deflFun (checkPropDeclaration)

checkProp' :: Maybe LL -> Maybe Ctr -> TrsStrategy
checkProp' = T.declFun checkPropDeclaration


--- * proofdata
--------------------------------------------------------------------------------


instance PP.Pretty LL where
  pretty IsLL = PP.text "is left-linear"
  pretty IsNotLL = PP.text "is not left-linear"

instance PP.Pretty Ctr where
  pretty IsCtr = PP.text "is a constructor TRS"
  pretty IsNotCtr = PP.text "is not a constructor TRS"

instance (Ord f, PP.Pretty f, PP.Pretty v) => PP.Pretty (CheckPropProof f v) where
  pretty (CheckPropProof prLL prCtr chLL chCtr) =
    -- Signatures
    maybe PP.empty (pretty chLL) prLL PP.<$>
    maybe PP.empty (pretty chCtr) prCtr PP.<$>
    PP.text "Overall Answer to question if TRS is " PP.<> question PP.<> PP.colon PP.<$>
    PP.bool answer

    where question = PP.hcat $ intersperse (PP.text " and ") $
                     [ maybe PP.empty PP.pretty chLL
                     , maybe PP.empty PP.pretty chCtr
                     ]
          cF x = if x == pos then True else False

          chks = [ cF <$> chLL  -- testing for True/False values
                 , cF <$> chCtr
                 ]

          prs = [ prLL          -- outcome of checks
                , prCtr
                ]
          answer = all (\(a,b) -> a == b) $
                   concatMap (\(a,b) -> if isJust b then [(a,b)] else [])
                   (zip [prLL,prCtr] chks)

          pretty Nothing _ = PP.empty
          pretty (Just x) o = PP.pretty x PP.<> PP.colon PP.<+> PP.pretty o


instance Xml.Xml (CheckPropProof f v) where
  toXml _ = Xml.empty

