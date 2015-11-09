-- | This module collects declarations from 'Tct.Trs.Method.* and  'Tct.Trs.Strategy.*'.
module Tct.Trs.Declarations
  ( trsDeclarations
  , competition
  ) where


import           Tct.Core                      (withProblem)
import qualified Tct.Core.Data                 as T

import           Tct.Trs.Data.Problem          (isRCProblem)

import           Tct.Trs.Data
import           Tct.Trs.Processors
import           Tct.Trs.Strategy.Certify
import           Tct.Trs.Strategy.Derivational
import           Tct.Trs.Strategy.Runtime
import           Tct.Trs.Strategy.Web


trsDeclarations :: T.Declared Trs Trs => [TrsDeclaration]
trsDeclarations =
  [ T.SD emptyDeclaration
  -- , T.SD withCertificationDeclaration

  , T.SD decomposeDeclaration
  , T.SD decomposeCPDeclaration

  , T.SD boundsDeclaration

  , T.SD innermostRuleRemovalDeclaration
  , T.SD toInnermostDeclaration

  -- Path Orders
  , T.SD epoStarDeclaration

  -- Semantic
  , T.SD polyDeclaration
  , T.SD matrixDeclaration
  , T.SD weightGapDeclaration

  -- DP
  , T.SD dependencyPairsDeclaration
  , T.SD usableRulesDeclaration

  -- DP graph
  -- , T.SD decomposeDGDeclaration
  , T.SD pathAnalysisDeclaration
  , T.SD predecessorEstimationDeclaration
  , T.SD removeHeadsDeclaration
  , T.SD removeInapplicableDeclaration
  , T.SD removeWeakSuffixesDeclaration
  , T.SD simplifyRHSDeclaration
  , T.SD trivialDeclaration

  -- Interpretations
  , T.SD $ T.strategy "matrices"               boundedArgs matrices
  , T.SD $ T.strategy "polys"                  boundedArgs polys
  , T.SD $ T.strategy "ints"                   boundedArgs ints

  -- Simplifications
  , T.SD $ T.strategy "dpsimps"                () dpsimps
  , T.SD $ T.strategy "cleanSuffix"            () cleanSuffix
  , T.SD $ T.strategy "decomposeIndependent"   () decomposeIndependent
  , T.SD $ T.strategy "decomposeIndependentSG" () decomposeIndependentSG
  , T.SD $ T.strategy "toDP"                   () toDP
  , T.SD $ T.strategy "removeLeaf"             (T.OneTuple complexityPairArg) removeLeaf

  -- Strategies
  , T.SD certifyDeclaration
  , T.SD derivationalDeclaration
  , T.SD runtimeDeclaration
  , T.SD competitionDeclaration
  , T.SD webDeclaration
  ]


-- | Declaration for "competition" strategy.
competitionDeclaration :: T.Declaration ('[] T.:-> TrsStrategy)
competitionDeclaration = T.strategy "competition" () competitionStrategy

-- | Default competition strategy.
competition :: TrsStrategy
competition = T.deflFun competitionDeclaration

competitionStrategy :: TrsStrategy
competitionStrategy =
  withProblem $ \p ->
    if isRCProblem p
      then runtime' Best
      else derivational


-- selArg :: T.Argument 'T.Optional (ExpressionSelector F V)
-- selArg = RS.selectorArg
--   `T.withName` "onSelection"
--   `T.withHelp`
--     [ "Determines the strict rules of the selected upper conguence rules." ]
--   `T.optional` decomposeDGselect

-- upperArg :: T.Argument 'T.Optional (Maybe TrsStrategy)
-- upperArg = T.some (T.strat "onUpper" ["Use this processor to solve the upper component."])
--   `T.optional` Nothing

-- lowerArg :: T.Argument 'T.Optional (Maybe TrsStrategy)
-- lowerArg = T.some (T.strat "onLower" ["Use this processor to solve the lower component."])
--   `T.optional` Nothing


-- | This processor implements processor \'dependency graph decomposition\'.
-- It tries to estimate the
-- complexity of the input problem based on the complexity of
-- dependency pairs of upper congruence classes (with respect to the
-- congruence graph) relative to the dependency pairs in the remaining
-- lower congruence classes. The overall upper bound for the
-- complexity of the input problem is estimated by multiplication of
-- upper bounds of the sub problems.
-- Note that the processor allows the optional specification of
-- processors that are applied on the two individual subproblems. The
-- transformation results into the systems which could not be oriented
-- by those processors.
-- decomposeDGDeclaration :: T.Declaration (
--   '[ T.Argument 'T.Optional (ExpressionSelector F V)
--    , T.Argument 'T.Optional (Maybe TrsStrategy)
--    , T.Argument 'T.Optional (Maybe TrsStrategy) ]
--   T.:-> TrsStrategy)
-- decomposeDGDeclaration = T.declare "decomposeDG" help (selArg,upperArg,lowerArg) (\x y z -> T.Apply (decomposeDGProcessor x y z))


