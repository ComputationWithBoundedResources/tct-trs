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


trsDeclarations :: [TrsDeclaration]
trsDeclarations =
  [ T.SD emptyDeclaration
  , T.SD withCertificationDeclaration

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
  , T.SD decomposeDGDeclaration
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

