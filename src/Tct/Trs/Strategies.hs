-- | This module collects declarations from 'Tct.Trs.Processor.* and  'Tct.Trs.Strategy.*'.
module Tct.Trs.Strategies (trsDeclarations) where


import Tct.Core

import Tct.Trs.Data
import Tct.Trs.Processors
import Tct.Trs.Strategy.Certify
import Tct.Trs.Strategy.Competition
import Tct.Trs.Strategy.Derivational
import Tct.Trs.Strategy.Runtime
import Tct.Trs.Strategy.Web


trsDeclarations :: Declared Trs Trs => [TrsDeclaration]
trsDeclarations =
  [ SD emptyDeclaration
  -- , SD withCertificationDeclaration

  , SD decomposeDeclaration
  , SD decomposeCPDeclaration

  , SD boundsDeclaration

  , SD innermostRuleRemovalDeclaration
  , SD toInnermostDeclaration

  -- Path Orders
  , SD epoStarDeclaration

  -- Semantic
  , SD polyDeclaration
  , SD matrixDeclaration
  , SD weightGapDeclaration

  -- DP
  , SD dependencyPairsDeclaration
  , SD usableRulesDeclaration

  -- DP graph
  -- , SD decomposeDGDeclaration
  , SD pathAnalysisDeclaration
  , SD predecessorEstimationDeclaration
  , SD removeHeadsDeclaration
  , SD removeInapplicableDeclaration
  , SD removeWeakSuffixesDeclaration
  , SD simplifyRHSDeclaration
  , SD trivialDeclaration

  -- Interpretations
  , SD $ strategy "matrices"               boundedArgs matrices
  , SD $ strategy "polys"                  boundedArgs polys
  , SD $ strategy "ints"                   boundedArgs ints

  -- Simplifications
  , SD $ strategy "dpsimps"                () dpsimps
  , SD $ strategy "cleanSuffix"            () cleanSuffix
  , SD $ strategy "decomposeIndependent"   () decomposeIndependent
  , SD $ strategy "decomposeIndependentSG" () decomposeIndependentSG
  , SD $ strategy "toDP"                   () toDP
  , SD $ strategy "removeLeaf"             (OneTuple complexityPairArg) removeLeaf

  -- Strategies
  , SD certifyDeclaration
  , SD derivationalDeclaration
  , SD runtimeDeclaration
  , SD competitionDeclaration
  , SD webDeclaration
  ]

