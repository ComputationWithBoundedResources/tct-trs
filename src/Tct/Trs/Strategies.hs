-- | This module collects strategies and declarations from 'Tct.Trs.Processor.* and  'Tct.Trs.Strategy.*'.
module Tct.Trs.Strategies (
  trsDeclarations
  , module M
  ) where


import Tct.Core
import Tct.Core.Data                 (declare)
import Tct.Core.Processor.MSum       (madd)

import Tct.Trs.Data
import Tct.Trs.Processors            as M
import Tct.Trs.Strategy.Certify      as M
import Tct.Trs.Strategy.Competition  as M
import Tct.Trs.Strategy.Derivational as M
import Tct.Trs.Strategy.Runtime      as M
import Tct.Trs.Strategy.Web          as M


trsDeclarations :: Declared Trs Trs => [TrsDeclaration]
trsDeclarations =
  [ SD emptyDeclaration
  , SD withCertificationDeclaration
  , SD $ declare
          "tight"
          ["Run lower and upper bounds analysis in parallel."]
          (strat "lower" ["The lower bound strategy to apply."], strat "upper" ["The upper bound strategy to apply."])
          (madd :: TrsStrategy -> TrsStrategy -> TrsStrategy)
  --
  -- * Lower Bound
  , SD decreasingLoopsDeclaration

  -- * Upper Bound
  , SD decomposeDeclaration
  , SD decomposeCPDeclaration

  , SD boundsDeclaration

  , SD innermostRuleRemovalDeclaration
  , SD toInnermostDeclaration

  -- ** Path Orders
  , SD epoStarDeclaration

  -- ** Semantic
  , SD polyDeclaration
  , SD matrixDeclaration
  , SD weightGapDeclaration

  -- ** DP
  , SD dependencyPairsDeclaration
  , SD usableRulesDeclaration

  -- ** DP graph
  , SD decomposeDGDeclaration
  , SD pathAnalysisDeclaration
  , SD predecessorEstimationDeclaration
  , SD removeHeadsDeclaration
  , SD removeInapplicableDeclaration
  , SD removeWeakSuffixesDeclaration
  , SD simplifyRHSDeclaration
  , SD trivialDeclaration

  -- ** Interpretations
  , SD $ strategy "matrices"               boundedArgs matrices
  , SD $ strategy "polys"                  boundedArgs polys
  , SD $ strategy "ints"                   boundedArgs ints

  -- ** Simplifications
  , SD $ strategy "dpsimps"                () dpsimps
  , SD $ strategy "cleanSuffix"            () cleanSuffix
  , SD $ strategy "decomposeIndependent"   () decomposeIndependent
  , SD $ strategy "decomposeIndependentSG" () decomposeIndependentSG
  , SD $ strategy "toDP"                   () toDP
  , SD $ strategy "removeLeaf"             (OneTuple complexityPairArg) removeLeaf

  -- ** Strategies
  , SD $ strategy "matchbounds"           () matchbounds

  , SD $ strategy "ara"                   boundedArgs araBounds


  , SD certifyDeclaration
  , SD derivationalDeclaration
  , SD runtimeDeclaration
  , SD competitionDeclaration
  , SD webCustomDeclaration
  , SD webAutomaticDeclaration
  ]

