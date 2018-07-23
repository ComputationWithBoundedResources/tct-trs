-- | The competition strategy. Wrapper for default runtime/derivational complexity.
--
-- termcomp 2017:
--  * rc/rci
--    * add amortized analysis
-- termcomp 2018:
--  * certification: 
--    * compute more precise bounds of MIs
--    * add automaton based maximal matrix MI
module Tct.Trs.Strategy.Competition
  ( competition
  , competition'
  , competitionDeclaration
  ) where


import Tct.Core
import Tct.Core.Data                 (declFun, deflFun)
import Tct.Core.Processor.MSum       (madd)

import Tct.Trs.Data
import Tct.Trs.Data.Problem          (isRCProblem)
import Tct.Trs.Processors
import Tct.Trs.Strategy.Derivational
import Tct.Trs.Strategy.Runtime


-- | Declaration for "competition" strategy.
competitionDeclaration :: Declaration ('[Argument 'Optional CombineWith] :-> TrsStrategy)
competitionDeclaration = strategy "competition" (OneTuple cmb) competitionStrategy
  where cmb = combineWithArg `optional` Fastest

-- | Default competition strategy.
competition :: TrsStrategy
competition = deflFun competitionDeclaration

-- | Default competition strategy.
competition' :: CombineWith -> TrsStrategy
competition' = declFun competitionDeclaration

competitionStrategy :: CombineWith -> TrsStrategy
competitionStrategy cmb =
  withProblem $ \p ->
    if isRCProblem p
      then timeoutIn 5 decreasingLoops `madd`
           runtime' cmb
      else derivational

