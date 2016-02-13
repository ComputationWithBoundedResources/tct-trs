-- | The competition strategy. Wrapper for default runtime/derivational complexity.
module Tct.Trs.Strategy.Competition
  ( competition
  , competitionDeclaration
  , competitionStrategy
  ) where


import           Tct.Core
import           Tct.Core.Data                 (deflFun)

import           Tct.Trs.Data
import           Tct.Trs.Data.Problem          (isRCProblem)
import           Tct.Trs.Processors
import           Tct.Trs.Strategy.Derivational
import           Tct.Trs.Strategy.Runtime


-- | Declaration for "competition" strategy.
competitionDeclaration :: Declaration ('[] :-> TrsStrategy)
competitionDeclaration = strategy "competition" () competitionStrategy

-- | Default competition strategy.
competition :: TrsStrategy
competition = deflFun competitionDeclaration

competitionStrategy :: TrsStrategy
competitionStrategy =
  withProblem $ \p ->
    if isRCProblem p
      then runtime' Best
      else derivational

