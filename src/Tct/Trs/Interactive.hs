-- | This module re-exports 'Tct.Core.Interactive' and provide Trs specific commands.
module Tct.Trs.Interactive
  ( module M

  , loadTrs
  , loadDC
  , loadRC
  , loadDCI
  , loadRCI

  , wdg
  ) where


import           Control.Applicative
import qualified Tct.Core.Common.Pretty as PP
import           Tct.Core.Interactive   as M
import qualified Tct.Core.Main          as T

import           Tct.Trs.Config         (trsConfig)
import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem   as Prob


loadX :: (TrsProblem -> TrsProblem) -> FilePath -> IO ()
loadX k fp = load parse fp >> printState
  where parse fp' = fmap k <$> T.parseProblem trsConfig fp'

-- | Load a Trs problem. Uses the parser defined in 'trsConfig'.
loadTrs, loadDC, loadDCI, loadRC, loadRCI :: FilePath -> IO ()
loadTrs = loadX id
loadDC  = loadX (Prob.toDC . Prob.toFull)
loadDCI = loadX (Prob.toDC . Prob.toInnermost)
loadRC  = loadX (Prob.toRC . Prob.toFull)
loadRCI = loadX (Prob.toRC . Prob.toInnermost)

wdg :: IO ()
wdg = onProblems $ PP.putPretty . (Prob.dependencyGraph :: TrsProblem -> DG F V)

