-- | This module extends 'Tct.Core.Interactive' with TRS specific commands.
module Tct.Trs.Interactive
  ( loadDC
  , loadRC
  , loadIDC
  , loadIRC

  , wdg
  ) where


import           Tct.Core.Interactive
import qualified Tct.Core.Main        as T
import qualified Tct.Core.Common.Pretty as PP

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem as Prob


loadX :: T.TctMode TrsProblem o -> FilePath -> (TrsProblem -> TrsProblem) -> IO ()
loadX tm f k = load tm f >> modifyProblem k >> state

loadDC, loadIDC, loadRC, loadIRC :: T.TctMode TrsProblem o -> FilePath -> IO ()
loadDC tm f  = loadX tm f (Prob.toDC . Prob.toFull)
loadIDC tm f = loadX tm f (Prob.toDC . Prob.toInnermost)
loadRC tm f  = loadX tm f (Prob.toRC . Prob.toFull)
loadIRC tm f = loadX tm f (Prob.toRC . Prob.toInnermost)

wdg :: IO ()
wdg = onProblem $ PP.putPretty . (Prob.dependencyGraph :: TrsProblem -> DG F V)

