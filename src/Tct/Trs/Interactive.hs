-- | This module extends 'Tct.Core.Interactive' with TRS specific commands.
module Tct.Trs.Interactive
  ( loadDC
  , loadRC
  , loadIDC
  , loadIRC
  ) where


import           Tct.Core.Interactive
import qualified Tct.Core.Main        as T

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem as Prob


loadDC, loadIDC, loadRC, loadIRC :: T.TctMode TrsProblem o -> FilePath -> IO ()
loadDC tm f  = load tm f >> modifyProblem (Prob.toDC . Prob.toFull      :: TrsProblem -> TrsProblem)
loadIDC tm f = load tm f >> modifyProblem (Prob.toDC . Prob.toInnermost :: TrsProblem -> TrsProblem)
loadRC tm f  = load tm f >> modifyProblem (Prob.toRC . Prob.toFull      :: TrsProblem -> TrsProblem)
loadIRC tm f = load tm f >> modifyProblem (Prob.toRC . Prob.toInnermost :: TrsProblem -> TrsProblem)

