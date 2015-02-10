-- | A handy wrapper for the smt solver.
module Tct.Trs.Data.SMT
  (module SMT
  , minismt
  ) where


import           Tct.Common.SMT as SMT hiding (minismt)
import qualified Tct.Core.Data  as T


minismt :: SolverStM (Formula IFormula) (Decoder res) -> T.TctM (Result res)
minismt fm = do
  tmp <- T.tempDirectory `fmap` T.askState
  SMT.solveStM (minismt' (opts tmp)) fm
  where opts tmp = (defaultOptions ["-m", "-v2"]) {tmpDir = Just tmp}

