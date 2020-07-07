-- | This module provides Trs specific commands for the interactive mode.
module Tct.Trs.Interactive
  ( module M

  , loadTrs
  , loadDC
  , loadRC
  , loadDCI
  , loadRCI

  , parseTrs
  , listTrs

  , wdg
  ) where


import           Tct.Trs.Processors     as M
import           Tct.Trs.Strategies     as M

import           Tct.Core.Interactive
import qualified Tct.Core.Common.Pretty as PP
import qualified Tct.Core.Data          as T
import qualified Tct.Core.Main          as T

import           Tct.Trs.Config         (trsConfig)
import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem   as Prob


loadX :: T.Declared Trs Trs => (Trs -> Trs) -> FilePath -> IO ()
loadX k fp = load pars fp >> state
  where pars fp' = fmap k <$> T.parseProblem trsConfig fp'

-- | Load a Trs problem. Uses the parser defined in 'trsConfig'.
-- WARNING: this fails when T.Declared Trs Trs is not defined
loadTrs, loadDC, loadDCI, loadRC, loadRCI :: T.Declared Trs Trs => FilePath -> IO ()
loadTrs = loadX id
loadDC  = loadX (Prob.toDC . Prob.toFull)
loadDCI = loadX (Prob.toDC . Prob.toInnermost)
loadRC  = loadX (Prob.toRC . Prob.toFull)
loadRCI = loadX (Prob.toRC . Prob.toInnermost)

wdg :: IO ()
wdg = onProblems $ PP.putPretty . (Prob.dependencyGraph :: Trs -> DG F V)

-- | Parse 'Trs' strategy. Specialised version of 'parse'.
parseTrs :: T.Declared Trs Trs => String -> T.Strategy Trs Trs
parseTrs = parse (T.decls :: [T.StrategyDeclaration Trs Trs])

-- | List 'Trs' strategies. Specialised version of 'list'.
listTrs :: T.Declared Trs Trs => IO ()
listTrs = list (T.decls :: [T.StrategyDeclaration Trs Trs])

