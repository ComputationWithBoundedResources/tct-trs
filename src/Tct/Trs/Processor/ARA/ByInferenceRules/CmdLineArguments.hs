-- CommandLineArguments.hs ---
--
-- Filename: CommandLineArguments.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Thu Sep  4 12:25:37 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sat Apr  8 15:22:43 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 37
-- URL:
-- Doc URL:
-- Keywords:
-- Compatibility:
--
--

-- Commentary:
--
--
--
--

-- Change Log:
--
--
--

--
--

-- Code:

-- | Reexporting the modules in ./CmdLineArguments
module Tct.Trs.Processor.ARA.ByInferenceRules.CmdLineArguments
    (
     -- reexported modules
      module Tct.Trs.Processor.ARA.ByInferenceRules.CmdLineArguments.Type
    , module Tct.Trs.Processor.ARA.ByInferenceRules.CmdLineArguments.Parse
    ) where

import           Tct.Trs.Processor.ARA.ByInferenceRules.CmdLineArguments.Parse
import           Tct.Trs.Processor.ARA.ByInferenceRules.CmdLineArguments.Type


--
-- CmdLineArguments.hs ends here
