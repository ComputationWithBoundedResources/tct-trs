-- | This module provides the custom strategy for the web interface.
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module Tct.Trs.Strategy.WebAutomatic where

import Tct.Core
import Tct.Trs.Strategy.Competition

-- currently set to competition strategy. like it was before.
webAutomatic = strategy "automatic" () competitionStrategy 


