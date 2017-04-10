-- Pretty.hs ---
--
-- Filename: Pretty.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Thu Sep  4 10:42:24 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sat Apr  8 15:22:34 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 60
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

module Tct.Trs.Processor.ARA.Exception.Pretty
    ( prettyProgException
    ) where

import           Tct.Trs.Processor.ARA.Constants
import           Tct.Trs.Processor.ARA.Exception.Type
import           Text.PrettyPrint

prettyProgException           :: ProgException -> Doc
prettyProgException ex = text (prefix ex) <> text (getElem ex)
    where
      prefix ShowTextOnly {}        = ""
      prefix SemanticException{}    = exceptionPrefixSemantic ++ " "
      prefix WarningException{}     = exceptionPrefixWarning ++ " "
      prefix FatalException{}       = exceptionPrefixFatal ++ " "
      prefix ParseException{}       = exceptionPrefixParse ++ " "
      prefix UnsolveableException{} = exceptionPrefixUnsolveable ++ " "

      getElem (ShowTextOnly x)         = x
      getElem (SemanticException x)    = x
      getElem (WarningException x)     = x
      getElem (FatalException x)       = x
      getElem (ParseException x)       = x
      getElem (UnsolveableException x) = x

--
-- Pretty.hs ends here
