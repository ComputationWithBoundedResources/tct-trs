module Tct.Trs.Data.Mode
  (
  Problem (..)
  , trsMode
  , CC
  ) where



import           Tct.Core.Common.Error      (TctError(..))
import qualified Tct.Core.Common.Pretty     as PP
import           Tct.Core.Main
import           Tct.Core.Processor.Trivial (failing)

import           Tct.Common.Answer          (answering)

import qualified Data.Rewriting.Problem     as R

import Tct.Trs.Data.Problem


trsMode :: TctMode Problem CC
trsMode = TctMode
  { modeId              = "trs"
  , modeParser          = parser
  , modeStrategies      = []

  , modeDefaultStrategy = failing
  , modeOptions         = options
  , modeModifyer        = modifyer
  , modeAnswer          = answering }


data CC = DCF | DCI | RCF | RCI deriving (Eq, Read)

instance Show CC where
  show DCF = "DCF"
  show DCI = "DCI"
  show RCF = "RCF"
  show RCI = "RCI"


ccProperties :: CC -> (R.StartTerms, R.Strategy)
ccProperties cc = case cc of
  DCF -> (R.AllTerms,   R.Full)
  DCI -> (R.AllTerms,   R.Innermost)
  RCF -> (R.BasicTerms, R.Full)
  RCI -> (R.BasicTerms, R.Innermost)

parser :: String -> Either TctError Problem
parser s = case R.fromString s of
  Left e  -> Left $ TctParseError (show e)
  Right p -> Right $ fromRewriting p

options :: Options CC
options = option $ eopt
  `withArgLong` "complexity"
  `withCropped` 'c'
  `withHelpDoc` PP.text "RCF - runtime complexity"
  `withDefault` RCF

modifyer :: Problem -> CC -> Problem
modifyer p cc = p { startTerms = ts, strategy = st }
  where (ts,st) = ccProperties cc

