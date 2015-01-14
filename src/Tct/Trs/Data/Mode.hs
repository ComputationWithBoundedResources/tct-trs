module Tct.Trs.Data.Mode
  (
  Problem (..)
  , trsMode
  , CC
  ) where


import qualified Data.Set                   as S

import           Tct.Core.Common.Error      (TctError (..))
import qualified Tct.Core.Common.Pretty     as PP
import           Tct.Core.Main
import           Tct.Core.Processor.Trivial (failing)

import qualified Data.Rewriting.Problem     as R

import           Tct.Trs.Data.Problem
import           Tct.Trs.Data.Trs


trsMode :: TctMode Problem CC
trsMode = TctMode
  { modeId              = "trs"
  , modeParser          = parser
  , modeStrategies      = []

  , modeDefaultStrategy = failing
  , modeOptions         = options
  , modeModifyer        = modifyer
  , modeAnswer          = const $ return () }


data CC = DCF | DCI | RCF | RCI deriving (Eq, Read)

instance Show CC where
  show DCF = "DCF"
  show DCI = "DCI"
  show RCF = "RCF"
  show RCI = "RCI"

ccProperties :: CC -> Trs -> Signature -> (StartTerms, Strategy)
ccProperties cc trs sig = case cc of
  DCF -> (AllTerms fs          , Full)
  DCI -> (AllTerms fs          , Innermost)
  RCF -> (BasicTerms defs cons , Full)
  RCI -> (BasicTerms defs cons , Innermost)
  where
    fs   = defs `S.union` cons
    defs = mkDefinedSymbols trs
    cons = mkConstructorSymbols sig defs

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
  where (ts,st) = ccProperties cc (allComponents p) (signature p)

