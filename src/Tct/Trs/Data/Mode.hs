module Tct.Trs.Data.Mode
  (
  Problem (..)
  , trsMode
  , CC
  ) where


import qualified Data.Set                   as S

import           Tct.Core.Common.Error      (TctError (..))
import qualified Tct.Core.Common.Pretty     as PP
import qualified Tct.Core.Common.Xml        as Xml (putXml)
import           Tct.Core.Data              (ProofTree)
import           Tct.Core.Main
import           Tct.Core.Processor.Trivial (failing)

import qualified Data.Rewriting.Problem     as R

import           Tct.Trs.Data.CeTA
import           Tct.Trs.Data.Problem
import           Tct.Trs.Data.Trs (Trs, Signature)
import qualified Tct.Trs.Data.Trs as Trs
import           Tct.Trs.Data.Xml           ()


trsMode :: TctMode TrsProblem CC
trsMode = TctMode
  { modeId              = "trs"
  , modeParser          = parser
  , modeStrategies      = []

  , modeDefaultStrategy = failing
  , modeOptions         = options
  , modeModifyer        = modifyer
  , modeAnswer          = answering }

answering :: ProofTree TrsProblem -> IO ()
answering pt = case cetaOutput pt of
  Left s    -> putStrLn s
  Right xml -> Xml.putXml xml

data CC = DCF | DCI | RCF | RCI deriving (Eq, Read)

instance Show CC where
  show DCF = "DCF"
  show DCI = "DCI"
  show RCF = "RCF"
  show RCI = "RCI"

ccProperties :: CC -> Trs F V -> Signature F -> (StartTerms F, Strategy)
ccProperties cc trs sig = case cc of
  DCF -> (AllTerms fs          , Full)
  DCI -> (AllTerms fs          , Innermost)
  RCF -> (BasicTerms defs cons , Full)
  RCI -> (BasicTerms defs cons , Innermost)
  where
    fs   = defs `S.union` cons
    defs = Trs.definedSymbols trs
    cons = Trs.constructorSymbols sig defs

parser :: String -> Either TctError TrsProblem
parser s = case R.fromString s of
  Left e  -> Left $ TctParseError (show e)
  Right p -> Right $ fromRewriting p

options :: Options CC
options = option $ eopt
  `withArgLong` "complexity"
  `withCropped` 'c'
  `withHelpDoc` PP.text "RCF - runtime complexity"
  `withDefault` RCF

modifyer :: TrsProblem -> CC -> TrsProblem
modifyer p cc = p { startTerms = ts, strategy = st }
  where (ts,st) = ccProperties cc (allComponents p) (signature p)

