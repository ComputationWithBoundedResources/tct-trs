module Tct.Trs.Data.Mode
  (
  Problem (..)
  , TrsMode
  , trsMode
  , CC
  ) where


import qualified Data.Set                   as S

import           Tct.Core.Common.Error      (TctError (..))
import qualified Tct.Core.Common.Pretty     as PP
import qualified Tct.Core.Common.Xml        as Xml (putXml)
import           Tct.Core.Main
import qualified Tct.Core.Data as T
import           Tct.Core.Processor.Failing (failing)

import qualified Data.Rewriting.Problem     as R

import           Tct.Trs.Data.CeTA
import           Tct.Trs.Data.Problem
import           Tct.Trs.Data.ProblemKind
import           Tct.Trs.Data.Signature     (Signature)
import           Tct.Trs.Data.Trs           (Trs)
import qualified Tct.Trs.Data.Trs           as Trs
import           Tct.Trs.Processor          (defaultDeclarations)


type TrsMode = TctMode TrsProblem TrsProblem CC

trsMode :: TrsMode
trsMode = TctMode
  { modeId              = "trs"
  , modeParser          = parser
  , modeStrategies      = defaultDeclarations

  , modeDefaultStrategy = failing
  , modeOptions         = options
  , modeModifyer        = modifyer
  , modeAnswer          = answering }

-- TODO: MS: options for total or partial proof output
answering :: CC -> T.Return (ProofTree TrsProblem) -> IO ()
answering _ ret = case ret of
  T.Flop -> putStrLn "Flop`"
  r    -> PP.putPretty (answer pt) >> case totalProof pt of
    Left s    -> print s
    Right xml -> Xml.putXml xml
    where pt = T.fromReturn r

data CC = DCF | DCI | RCF | RCI deriving (Eq, Show, Read)

ccProperties :: CC -> Trs F V -> Signature F -> (StartTerms F, Strategy)
ccProperties cc trs sig = case cc of
  DCF -> (AllTerms fs,          Full)
  DCI -> (AllTerms fs,          Innermost)
  RCF -> (BasicTerms defs cons, Full)
  RCI -> (BasicTerms defs cons, Innermost)
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

modifyer :: CC -> TrsProblem -> TrsProblem
modifyer cc p = p { startTerms = ts, strategy = st }
  where (ts,st) = ccProperties cc (allComponents p) (signature p)

