module Tct.Trs.Data.Mode
  (
    TrsMode
  , trsMode
  , TrsOptions
  ) where


import           Control.Applicative
import qualified Data.Set                   as S

import           Tct.Core.Common.Error      (TctError (..))
import qualified Tct.Core.Common.Pretty     as PP
import qualified Tct.Core.Common.Xml        as Xml (putXml)
import qualified Tct.Core.Data              as T
import           Tct.Core.Main
import           Tct.Core.Processor.Failing (failing)

import qualified Data.Rewriting.Problem     as R

import           Tct.Trs.Data.CeTA
import           Tct.Trs.Data.Problem
import           Tct.Trs.Data.ProblemKind
import           Tct.Trs.Data.Signature     (Signature)
import           Tct.Trs.Data.Trs           (Trs)
import qualified Tct.Trs.Data.Trs           as Trs
import           Tct.Trs.Processor          (defaultDeclarations)


type TrsMode = TctMode TrsProblem TrsProblem TrsOptions

trsMode :: TrsMode
trsMode = TctMode
  { modeId              = "trs"
  , modeParser          = parser
  , modeStrategies      = defaultDeclarations

  , modeDefaultStrategy = failing
  , modeOptions         = options
  , modeModifyer        = modifyer
  , modeAnswer          = answering }

-- | WST format parser from 'Data.Rewriting'.
parser :: String -> Either TctError TrsProblem
parser s = case R.fromString s of
  Left e  -> Left $ TctParseError (show e)
  Right p -> Right $ fromRewriting p

-- | Trs specific command line options.
options :: Options TrsOptions
options = TrsOptions
  <$> option' readCC (eopt
    `withArgLong` "complexity"
    `withCropped` 'c'
    `withHelpDoc` PP.listing
      [ (PP.text "dc"  , PP.text "derivational complexity")
      , (PP.text "dci" , PP.text "derivational complexity innermost")
      , (PP.text "rc"  , PP.text "runtime complexity")
      , (PP.text "rci" , PP.text "runtime complexity innermost") ]
    `withDefault` RCI)
  <*> option' readCP (eopt
      `withArgLong` "proofOutput"
      `withCropped` 'p'
      `withHelpDoc` PP.listing
        [ (PP.text "totalProof"   , PP.text "outputs the answer and then the CeTA proof")
        , (PP.text "partialProof" , PP.text "outputs the answer and then the CeTA (partial) proof") ]
      `withDefault` TotalProof)

-- | Sets complexity problem.
modifyer :: TrsOptions -> TrsProblem -> TrsProblem
modifyer (TrsOptions cc _) p = p { startTerms = ts, strategy = st }
  where (ts,st) = ccProperties cc (allComponents p) (signature p)

-- | CeTA (partial proof output)
answering :: TrsOptions -> T.Return (ProofTree TrsProblem) -> IO ()
answering (TrsOptions _ cp) ret = case ret of
  T.Halt _  -> PP.putPretty T.MaybeAnswer
  r         -> PP.putPretty (answer pt) >> case prover pt of
    Left s    -> print s
    Right xml -> Xml.putXml xml
    where
      pt = T.fromReturn r
      prover = if cp == TotalProof then totalProof else partialProof


data TrsOptions =  TrsOptions CC CP

data CC = DC | DCI | RC | RCI deriving Eq

instance Show CC where
  show cc = case cc of { DC -> "dc"; DCI -> "dci"; RC -> "rc"; RCI -> "rci" }

readCC :: Monad m => String -> m CC
readCC cc
  | cc == show DC  = return DC
  | cc == show DCI = return DCI
  | cc == show DC  = return DC
  | cc == show DCI = return DCI
  | otherwise      =  fail $ "Tct.Trs.Data.Mode.readCC: " ++ cc

data CP = TotalProof | PartialProof deriving Eq

instance Show CP where
  show cc = case cc of { TotalProof -> "totalProof"; PartialProof -> "partialProof" }

readCP :: Monad m => String -> m CP
readCP cp
  | cp == show TotalProof   = return TotalProof
  | cp == show PartialProof = return PartialProof
  | otherwise               = fail $ "Tct.Trs.Data.Mode:" ++ cp

ccProperties :: CC -> Trs F V -> Signature F -> (StartTerms F, Strategy)
ccProperties cc trs sig = case cc of
  DC  -> (AllTerms fs,          Full)
  DCI -> (AllTerms fs,          Innermost)
  RC  -> (BasicTerms defs cons, Full)
  RCI -> (BasicTerms defs cons, Innermost)
  where
    fs   = defs `S.union` cons
    defs = Trs.definedSymbols trs
    cons = Trs.constructorSymbols sig defs

