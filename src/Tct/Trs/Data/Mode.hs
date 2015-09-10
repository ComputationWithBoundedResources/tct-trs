module Tct.Trs.Data.Mode
  (
    TrsMode
  , trsMode
  , TrsOptions
  ) where


import           Control.Applicative
import           System.FilePath            (takeExtension)

import qualified Tct.Core.Common.Pretty     as PP
import qualified Tct.Core.Common.Xml        as Xml (putXml)
import qualified Tct.Core.Data              as T
import           Tct.Core.Main
import           Tct.Core.Processor.Failing (failing)

import qualified Data.Rewriting.Problem     as R
import qualified Data.Rewriting.Problem.Xml as R

import           Tct.Trs.Data.CeTA
import           Tct.Trs.Data.Problem
import           Tct.Trs.Processor          (defaultDeclarations)


type TrsMode = TctMode TrsProblem TrsProblem TrsOptions

trsMode :: TrsMode
trsMode = TctMode
  { modeId              = "trs"
  , modeParser          = parserIO
  , modeStrategies      = defaultDeclarations

  , modeDefaultStrategy = failing
  , modeOptions         = options
  , modeModifyer        = modifyer
  , modeAnswer          = \_ _  -> return ()
  , modeProof           = proofing }

-- | Parses a TrsProblem. Uses the @xml@ format if the file extension is @xml@, otherwise the WST format.
parserIO :: FilePath -> IO (Either String TrsProblem)
parserIO fn 
  | takeExtension fn == ".xml" = fromRewriting <$> R.xmlFileToProblem fn
  | otherwise                  = parser <$> readFile fn

-- | WST format parser from 'Data.Rewriting'.
parser :: String -> Either String TrsProblem
parser s = case R.fromString s of
  Left e  -> Left (show e)
  Right p -> fromRewriting p

-- | Trs specific command line options.
options :: Options TrsOptions
options = TrsOptions
  <$> alt (option' readCC (eopt
    `withArgLong` "complexity"
    `withCropped` 'c'
    `withHelpDoc` PP.listing
      [ (PP.text (show DC)  , PP.text "derivational complexity")
      , (PP.text (show DCI) , PP.text "derivational complexity innermost")
      , (PP.text (show RC)  , PP.text "runtime complexity")
      , (PP.text (show RCI) , PP.text "runtime complexity innermost") ] ))
  <*> option' readCP (eopt
      `withArgLong` "proofOutput"
      `withCropped` 'b'
      `withHelpDoc` PP.listing
        [ (PP.text (show TotalProof)   , PP.text "outputs the answer and then the CeTA proof")
        , (PP.text (show PartialProof) , PP.text "outputs the answer and then the CeTA (partial) proof") ]
      `withDefault` TotalProof)

-- | Sets complexity problem.
modifyer :: TrsOptions -> TrsProblem -> TrsProblem
modifyer (TrsOptions cc _) = updateCC cc

-- | CeTA (partial proof output)
proofing :: TrsOptions -> T.Return (ProofTree TrsProblem) -> IO ()
proofing (TrsOptions _ cp) ret = case ret of
  T.Halt _  -> PP.putPretty $ PP.text "MAYBE"
  r         -> case prover pt of
    Left s    -> print s
    Right xml -> Xml.putXml xml
    where
      pt     = T.fromReturn r
      prover = if cp == TotalProof then totalProof else partialProof


data TrsOptions =  TrsOptions (Maybe CC) CP

data CC = DC | DCI | RC | RCI deriving Eq

instance Show CC where
  show cc = case cc of { DC -> "dc"; DCI -> "dci"; RC -> "rc"; RCI -> "rci" }

readCC :: Monad m => String -> m CC
readCC cc
  | cc == show DC  = return DC
  | cc == show DCI = return DCI
  | cc == show RC  = return RC
  | cc == show RCI = return RCI
  | otherwise      =  fail $ "Tct.Trs.Data.Mode.readCC: " ++ cc

data CP = TotalProof | PartialProof deriving Eq

instance Show CP where
  show cc = case cc of { TotalProof -> "totalProof"; PartialProof -> "partialProof" }

readCP :: Monad m => String -> m CP
readCP cp
  | cp == show TotalProof   = return TotalProof
  | cp == show PartialProof = return PartialProof
  | otherwise               = fail $ "Tct.Trs.Data.Mode:" ++ cp

updateCC :: Maybe CC -> TrsProblem -> TrsProblem
updateCC cc = case cc of
  Nothing    -> id
  (Just DC)  -> toDC . toFull
  (Just DCI) -> toDC . toInnermost
  (Just RC)  -> toRC . toFull
  (Just RCI) -> toRC . toInnermost
