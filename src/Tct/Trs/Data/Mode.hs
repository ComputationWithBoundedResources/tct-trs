{- | This module provides a Tct configuration for Trs problems.

The configuration is meant to work with 'Tct.Core.Main.tct3'

  * sets the parser to standard @xml@ / @wst@ format
  * sets default strategies
  * provides the @--complexity <rc|rci|dc|dci>@ argument to set the complexity problem
    * this argument overrides the complexity problem returned by the parser
  * provides @--ceta <total|partial>@ argument to set the complexity problem
-}
module Tct.Trs.Data.Mode
  (
  trs
  -- * Problem parser
  , parserIO
  , parser
  -- * Trs Configuration
  , TrsConfig
  , trsConfig
  -- * Trs Options
  , TrsOptions
  , trsOptions
  -- * Trs update hook
  , trsUpdate
  ) where


import           Control.Applicative
import           System.FilePath            (takeExtension)

import qualified Tct.Core.Common.Pretty     as PP
import qualified Tct.Core.Common.Xml        as Xml (putXml)
import qualified Tct.Core.Data              as T
import           Tct.Core.Main
import           Tct.Core

import qualified Data.Rewriting.Problem     as R
import qualified Data.Rewriting.Problem.Xml as R

import           Tct.Trs.Data.CeTA
import           Tct.Trs.Data.Problem
import           Tct.Trs.Declarations        (trsDeclarations)


trs :: TrsConfig -> IO ()
trs = tct3WithOptions trsUpdate trsOptions

-- | Parses a TrsProblem. Uses the @xml@ format if the file extension is @xml@, otherwise the @WST@ format.
parserIO :: FilePath -> IO (Either String TrsProblem)
parserIO fn
  | takeExtension fn == ".xml" = fromRewriting <$> R.xmlFileToProblem fn
  | otherwise                  = parser <$> readFile fn

-- | @WST@ format parser from 'Data.Rewriting'.
parser :: String -> Either String TrsProblem
parser s = case R.fromString s of
  Left e  -> Left (show e)
  Right p -> fromRewriting p


-- | The Tct configuration type for Trs.
type TrsConfig = TctConfig TrsProblem

-- | Default Tct configuration for Trs.
-- Sets the @xml@ / @wst@ parser. Sets a list of default strategies.
trsConfig :: TrsConfig
trsConfig = defaultTctConfig parserIO
  `addStrategies` trsDeclarations
  `appendGHCiScript`
    [ ":module +Tct.Trs.Processors"
    , ":module +Tct.Trs.Interactive"]

-- | Trs specific command line arguments.
data TrsOptions =  TrsOptions (Maybe CC) (Maybe CP)

-- | Trs specific command line options.
trsOptions :: Options TrsOptions
trsOptions = TrsOptions
  <$> alt (option' readCC (eopt
    `withArgLong` "complexity"
    `withHelpDoc` PP.listing
      [ (PP.text (show DC)  , PP.text "derivational complexity")
      , (PP.text (show DCI) , PP.text "derivational complexity innermost")
      , (PP.text (show RC)  , PP.text "runtime complexity")
      , (PP.text (show RCI) , PP.text "runtime complexity innermost") ] ))
  <*> alt (option' readCP (eopt
      `withArgLong` "ceta"
      `withHelpDoc` PP.listing
        [ (PP.text (show TotalProof)   , PP.text "outputs the proof in the CeTA format")
        , (PP.text (show PartialProof) , PP.text "outputs the proof in the CeTA (partial) format") ]))

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
  show cc = case cc of { TotalProof -> "total"; PartialProof -> "partial" }

readCP :: Monad m => String -> m CP
readCP cp
  | cp == show TotalProof   = return TotalProof
  | cp == show PartialProof = return PartialProof
  | otherwise               = fail $ "Tct.Trs.Data.Mode:" ++ cp


-- | Update hook for options
-- Updates the parsed problem if a @complexity@ argument is set.
-- Updates the proof output if the @proofOUtput@ argument is set.
trsUpdate :: TrsConfig -> TrsOptions -> TrsConfig
trsUpdate cfg (TrsOptions ccM cpM) = setParseProblem $ setPutProof cfg
  where
    setParseProblem cfg' = cfg' { parseProblem = \fp -> fmap (updateCC ccM) <$> parseProblem cfg' fp }
    setPutProof cfg'     = cfg' { putProof     = proofing cpM }

    updateCC cc = case cc of
      Nothing    -> id
      (Just DC)  -> toDC . toFull
      (Just DCI) -> toDC . toInnermost
      (Just RC)  -> toRC . toFull
      (Just RCI) -> toRC . toInnermost
    proofing cp ret = case cp of
      Nothing  -> putProof cfg ret
      Just cp' -> case ret of
        T.Halt _  -> PP.putPretty $ PP.text "MAYBE"
        r         -> case prover pt of
          Left s    -> print s
          Right xml -> Xml.putXml xml
          where
            pt     = T.fromReturn r
            prover = if cp' == TotalProof then totalProof else partialProof

