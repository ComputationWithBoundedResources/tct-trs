module Tct.Trs.Data.CeTA
  (
  CertFail (..)
  , Result
  -- * prover methods
  , totalProof
  , partialProof

  -- * IO prover
  , totalProofIO
  , partialProofIO
  , totalProofIO'
  , partialProofIO'
  ) where


import qualified Control.Exception    as E (bracket)
import           Control.Monad.Trans  (MonadIO, liftIO)
import           System.Exit
import           System.IO            (hClose)
import           System.IO.Temp       (openTempFile)
import           System.Process       (readProcessWithExitCode)

import           Tct.Core.Common.Xml  as Xml


import           Control.Applicative
import qualified Data.Foldable        as F

import qualified Tct.Core.Data        as T

import qualified Tct.Common.CeTA      as C

import           Tct.Trs.Data.Problem

-- MS:
-- Assumption: CeTA 2.2
-- toCeTA proof constructs valid xml elements, and </unsupported> otherwise
-- toCeTA problem constructs a valid xml problem element, with the complextiyClass tag missing

data CertFail
  = Infeasible
  | Unsupported String
  deriving Show

type Result r = Either CertFail r

data Proof = TotalProof | PartialProof deriving Eq

isFeasible :: Bool -> T.ProofTree l -> Result Xml.XmlContent
isFeasible partial pt
  | partial   = k $ T.timeUB (T.certificateWith pt $ T.timeUBCert T.constant)
  | otherwise = k $ T.timeUB (T.certificate pt)
  where
    k (T.Poly (Just n)) = Right $ Xml.elt "polynomial" [Xml.int n]
    k _                 = Left Infeasible

cetaProblem :: Xml.Xml prob => Bool -> prob -> T.ProofTree t -> Result Xml.XmlContent
cetaProblem partial prob pt = do
  c <- isFeasible partial pt
  return $ Xml.addChildren (Xml.toCeTA prob) [c]

cetaSubProblem :: Xml.Xml t => Bool -> T.ProofTree t -> Result Xml.XmlContent
cetaSubProblem partial pt@(T.Open prob)      = cetaProblem partial prob pt
cetaSubProblem partial pt@(T.Success pn _ _) = cetaProblem partial (T.problem pn) pt
cetaSubProblem _ _                           = Left Infeasible

isCertifiable :: Xml.XmlContent -> Bool
isCertifiable c = Xml.rootTag c /= "unsupported"

-- | @partialProof pt@ translates unsupported techniques using `CeTA.unknownProof` and `CeTA.complextityAssumption` for open
-- problems. Here we assume a constant bound for open problems. Returns
--
--   * @Left 'CertFail'@ if the sub-problem is not feasible, and * @Right xml@ otherwise.
partialProof :: (Ord f, Ord v, Xml f, Xml v) => T.ProofTree (Problem f v) -> Result Xml.XmlDocument
partialProof pt = toDoc <$> partialProofM1 pt <*> subProblem pt
  where
    toDoc b a = C.cetaDocument (C.certificationProblem a b)
    subProblem = cetaSubProblem True
    mkAssumption n = Xml.elt "complexityAssumption" . (:[]) <$> subProblem n

    partialProofM1 r = C.complexityProof <$> partialProofM2 r
    partialProofM2 n@(T.Open _)          = mkAssumption n
    partialProofM2 (T.Failure _)         = Left Infeasible
    partialProofM2 (T.Success pn _ spts) = case F.toList spts of
      []  | isCertifiable xmlpn -> return xmlpn
      [t] | isCertifiable xmlpn -> Xml.addChildren xmlpn . (:[]) <$> partialProofM1 t
      ts                        -> C.unknownProof "description" <$> subProblem pt  <*> mapM mkSubProofs ts
      where
        xmlpn   = Xml.toCeTA (T.proof pn)
        mkSubProofs spt = C.subProof <$> subProblem spt <*> partialProofM1 spt


-- | @totalProof pt@ returns
--   * @Left 'CertFail'@ if the problem is not feasible, or an unsupported technique has been used,
--   * @Right xml@ otherwise.
totalProof :: (Ord f, Ord v, Xml f, Xml v) => T.ProofTree (Problem f v) -> Result Xml.XmlDocument
totalProof pt = toDoc <$> totalProofM1 pt <*> subProblem pt
  where
    toDoc a b = C.cetaDocument (C.certificationProblem b a)
    subProblem = cetaSubProblem False

    totalProofM1 r = C.complexityProof <$> totalProofM2 r
    totalProofM2 (T.Open _)            = Left $ Unsupported "open problem"
    totalProofM2 (T.Failure _)         = Left $ Unsupported "failure"
    totalProofM2 (T.Success pn _ spts) = case F.toList spts of
      []  | isCertifiable xmlpn -> return xmlpn
      [t] | isCertifiable xmlpn -> Xml.addChildren xmlpn . (:[]) <$> totalProofM1 t
      _   -> Left $ Unsupported (show $ T.appliedProcessor pn)
      where xmlpn = Xml.toCeTA (T.proof pn)


--- * io -------------------------------------------------------------------------------------------------------------

proofIO :: MonadIO m => FilePath -> (l -> Either CertFail XmlDocument) -> Proof -> l -> m (Either String l)
proofIO tmpDir prover allowPartial p =
  case prover p of
    Left err -> return $ Left (show err)
    Right xml       ->
      liftIO . withFile $ \file hfile -> do
        Xml.putXmlHandle xml hfile
        hClose hfile
        (code , stdout, stderr) <- readProcessWithExitCode "ceta" (args [file]) ""
        return $ case code of
          ExitFailure i -> Left $ "Error(" ++ show i ++ "," ++ stderr ++ ")"
          ExitSuccess   -> case lines stdout of
            "CERTIFIED <complexityProof>" :_ -> Right p
            _                                -> Left stdout
  where
    args = if allowPartial == PartialProof then ("--allow-assumptions":) else id
    withFile = E.bracket (openTempFile tmpDir "ceta") (hClose . snd) . uncurry

totalProofIO :: (MonadIO m, Ord f, Ord v, Xml f, Xml v, l ~ T.ProofTree (Problem f v)) => l -> m (Either String l)
totalProofIO = totalProofIO' "/tmp"

partialProofIO :: (MonadIO m, Ord f, Ord v, Xml f, Xml v, l ~ T.ProofTree (Problem f v)) => l -> m (Either String l)
partialProofIO = partialProofIO' "/tmp"

totalProofIO' :: (MonadIO m, Ord f, Ord v, Xml f, Xml v, l ~ T.ProofTree (Problem f v)) => FilePath -> l -> m (Either String l)
totalProofIO' tmpDir = proofIO tmpDir totalProof TotalProof

partialProofIO' :: (MonadIO m, Ord f, Ord v, Xml f, Xml v, l ~ T.ProofTree (Problem f v)) => FilePath -> l -> m (Either String l)
partialProofIO' tmpDir = proofIO tmpDir partialProof PartialProof

