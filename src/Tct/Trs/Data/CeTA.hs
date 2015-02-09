module Tct.Trs.Data.CeTA 
  (
  CertFail (..)
  , Result
  , totalProof
  , partialProof
  ) where


import qualified Data.Foldable as F
import Control.Applicative

import           Tct.Core.Common.Xml (Xml)
import qualified Tct.Core.Common.Xml as Xml
import qualified Tct.Core.Data as T

import qualified Tct.Common.CeTA as C

import Tct.Trs.Data.Problem
import Tct.Trs.Data.Xml ()


-- MS:
-- Assumption: CeTA 2.2
-- toCeTA proof constructs valid xml elements, and </unsupported> otherwise
-- toCeTA problem constructs a valid xml problem element, with the complextiyClass tag missing
-- 

data CertFail
  = Infeasible 
  | Unsupported String
  deriving Show

type Result r = Either CertFail r

isFeasible :: Bool -> T.ProofTree l -> Result Xml.XmlContent
isFeasible allowPartial pt
  | allowPartial = k $ T.timeUB (T.certificateWith pt $ T.timeUBCert T.constant)
  | otherwise    = k $ T.timeUB (T.certificate pt)
  where 
    k (T.Poly (Just n)) = Right $ Xml.elt "polynomial" [Xml.int n]
    k _                 = Left Infeasible

cetaProblem :: Xml.Xml prob => Bool -> prob -> T.ProofTree t -> Result Xml.XmlContent
cetaProblem allowPartial prob pt = do
  c <- isFeasible allowPartial pt
  return $ Xml.addChildren (Xml.toCeTA prob) [c]

cetaSubProblem :: Xml.Xml t => Bool -> T.ProofTree t -> Result Xml.XmlContent
cetaSubProblem allowPartial pt@(T.Open prob)       = cetaProblem allowPartial prob pt
cetaSubProblem allowPartial pt@(T.NoProgress pn _) = cetaProblem allowPartial (T.problem pn) pt
cetaSubProblem allowPartial pt@(T.Progress pn _ _) = cetaProblem allowPartial (T.problem pn) pt

isCertifiable :: Xml.XmlContent -> Bool
isCertifiable c = Xml.rootTag c /= "unsupported"

-- | @partialProof pt@ translates unsupported techniques using `CeTA.unknownProof` and `CeTA.complextityAssumption` for open
-- problems. Here we assume a constant bound for open problems. Returns
-- 
--   * @Left 'CertFail'@ if the sub-problem is not feasible, and * @Right xml@ otherwise.
partialProof :: (Ord f, Ord v, Xml f, Xml v) => T.ProofTree (Problem f v) -> Result Xml.XmlDocument
partialProof pt = isFeasible True pt *> (toDoc <$> subProblem pt <*> partialProofM1 pt)
  where
    toDoc a b = C.cetaDocument (C.certificationProblem a b)
    subProblem = cetaSubProblem True
    mkAssumption n = Xml.elt "complexityAssumption" . (:[]) <$> subProblem n

    partialProofM1 r = C.complexityProof <$> partialProofM2 r
    partialProofM2 n@(T.Open _)           = mkAssumption n
    partialProofM2 (T.NoProgress _ spt)   = partialProofM2 spt
    partialProofM2 (T.Progress pn _ spts) = case F.toList spts of
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
totalProof pt = isFeasible False pt *> (toDoc <$> subProblem pt <*> totalProofM1 pt)
  where
    toDoc a b = C.cetaDocument (C.certificationProblem a b)
    subProblem = cetaSubProblem False

    totalProofM1 r = C.complexityProof <$> totalProofM2 r
    totalProofM2 (T.Open _)             = Left $ Unsupported "open problem"
    totalProofM2 (T.NoProgress _ spt)   = totalProofM2 spt
    totalProofM2 (T.Progress pn _ spts) = case F.toList spts of
      []  | isCertifiable xmlpn -> return xmlpn
      [t] | isCertifiable xmlpn -> Xml.addChildren xmlpn . (:[]) <$> totalProofM1 t
      _   -> Left $ Unsupported (show $ T.processor pn)
      where xmlpn = Xml.toCeTA (T.proof pn)
  
