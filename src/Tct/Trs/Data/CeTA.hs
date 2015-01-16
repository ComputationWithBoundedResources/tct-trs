module Tct.Trs.Data.CeTA 
  ( cetaOutput
  ) where


import qualified Data.Foldable as F

import qualified Tct.Core.Common.Xml as Xml
import qualified Tct.Core.Data as T

import qualified Tct.Common.CeTA as C

import Tct.Trs.Data.Problem
import Tct.Trs.Data.Xml ()

import Debug.Trace


certifiable :: [String]
certifiable = ["rIsEmpty"]

cetaOutput :: T.ProofTree Problem -> Either String Xml.XmlDocument
cetaOutput pt = case T.timeUB (T.certificate pt) of
  T.Poly (Just _) -> Right . C.cetaDocument $ C.certificationProblem (cetaSubProblem pt) (cetaProof pt)
  _               -> Left "Output.The problem is not polynomial."

cetaAnswer :: T.ProofTree l -> Xml.XmlContent
cetaAnswer pt = case T.timeUB (T.certificate pt) of
  T.Poly (Just k) -> Xml.elt "polynomial" [Xml.int k]
  _               -> Xml.text ""

cetaProblem :: Xml.Xml prob => prob -> T.ProofTree t -> Xml.XmlContent
cetaProblem prob pt = C.complexityInput trsInput complexityMeasure complexityClassE
  where
    xmlProb = Xml.toXml prob
    fd s = Xml.find s xmlProb

    trsInput          = Xml.elt "trsInput" [fd "trs", nonfull, fd "relativeRules"]
    strat             = fd "strategy"
    nonfull           = case Xml.search "full" strat of
      Just _  -> Xml.text ""
      Nothing -> strat
    complexityMeasure = Xml.child $ fd "complexityMeasure"
    complexityClassE  = cetaAnswer pt
   
cetaSubProblem :: Xml.Xml t => T.ProofTree t -> Xml.XmlContent
cetaSubProblem pt@(T.Open prob)       = cetaProblem prob pt
cetaSubProblem pt@(T.NoProgress pn _) = cetaProblem (T.problem pn) pt
cetaSubProblem pt@(T.Progress pn _ _) = cetaProblem (T.problem pn) pt


isCertifiable :: Xml.XmlContent -> Bool
isCertifiable c = let t = Xml.rootTag c `elem` certifiable in traceShow (Xml.rootTag c) t

cetaProof :: Xml.Xml t => T.ProofTree t -> Xml.XmlContent
cetaProof = C.complexityProof . cetaProof'

cetaProof' :: Xml.Xml t => T.ProofTree t -> Xml.XmlContent
cetaProof' (T.Open _)                = Xml.text ""
cetaProof' (T.NoProgress _ spt)      = cetaProof' spt
cetaProof' pt@(T.Progress pn _ spts) = case F.toList spts of
  []  | isCertifiable xmlpn -> xmlpn
  [t] | isCertifiable xmlpn -> Xml.addChildren xmlpn [cetaProof t]
  ts                          -> C.unknownProof "description" (cetaSubProblem pt) (map mkSubProofs ts)
  where 
    xmlpn   = Xml.toXml (T.proof pn)
    mkSubProofs spt = C.subProof (cetaSubProblem spt) (cetaProof spt)

