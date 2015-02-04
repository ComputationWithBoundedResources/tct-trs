{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Trs.Method.Poly.NaturalPI
  (
  -- * Declaration
  polyDeclaration
  -- * Strategies
  , poly
  , stronglyLinear
  , linear
  , quadratic
  , mixed
  ) where


import           Control.Monad                       (liftM)
import qualified Data.List                           as L
import qualified Data.Map.Strict                     as M
import qualified Data.Traversable                    as F

import qualified Data.Rewriting.Rule                 as R (Rule (..))
import qualified Data.Rewriting.Term                 as R

import qualified Tct.Common.Polynomial               as P
import qualified Tct.Common.PolynomialInterpretation as PI
import           Tct.Common.Ring
import           Tct.Common.SMT                      ((.>), (.>=),  (.==>), (.&&))
import qualified Tct.Common.SMT                      as SMT
import           Tct.Common.ProofCombinators

import           Tct.Core.Common.Error               (liftIO)
import qualified Tct.Core.Common.Pretty              as PP
import qualified Tct.Core.Common.Xml                 as Xml
import qualified Tct.Core.Data                       as T
import           Tct.Core.Data.Declaration.Parse     ()

import qualified Tct.Trs.Encoding.UsableRules as UREnc
import qualified Tct.Trs.Encoding.UsablePositions as UPEnc
import Tct.Trs.Interpretation
import qualified Tct.Trs.Data.Trs as Trs
import qualified Tct.Trs.Data.Signature as Sig
import qualified Tct.Trs.Data.ArgumentFiltering as AF
import qualified Tct.Trs.Data.RuleSelector as Trs
import Tct.Trs.Data
import qualified Tct.Trs.Data.Problem as Prob


--- Instances --------------------------------------------------------------------------------------------------------

polyDeclaration :: T.Declaration ('[ T.Argument 'T.Required PI.Shape ] T.:-> T.Strategy TrsProblem)
polyDeclaration = T.declare "poly" ["Applies polynomial interpretation."] (T.OneTuple PI.shapeArg) poly

poly :: PI.Shape -> T.Strategy TrsProblem
poly sh = T.Proc $ defaultPoly `withShape` sh

stronglyLinear, linear, quadratic :: T.Strategy TrsProblem
stronglyLinear = T.Proc $ defaultPoly `withShape` PI.StronglyLinear
linear         = T.Proc $ defaultPoly `withShape` PI.Linear
quadratic      = T.Proc $ defaultPoly `withShape` PI.Quadratic

mixed :: Int -> T.Strategy TrsProblem
mixed n = T.Proc $ defaultPoly `withShape` PI.Mixed n

defaultPoly :: PolyInterProcessor
defaultPoly = PolyInterProc
  { shape    = PI.Linear
  , uargs    = True
  , urules   = True
  , selector = Nothing }

withShape :: PolyInterProcessor -> PI.Shape -> PolyInterProcessor
withShape proc sh = proc {shape = sh}

withUrules :: PolyInterProcessor -> Bool -> PolyInterProcessor
withUrules proc b = proc {urules = b}

data PolyInterProcessor = PolyInterProc
  { shape    :: PI.Shape
  , uargs    :: Bool
  , urules   :: Bool
  , selector :: Maybe (ExpressionSelector F V)
  } deriving Show


newtype PolyInterProof = PolyInterProof (OrientationProof PolyOrder) deriving Show

type PolyInter      = PI.PolyInter F
type Kind           = PI.Kind F
type CoefficientVar = PI.CoefficientVar F

data PolyOrder = PolyOrder
  { kind_      :: Kind
  , pint_      :: PolyInter Int
  , sig_       :: Signature F
  , uargs_     :: UPEnc.UsablePositions F
  , strictDPs_ :: [(R.Rule F V, (P.Polynomial Int V, P.Polynomial Int V))]
  , strictTrs_ :: [(R.Rule F V, (P.Polynomial Int V, P.Polynomial Int V))]
  , weakDPs_   :: [(R.Rule F V, (P.Polynomial Int V, P.Polynomial Int V))]
  , weakTrs_   :: [(R.Rule F V, (P.Polynomial Int V, P.Polynomial Int V))]
  } deriving Show


instance T.Processor PolyInterProcessor where
  type ProofObject PolyInterProcessor = ApplicationProof PolyInterProof
  type Problem PolyInterProcessor     = TrsProblem
  type Forking PolyInterProcessor     = T.Id
  solve p prob
    | Prob.isTrivial prob = return . T.resultToTree p prob $ T.Fail Closed
    | otherwise  = do
        res <- liftIO $ entscheide p prob
        return . T.resultToTree p prob $ case res of
          SMT.Sat order ->
            T.Success (newProblem order prob) (Applicable . PolyInterProof $ Order order) (certification order)
          _                         -> T.Fail (Applicable $ PolyInterProof Incompatible)


newtype StrictVar f v = StrictVar (R.Rule f v) deriving (Show, Eq, Ord)

newProblem :: PolyOrder -> TrsProblem -> T.Id TrsProblem
newProblem order prob = T.Id $ prob 
  { Prob.strictDPs = Prob.strictDPs prob `Trs.difference` sDPs
  , Prob.strictTrs = Prob.strictTrs prob `Trs.difference` sTrs
  , Prob.weakDPs   = Prob.weakDPs prob `Trs.union` sDPs
  , Prob.weakTrs   = Prob.weakTrs prob `Trs.union` sTrs }
  where 
    rules = Trs.fromList . fst . unzip
    sDPs = rules (strictDPs_ order)
    sTrs = rules (strictTrs_ order)
    

degree :: PolyOrder -> T.Complexity
degree order  = PI.degree (kind_ order) (pint_ order)

certification :: PolyOrder -> T.Id T.Certificate -> T.Certificate
certification order (T.Id c) = T.updateTimeUBCert c (`add` degree order)

interpret :: (Show c, Show fun, SemiRing c, Eq c, Ord fun, Ord var) => PI.PolyInter fun c -> R.Term fun var -> P.Polynomial c var
interpret ebsi = interpretTerm interpretFun interpretVar
  where
    interpretFun f = P.substituteVariables interp . M.fromList . zip PI.indeterminates
      where interp = PI.interpretations ebsi M.! f
    interpretVar      = P.variable

data PolyDP = PWithDP | PNoDP deriving Eq

entscheide :: PolyInterProcessor -> TrsProblem -> IO (SMT.Result PolyOrder)
entscheide p prob = do
  res :: SMT.Result (M.Map CoefficientVar Int, Maybe (Symbols F), Maybe (AF.ArgumentFiltering F)) <- SMT.solveStM SMT.minismt $ do
    SMT.setFormat "QF_NIA"
    -- encode abstract interpretation
    (ebsi,coefficientEncoder) <- SMT.memo $ PI.PolyInter `liftM` F.mapM encode absi
    -- encode strict vars
    (_, strictEncoder) <- SMT.memo $ mapM (SMT.snvarMO . StrictVar) rules
    -- encode usable rules
    (usable, inFilter, usableEncoder, inFilterEncoder, validUsableEncoding) <- UREnc.usableRulesEncoding prob allowUR allowAF

    let
      strict = (strictEncoder M.!) . StrictVar

      orientSelected (Trs.SelectDP r)  = strict r SMT..> zero
      orientSelected (Trs.SelectTrs r) = strict r SMT..> zero
      orientSelected (Trs.BigAnd es)   = SMT.bigAnd [ orientSelected e | e <- es]
      orientSelected (Trs.BigOr es)    = SMT.bigOr [ orientSelected e | e <- es]

      p1 `gte` p2 = SMT.bigAnd [ c .>= SMT.zero | c <- P.coefficients $ p1 `sub` p2 ]
      ordered r   = interpret ebsi (R.lhs r) `gte` (interpret ebsi (R.rhs r) `add` P.constant (strict r))

    let
      orderConstraints = SMT.bigAnd $
        [ usable r .==> ordered r | r <- Trs.toList $ Prob.trsComponents prob]
        ++ [ ordered r | r <- Trs.toList $ Prob.dpComponents prob]

      rulesConstraint = forceAny .&& forceSel
        where  
          forceAny = SMT.bigOr [ s .> zero | r <- Trs.toList (Prob.strictComponents prob), let s = strict r]
          forceSel = maybe SMT.top (\sel -> orientSelected (Trs.rsSelect sel prob)) (selector p)

      usablePositions = UPEnc.usableArgsWhereApplicable prob (Prob.isDTProblem prob) (uargs p)

      monotoneConstraints = SMT.bigAnd $ do
        (f,is)  <- UPEnc.usablePositions usablePositions
        let fpoly = PI.interpretations ebsi M.! f
        i <- is
        return (P.getCoefficient fpoly [(toEnum i, 1)] .> zero)

      usableRulesConstraints
        | allowUR   = validUsableEncoding
        | otherwise = SMT.top
        
      filteringConstraints
        | not allowAF = SMT.top
        | otherwise   = SMT.bigAnd [ afpoly f po | (f,apoly) <- M.toList (PI.interpretations ebsi), let po = P.toView apoly ]
        where 
          afpoly f po = SMT.bigAnd [ c .> zero .==> (afmono f mo) | (c, mo) <- po ]
          afmono f mo = SMT.bigAnd [ inFilter f (fromEnum vi) | (vi,_) <- mo ]

    SMT.assert orderConstraints
    SMT.assert rulesConstraint
    SMT.assert monotoneConstraints
    SMT.assert usableRulesConstraints
    SMT.assert filteringConstraints

    return $ SMT.decode (coefficientEncoder, usableEncoder, inFilterEncoder)
  return $ mkOrder `fmap` res
  where

    pdp = if Trs.null (Prob.strictTrs prob) && Prob.isDPProblem prob then PWithDP else PNoDP
    allowUR = urules p && Prob.isDPProblem prob
    allowAF = allowUR && pdp == PWithDP

    encode = P.fromViewWithM enc where
      enc c
        | PI.restrict c = SMT.snvarMO c
        | otherwise     = SMT.nvarMO c
    rules = Trs.toList (Prob.allComponents prob)
    sig   = Prob.signature prob
    absi  = M.mapWithKey (curry (PI.mkInterpretation kind)) (Sig.toMap sig)
    kind  =
      if Prob.isRCProblem prob 
        then PI.ConstructorBased (shape p) (Prob.constructors $ Prob.startTerms prob)
        else PI.Unrestricted (shape p)

    mkOrder (inter,ussymbs,af) = PolyOrder
      { kind_      = kind
      , pint_      = pint
      , sig_       = sig
      , strictDPs_ = sDPs
      , strictTrs_ = sTrs
      , weakDPs_   = wDPs
      , weakTrs_   = wTrs }
      where
        pint        = PI.PolyInter $ M.map (P.fromViewWith (inter M.!)) absi
        dpPints     = [ (r, (interpret pint lhs, interpret pint rhs)) | r@(R.Rule lhs rhs)  <- Trs.toList (Prob.dpComponents prob) ]
        (sDPs,wDPs) = L.partition (\(_,(lhs,rhs)) -> P.constantValue (lhs `sub` rhs) > 0) dpPints
        trsPints    = [ (r, (interpret pint lhs, interpret pint rhs)) | r@(R.Rule lhs rhs)  <- Trs.toList (Prob.trsComponents prob) ]
        (sTrs,wTrs) = L.partition (\(_,(lhs,rhs)) -> P.constantValue (lhs `sub` rhs) > 0) trsPints



--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty PolyOrder where
  pretty order = PP.vcat
    [ PP.text "We apply a polynomial interpretation of kind" PP.<+> PP.pretty (kind_ order) PP.<> PP.char ':'
    , PP.indent 2 (PP.pretty (pint_ order))
    , PP.text ""
    , PP.text "Following rules are strictly oriented:"
    , ppOrder (PP.text " > ") (strictDPs_ order ++ strictTrs_ order)
    , PP.text ""
    , PP.text "Following rules are weakly oriented:"
    , ppOrder (PP.text " >= ") (weakDPs_ order ++ weakTrs_ order) ]
    where
      ppOrder ppOrd rs = PP.table [(PP.AlignRight, as), (PP.AlignLeft, bs), (PP.AlignLeft, cs)]
        where
          (as,bs,cs) = unzip3 $ concatMap ppRule rs
          ppRule (R.Rule l r,(lhs,rhs)) =
            [ (PP.pretty l, PP.text " = ", PP.pretty lhs)
            , (PP.empty   , ppOrd        , PP.pretty rhs)
            , (PP.empty   , PP.text " = ", PP.pretty r)
            , (PP.empty   , PP.empty     , PP.empty) ]

instance PP.Pretty PolyInterProof where
  pretty (PolyInterProof order) = PP.pretty order

instance Xml.Xml PolyOrder where
  toXml order = Xml.elt "ruleShifting"
    [ orderingConstraintProof
    , Xml.elt "trs" [trs] ]
    where 
      orderingConstraintProof =
        Xml.elt "orderingConstraintProof" 
          [ Xml.elt "redPair" [Xml.elt "interpretation" (xtype :xinters)]]
      xtype   = Xml.elt "type" [Xml.elt "polynomial" [xdomain, xdegree]]
      -- FIXME return the max degree of the interpretation
      xdegree = Xml.elt "degree" $ 
        case PI.degree (kind_ order) (pint_ order) of
          T.Poly (Just k) -> [Xml.int k]
          _               -> [Xml.text "unknown"]
      xdomain = Xml.elt "domain" [Xml.elt "naturals" []]
      xinters = (map xinter . M.toList . PI.interpretations $ pint_ order)
      xinter (f,p) = Xml.elt "interpret"
        [ Xml.toXml f
        , Xml.elt "arity" [Xml.int $ sig_ order `Sig.arity` f]
        , Xml.elt "polynomial" [Xml.toXml p]]
      trs = Xml.toXml (Trs.fromList $ map fst (strictTrs_ order ++ strictDPs_ order) )
  toCeTA = toXml

instance Xml.Xml PolyInterProof where
  toXml (PolyInterProof order) = Xml.toXml order
  toCeTA                       = toXml

