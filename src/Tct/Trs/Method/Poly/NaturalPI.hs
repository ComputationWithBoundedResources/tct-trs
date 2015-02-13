{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Trs.Method.Poly.NaturalPI
  (
  -- * Declaration
  poly
  , polyDeclaration
  , urArg
  , uaArg
  -- * Strategies
  , stronglyLinear
  , linear
  , quadratic
  , mixed
  ) where


import Control.Monad.Trans                           (liftIO)
import qualified Data.List                           as L
import qualified Data.Map.Strict                     as M
import           Data.Monoid
import qualified Data.Set                            as S
import qualified Data.Traversable                    as F

import qualified Data.Rewriting.Rule                 as R (Rule (..))
import qualified Data.Rewriting.Term                 as R

import qualified Tct.Core.Common.Pretty              as PP
import qualified Tct.Core.Common.Xml                 as Xml
import qualified Tct.Core.Data                       as T
import           Tct.Core.Data.Declaration.Parse     ()

import qualified Tct.Common.Polynomial               as P
import qualified Tct.Common.PolynomialInterpretation as PI
import           Tct.Common.ProofCombinators
import           Tct.Common.Ring
import           Tct.Common.SMT                     ((.&&), (.==>), (.>), (.>=))
import qualified Tct.Common.SMT                     as SMT

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem                as Prob
import qualified Tct.Trs.Data.RuleSelector           as Trs
import qualified Tct.Trs.Data.Signature              as Sig
import qualified Tct.Trs.Data.Trs                    as Trs
import qualified Tct.Trs.Encoding.UsablePositions    as UPEnc
import qualified Tct.Trs.Encoding.UsableRules        as UREnc
import           Tct.Trs.Interpretation

-- MS: TODO
-- implement a greedy interface reusing the encoding
-- should abstract polynomials for compound symbols be restricted to SLI ?


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
          _             -> T.Fail (Applicable $ PolyInterProof Incompatible)

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

certification :: PolyOrder -> T.Id T.Certificate -> T.Certificate
certification order (T.Id c) = T.updateTimeUBCert c (`add` bound)
  where bound = PI.bound (kind_ order) (pint_ order)

interpret :: (Show c, Show fun, SemiRing c, Eq c, Ord fun, Ord var) => PI.PolyInter fun c -> R.Term fun var -> P.Polynomial c var
interpret ebsi = interpretTerm interpretFun interpretVar
  where
    interpretFun f = P.substituteVariables interp . M.fromList . zip PI.indeterminates
      where interp = PI.interpretations ebsi M.! f
    interpretVar      = P.variable

newtype StrictVar f v = StrictVar (R.Rule f v) deriving (Show, Eq, Ord)

entscheide :: PolyInterProcessor -> TrsProblem -> IO (SMT.Result PolyOrder)
entscheide p prob = do
  res :: SMT.Result (M.Map CoefficientVar Int, UPEnc.UsablePositions F, Maybe (Symbols F)) <- SMT.solveStM SMT.minismt $ do
    SMT.setFormat "QF_NIA"
    -- encode abstract interpretation
    (ebsi,coefficientEncoder) <- SMT.memo $ PI.PolyInter `fmap` F.mapM encode absi
    -- encode strict vars
    (_, strictEncoder) <- SMT.memo $ mapM (SMT.snvarMO . StrictVar) rules
    -- encode usable rules
    (usable, inFilter, usableEncoder, _, validUsableEncoding) <- UREnc.usableRulesEncoding prob allowUR allowAF

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

    return $ SMT.decode (coefficientEncoder, usablePositions, usableEncoder)
  return $ mkOrder `fmap` res
  where

    allowUR = urules p && Prob.isDPProblem prob
    allowAF = allowUR && Prob.isDTProblem prob

    encode = P.fromViewWithM enc where
      enc c
        | PI.restrict c = SMT.snvarMO c
        | otherwise     = SMT.nvarMO c
    rules = Trs.toList (Prob.allComponents prob)
    sig   = Prob.signature prob
    absi  = M.mapWithKey (curry $ PI.mkInterpretation kind) (Sig.toMap sig)
    kind  =
      if Prob.isRCProblem prob
        then PI.ConstructorBased (shape p) (Prob.constructors $ Prob.startTerms prob)
        else PI.Unrestricted (shape p)

    mkOrder (inter, uposs, ufuns) = PolyOrder
      { kind_      = kind
      , pint_      = pint
      , sig_       = sig
      , uargs_     = uposs

      , strictDPs_ = sDPs
      , strictTrs_ = sTrs
      , weakDPs_   = wDPs
      , weakTrs_   = wTrs }
      where
        pint        = PI.PolyInter $ M.map (P.fromViewWith (inter M.!)) absi
        (sDPs,wDPs) = L.partition (isStrict . snd) (rs $ Prob.dpComponents prob)
        (sTrs,wTrs) = L.partition (isStrict . snd) (rs $ Prob.trsComponents prob)
        isStrict (lpoly,rpoly) = P.constantValue (lpoly `sub` rpoly) > 0
        rs trs =
          [ (r, (interpret pint lhs, interpret pint rhs))
          | r@(R.Rule lhs rhs) <- Trs.toList trs
          , isUsable ufuns r ]
        isUsable Nothing _                = True
        isUsable (Just fs) (R.Rule lhs _) = either (const False) (`S.member` fs) (R.root lhs)

--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty PolyOrder where
  pretty order = PP.vcat
    [ PP.text "We apply a polynomial interpretation of kind " <> PP.pretty (kind_ order) <> PP.char ':'
    , if uargs_ order /= UPEnc.fullWithSignature (sig_ order) 
        then PP.vcat
          [ PP.text "The following argument positions are considered usable:"
          , PP.indent 2 $ PP.pretty (uargs_ order) 
          , PP.empty ]
        else PP.empty
    , PP.text "TcT has computed the following interpretation:"
    , PP.indent 2 (PP.pretty (pint_ order))
    , PP.empty
    , PP.text "Following rules are strictly oriented:"
    , ppOrder (PP.text " > ") (strictDPs_ order ++ strictTrs_ order)
    , PP.text ""
    , PP.text "Following rules are (at-least) weakly oriented:"
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
  toXml order = Xml.elt "ruleShifting" $
    [ orderingConstraintProof
    , Xml.elt "trs" [Xml.toXml $ Trs.fromList trs] 
    , Xml.elt "usableRules" [Xml.toXml $ Trs.fromList usr]]
    where 
      orderingConstraintProof =
        Xml.elt "orderingConstraintProof" 
          [ Xml.elt "redPair" [Xml.elt "interpretation" (xtype :xinters)]]
      xtype   = Xml.elt "type" [Xml.elt "polynomial" [xdomain, xdegree]]
      xdegree = Xml.elt "degree" [Xml.int $ PI.degree (pint_ order)]
      xdomain = Xml.elt "domain" [Xml.elt "naturals" []]
      xinters = (map xinter . M.toList . PI.interpretations $ pint_ order)
      xinter (f,p) = Xml.elt "interpret"
        [ Xml.toXml f
        , Xml.elt "arity" [Xml.int $ sig_ order `Sig.arity` f]
        , Xml.elt "polynomial" [Xml.toXml p]]
      trs = map fst $ strictTrs_ order ++ strictDPs_ order
      usr = (trs ++) . map fst $ weakTrs_ order ++ weakDPs_ order
  toCeTA = Xml.toXml

instance Xml.Xml PolyInterProof where
  toXml (PolyInterProof order) = Xml.toXml order
  toCeTA                       = Xml.toXml


--- * instances ------------------------------------------------------------------------------------------------------

polyDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional PI.Shape 
   , T.Argument 'T.Optional Bool 
   , T.Argument 'T.Optional Bool 
   , T.Argument 'T.Optional (Maybe (ExpressionSelector F V)) ]
   T.:-> T.Strategy TrsProblem)
polyDeclaration = T.declare "poly" desc  (shArg, uaArg `T.optional` True,  urArg `T.optional` True, slArg) poly where
  desc =  ["This processor tries to find a polynomial interpretation and shifts strict oriented rules to the weak components."]
  shArg = PI.shapeArg `T.optional` PI.Linear
  slArg = T.some Trs.selectorArg 
    `T.withName` "shift"
    `T.withHelp`
      [ "This argument specifies which rules to orient strictly and shift to the weak components." ]
    `T.optional` Nothing

uaArg :: T.Argument 'T.Required Bool
uaArg = T.bool 
  `T.withName` "uargs"
  `T.withHelp` 
    [ "This argument specifies whether usable arguments are computed (if applicable)"
    , "in order to relax the monotonicity constraints on the interpretation."]

urArg :: T.Argument 'T.Required Bool
urArg = T.bool
  `T.withName` "urules"
  `T.withHelp`
    [ "This argument specifies whether usable rules modulo argument filtering is applied"
    , "in order to decrease the number of rules that have to be orient. "]


poly :: PI.Shape -> Bool -> Bool -> Maybe (ExpressionSelector F V) -> T.Strategy TrsProblem
poly sh ua ur sl = T.Proc $ PolyInterProc
  { shape    = sh
  , uargs    = ua
  , urules   = ur
  , selector = sl }

-- TODO: MS: better interface
-- can we do without exposing the processor type a builder a -> Strategy with modifyers f a -> a?
stronglyLinear :: Bool -> Bool -> Maybe (ExpressionSelector F V) -> T.Strategy TrsProblem
stronglyLinear ua ur sl = T.Proc $ PolyInterProc
  { shape    = PI.Linear
  , uargs    = ua
  , urules   = ur
  , selector = sl }

linear :: Bool -> Bool -> Maybe (ExpressionSelector F V) -> T.Strategy TrsProblem
linear ua ur sl = T.Proc $ PolyInterProc
  { shape    = PI.Linear
  , uargs    = ua
  , urules   = ur
  , selector = sl }

quadratic :: Bool -> Bool -> Maybe (ExpressionSelector F V) -> T.Strategy TrsProblem
quadratic ua ur sl = T.Proc $ PolyInterProc
  { shape    = PI.Quadratic
  , uargs    = ua
  , urules   = ur
  , selector = sl }

mixed :: Int -> Bool -> Bool -> Maybe (ExpressionSelector F V) -> T.Strategy TrsProblem
mixed i ua ur sl = T.Proc $ PolyInterProc
  { shape    = PI.Mixed i
  , uargs    = ua
  , urules   = ur
  , selector = sl }

