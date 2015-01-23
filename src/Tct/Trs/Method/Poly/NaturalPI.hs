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
import qualified Data.Traversable                    as T

import qualified Data.Rewriting.Rule                 as R (Rule (..))

import qualified Data.Rewriting.Term                 as R

import qualified Tct.Common.Polynomial               as P
import qualified Tct.Common.PolynomialInterpretation as PI
import           Tct.Common.Ring
import qualified Tct.Common.SMT                      as SMT
import           Tct.Common.ProofCombinators

import           Tct.Core.Common.Error               (liftIO)
import qualified Tct.Core.Common.Pretty              as PP
import qualified Tct.Core.Common.Xml                 as Xml
import qualified Tct.Core.Data                       as T
import           Tct.Core.Data.Declaration.Parse     ()

import Tct.Trs.Interpretation
import qualified Tct.Trs.Data.Trs as Trs
import Tct.Trs.Data
import qualified Tct.Trs.Data.Problem as Prob

import Debug.Trace


--- Instances --------------------------------------------------------------------------------------------------------

polyDeclaration :: T.Declaration ('[ T.Argument 'T.Required PI.Shape ] T.:-> T.Strategy TrsProblem)
polyDeclaration = T.declare "poly" ["Applies polynomial interpretation."] (T.OneTuple PI.shapeArg) poly

poly :: PI.Shape -> T.Strategy TrsProblem
poly = T.Proc . PolyInterProc


stronglyLinear, linear, quadratic :: T.Strategy TrsProblem
stronglyLinear = T.Proc (PolyInterProc PI.StronglyLinear)
linear         = T.Proc (PolyInterProc PI.Linear)
quadratic      = T.Proc (PolyInterProc PI.Quadratic)

mixed :: Int -> T.Strategy TrsProblem
mixed = T.Proc . PolyInterProc . PI.Mixed


data PolyInterProcessor = PolyInterProc
  { shape :: PI.Shape
  } deriving Show


newtype PolyInterProof = PolyInterProof (OrientationProof PolyOrder) deriving Show

type PolyInter      = PI.PolyInter F
type Kind           = PI.Kind F
type CoefficientVar = PI.CoefficientVar F

data PolyOrder = PolyOrder
  { kind_      :: Kind
  , pint_      :: PolyInter Int
  , sig_       :: Signature F
  , strictDPs_ :: [(R.Rule F V, (P.Polynomial Int V, P.Polynomial Int V))]
  , strictTrs_ :: [(R.Rule F V, (P.Polynomial Int V, P.Polynomial Int V))]
  , weakDPs_   :: [(R.Rule F V, (P.Polynomial Int V, P.Polynomial Int V))]
  , weakTrs_   :: [(R.Rule F V, (P.Polynomial Int V, P.Polynomial Int V))]
  } deriving Show


instance T.Processor PolyInterProcessor where
  type ProofObject PolyInterProcessor = ApplicationProof PolyInterProof
  type Problem PolyInterProcessor     = TrsProblem
  type Forking PolyInterProcessor     = T.Optional T.Id
  solve p prob
    {-| isTrivial prob = return . T.resultToTree p prob $-}
       {-T.Success T.Null Closed (const $ T.timeUBCert T.constant)-}
    | Prob.isTrivial prob = return . T.resultToTree p prob $ T.Fail Closed
    | otherwise  = do
        res <- liftIO $ entscheide p prob
        return . T.resultToTree p prob $ case res of
          SMT.Sat order ->
            T.Success (newProblem order prob) (Applicable $ PolyInterProof $ Order order) (certification order)
          _                         -> T.Fail (Applicable $ PolyInterProof Incompatible)


newtype StrictVar f v = StrictVar (R.Rule f v) deriving (Show, Eq, Ord)

strict :: R.Rule f v -> StrictVar f v 
strict = StrictVar

newProblem :: PolyOrder -> TrsProblem -> T.Optional T.Id TrsProblem
newProblem order prob = T.Opt . T.Id $ prob 
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

certification :: PolyOrder -> T.Optional T.Id T.Certificate -> T.Certificate
certification order T.Null           = T.timeUBCert (degree order)
certification order (T.Opt (T.Id c)) = T.updateTimeUBCert c (`add` degree order)

interpret :: (Show c, Show fun, SemiRing c, Eq c, Ord fun, Ord var) => PI.PolyInter fun c -> R.Term fun var -> P.Polynomial c var
interpret ebsi | traceShow ("INTERPRET", ebsi) False = undefined
interpret ebsi = interpretTerm interpretFun interpretVar
  where
    interpretFun f = P.substituteVariables interp . M.fromList . zip [PI.SomeIndeterminate 0..]
      where interp = PI.interpretations ebsi M.! f
    interpretVar      = P.variable

entscheide :: PolyInterProcessor -> TrsProblem -> IO (SMT.Result PolyOrder)
entscheide p prob = do
  res :: SMT.Result (M.Map CoefficientVar Int) <- SMT.solveStM SMT.minismt $ do
    SMT.setFormat "QF_NIA"
    -- encode abstract interpretation
    (ebsi,coefficientEncoder) <- SMT.memo $ PI.PolyInter `liftM` T.mapM encode absi
    -- encode strict vars
    (_, strictVarEncoder) <- SMT.memo $ mapM  (SMT.snvarMO . StrictVar) rules

    let
      encodeStrictVar   = traceShow ("ENCODER", coefficientEncoder, strictVarEncoder) (strictVarEncoder M.!)

    let
      p1 `gte` p2 = SMT.bigAnd [ c SMT..>= SMT.zero | c <- P.coefficients $ p1 `add` neg p2 ]
      interpreted = [ (r, interpret ebsi (R.lhs r), interpret ebsi (R.rhs r)) | r <- take 1 rules ]
      orderConstraints     = traceShow ("INTERPRETED", interpreted) $
        [ lhs `gte`  (rhs `add` P.constant (encodeStrictVar $ strict r))
        | (r,lhs,rhs) <- interpreted ]
      monotoneConstraints = [ c SMT..> SMT.zero | (v,c) <- M.assocs coefficientEncoder, isSimple (PI.argpos v)]
      rulesConstraint     = [ s SMT..> SMT.zero | r <- Trs.toList (Prob.strictComponents prob), let s = encodeStrictVar (StrictVar r) ]

    SMT.assert $ SMT.bigAnd $ let r = orderConstraints in traceShow ("ORDER", r) r 
    SMT.assert $ SMT.bigAnd $ let r = monotoneConstraints in traceShow ("MONOTNONE", r) r
    SMT.assert $ SMT.bigOr  $ let r = rulesConstraint in traceShow ("RULES", r) r

    return $ SMT.decode coefficientEncoder
  return $ mkOrder `fmap` res
  where
    isSimple m = case P.mtoView' m of
      [(_,1)] -> True
      _       -> False

    encode = P.fromViewWithM enc where
      enc c
        | PI.restrict c = SMT.snvarMO c
        | otherwise     = SMT.nvarMO c
    rules = Trs.toList (Prob.allComponents prob)
    sig   = Prob.signature prob
    absi  = M.mapWithKey (curry (PI.mkInterpretation kind)) (Trs.runSignature sig)
    kind  =
      if Prob.isRCProblem prob 
        then PI.ConstructorBased (shape p) (Prob.constructors $ Prob.startTerms prob)
        else PI.Unrestricted (shape p)

    mkOrder inter = PolyOrder
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


--- Proofdata --------------------------------------------------------------------------------------------------------

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
      xdegree = Xml.elt "degree" $ 
        case PI.degree (kind_ order) (pint_ order) of
          T.Poly (Just k) -> [Xml.int k]
          _               -> [Xml.text "unknown"]
      xdomain = Xml.elt "domain" [Xml.elt "naturals" []]
      xinters = (map xinter . M.toList . PI.interpretations $ pint_ order)
      xinter (f,p) = Xml.elt "interpret"
        [ Xml.toXml f
        , Xml.elt "arity" [Xml.int $ sig_ order `Trs.arity` f]
        , Xml.elt "polynomial" [Xml.toXml p]]
      trs = Xml.toXml (Trs.fromList $ map fst (strictTrs_ order ++ strictDPs_ order) )

instance Xml.Xml PolyInterProof where
  toXml (PolyInterProof order) = Xml.toXml order

