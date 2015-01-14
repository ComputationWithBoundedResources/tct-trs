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

import           Tct.Trs
import           Tct.Trs.Data.Trs
import           Tct.Trs.Interpretation


--- Instances --------------------------------------------------------------------------------------------------------

polyDeclaration :: T.Declaration ('[ T.Argument 'T.Required PI.Shape ] T.:-> T.Strategy Problem)
polyDeclaration = T.declare "poly" ["Applies polynomial interpretation."] (T.OneTuple PI.shapeArg) poly

poly :: PI.Shape -> T.Strategy Problem
poly = T.Proc . PolyInterProc


stronglyLinear, linear, quadratic :: T.Strategy Problem
stronglyLinear = T.Proc (PolyInterProc PI.StronglyLinear)
linear         = T.Proc (PolyInterProc PI.Linear)
quadratic      = T.Proc (PolyInterProc PI.Quadratic)

mixed :: Int -> T.Strategy Problem
mixed = T.Proc . PolyInterProc . PI.Mixed


data PolyInterProcessor = PolyInterProc
  { shape :: PI.Shape
  } deriving Show


newtype PolyInterProof = PolyInterProof (OrientationProof PolyOrder) deriving Show

type PolyInter      = PI.PolyInter Fun
type Kind           = PI.Kind Fun
type CoefficientVar = PI.CoefficientVar Fun

data PolyOrder = PolyOrder
  { kind_      :: Kind
  , pint_      :: PolyInter Int
  , strictDPs_ :: [(Rule, (P.Polynomial Int Var, P.Polynomial Int Var))]
  , strictTrs_ :: [(Rule, (P.Polynomial Int Var, P.Polynomial Int Var))]
  , weakDPs_   :: [(Rule, (P.Polynomial Int Var, P.Polynomial Int Var))]
  , weakTrs_   :: [(Rule, (P.Polynomial Int Var, P.Polynomial Int Var))]
  } deriving Show


instance T.Processor PolyInterProcessor where
  type ProofObject PolyInterProcessor = ApplicationProof PolyInterProof
  type Problem PolyInterProcessor     = Problem
  type Forking PolyInterProcessor     = T.Optional T.Id
  solve p prob
    | isTrivial prob = return . T.resultToTree p prob $
       T.Success T.Null Closed (const $ T.timeUBCert T.constant)
    | otherwise  = do
        res <- liftIO $ entscheide p prob
        return . T.resultToTree p prob $ case res of
          SMT.Sat order ->
            T.Success (newProblem order prob) (Applicable $ PolyInterProof $ Order order) (certification order)
          _                         -> T.Fail (Applicable $ PolyInterProof Incompatible)


newtype StrictVar = StrictVar Rule deriving (Eq, Ord)

strict :: Rule -> StrictVar
strict = StrictVar

newProblem :: PolyOrder -> Problem -> T.Optional T.Id Problem
newProblem order prob = T.Opt . T.Id $ prob 
  { strictDPs = strictDPs prob `difference` sDPs
  , strictTrs = strictTrs prob `difference` sTrs
  , weakDPs = weakDPs prob `union` sDPs
  , weakTrs = weakTrs prob `union` sTrs
  }
  where 
    rules = fromRuleList . fst . unzip
    sDPs = rules (strictDPs_ order)
    sTrs = rules (strictTrs_ order)
    

degree :: PolyOrder -> T.Complexity
degree order  = PI.degree (kind_ order) (pint_ order)

certification :: PolyOrder -> T.Optional T.Id T.Certificate -> T.Certificate
certification order T.Null           = T.timeUBCert (degree order)
certification order (T.Opt (T.Id c)) = T.updateTimeUBCert c (`add` degree order)

interpret :: (SemiRing c, Eq c, Ord fun, Ord var) => PI.PolyInter fun c -> R.Term fun var -> P.Polynomial c var
interpret ebsi = interpretTerm interpretFun interpretVar
  where
    interpretFun f = P.substituteVariables interp . M.fromList . zip [PI.SomeIndeterminate 0..]
      where interp = PI.interpretations ebsi M.! f
    interpretVar      = P.variable

entscheide :: PolyInterProcessor -> Problem -> IO (SMT.Result PolyOrder)
entscheide p prob = do
  res :: SMT.Result (M.Map CoefficientVar Int) <- SMT.solveStM SMT.minismt $ do
    SMT.setFormat "QF_NIA"
    -- encode abstract interpretation
    (ebsi,coefficientEncoder) <- SMT.memo $ PI.PolyInter `liftM` T.mapM encode absi
    -- encode strict vars
    (_, strictVarEncoder) <- SMT.memo $ mapM  (SMT.snvarMO . StrictVar) rules

    let
      encodeStrictVar   = (strictVarEncoder M.!)

    let
      p1 `gte` p2 = SMT.bigAnd [ c SMT..>= SMT.zero | c <- P.coefficients $ p1 `add` neg p2 ]
      interpreted = [ (r, interpret ebsi (R.lhs r), interpret ebsi (R.rhs r)) | r <- rules ]
      orderConstraints     =
        [ lhs `gte`  (rhs `add` P.constant (encodeStrictVar $ strict r))
        | (r,lhs,rhs) <- interpreted ]
      monotoneConstraints = [ c SMT..> SMT.zero | (v,c) <- M.assocs coefficientEncoder, isSimple (PI.argpos v)]
      rulesConstraint     = [ s SMT..> SMT.zero | r <- ruleList (strictComponents prob), let s = encodeStrictVar (StrictVar r) ]

    SMT.assert $ SMT.bigAnd orderConstraints
    SMT.assert $ SMT.bigAnd monotoneConstraints
    SMT.assert $ SMT.bigOr rulesConstraint

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
    rules = ruleList (allComponents prob)
    sig   = signature prob
    absi  = M.mapWithKey (curry (PI.mkInterpretation kind)) sig
    kind  =
      if isRCProblem prob 
        then PI.ConstructorBased (shape p) (constructorSymbols $ startTerms prob)
        else PI.Unrestricted (shape p)

    mkOrder inter = PolyOrder
      { kind_      = kind
      , pint_      = pint
      , strictDPs_ = sDPs
      , strictTrs_ = sTrs
      , weakDPs_   = wDPs
      , weakTrs_   = wTrs }
      where
        pint        = PI.PolyInter $ M.map (P.fromViewWith (inter M.!)) absi
        dpPints     = [ (r, (interpret pint lhs, interpret pint rhs)) | r@(R.Rule lhs rhs)  <- ruleList (dpComponents prob) ]
        (sDPs,wDPs) = L.partition (\(_,(lhs,rhs)) -> P.constantValue (lhs `sub` rhs) > 0) dpPints
        trsPints    = [ (r, (interpret pint lhs, interpret pint rhs)) | r@(R.Rule lhs rhs)  <- ruleList (trsComponents prob) ]
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
  toXml _ = Xml.text "polyorder"

instance Xml.Xml PolyInterProof where
  toXml (PolyInterProof order) = Xml.toXml order

