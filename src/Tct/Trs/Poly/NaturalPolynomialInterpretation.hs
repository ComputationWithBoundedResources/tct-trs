{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Trs.Poly.NaturalPolynomialInterpretation
  (
  -- * Declaration
  poly
  -- * Strategies
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
import qualified SmtLib.Logic.Core                   as SMT
import qualified SmtLib.Logic.Int                    as SMT
import qualified SmtLib.SMT                          as SMT
import qualified SmtLib.Solver                       as SMT

import qualified Data.Rewriting.Term                 as R

import qualified Tct.Common.Polynomial               as P
import qualified Tct.Common.PolynomialInterpretation as PI
import           Tct.Common.Ring
import           Tct.Common.SMT                      ()
import           Tct.Common.Orientation

import           Tct.Core.Common.Error               (liftIO)
import qualified Tct.Core.Common.Pretty              as PP
import qualified Tct.Core.Common.Xml                 as Xml
import           Tct.Core.Data                       hiding (linear)
import           Tct.Core.Data.Declaration.Parse     ()

import           Tct.Trs
import           Tct.Trs.Interpretation


--- Instances --------------------------------------------------------------------------------------------------------

polyInterProcessor :: PolyInterProcessor
polyInterProcessor = PolyInterProc PI.StronglyLinear

poly ::Declaration ('[ Argument 'Required PI.Shape ] :-> Strategy Trs)
poly = declaration polyInterProcessor

stronglyLinear, linear, quadratic :: Strategy Trs
stronglyLinear = Proc (PolyInterProc PI.StronglyLinear)
linear         = Proc (PolyInterProc PI.Linear)
quadratic      = Proc (PolyInterProc PI.Quadratic)

mixed :: Int -> Strategy Trs 
mixed = Proc . PolyInterProc . PI.Mixed


data PolyInterProcessor = PolyInterProc
  { shape :: PI.Shape
  } deriving Show


newtype PolyInterProof = PolyInterProof (OrientationProof PolyOrder)

type PolyInter      = PI.PolyInter Fun
type Kind           = PI.Kind Fun
type CoefficientVar = PI.CoefficientVar Fun

data PolyOrder = PolyOrder
  { strict_ :: [Rule]
  , weak_   :: [Rule]
  , inter_  :: PolyInter Int
  , kind_   :: Kind
  } deriving Show


instance Processor PolyInterProcessor where
  type ProofObject PolyInterProcessor = PolyInterProof
  type Problem PolyInterProcessor     = Trs
  type Forking PolyInterProcessor     = Optional Id
  type ProcessorArgs PolyInterProcessor = 
    '[ Argument 'Required PI.Shape ]
  solve p prob
    | null (strictRules prob) = return . resultToTree p prob $
       (Success Null (PolyInterProof Empty) (const $ timeUBCert constant))
    | otherwise  = do
        res <- liftIO $ entscheide p prob
        return . resultToTree p prob $ case res of
          SMT.Sat (order) ->
            Success (newProblem order prob) (PolyInterProof $ Order order) (certification order)
          _                         -> Fail (PolyInterProof Incompatible)
  declaration _ = declareProcessor "poly" [] (OneTuple PI.shapeArg) (Proc . PolyInterProc)

newtype StrictVar = StrictVar Rule deriving (Eq, Ord)

strict :: Rule -> StrictVar
strict = StrictVar

newProblem :: PolyOrder -> Trs -> Optional Id Trs
newProblem order prob = Opt . Id $ prob 
  { strictRules = strictRules prob L.\\ (strict_ order)
  , weakRules   = L.nub $ weakRules prob ++ (strict_ order) }

degree :: PolyOrder -> Complexity
degree order  = PI.degree (kind_ order) (inter_ order)

certification :: PolyOrder -> Optional Id Certificate -> Certificate
certification order Null         = timeUBCert (degree order)
certification order (Opt (Id c)) = updateTimeUBCert c (`add` degree order)

interpret :: (SemiRing c, Eq c, Ord fun, Ord var) => PI.PolyInter fun c -> R.Term fun var -> P.Polynomial c var
interpret ebsi = interpretTerm interpretFun interpretVar
  where
    interpretFun f = P.substituteVars interp . M.fromList . zip [PI.SomeIndeterminate 0..]
      where interp = PI.interpretations ebsi M.! f
    interpretVar      = P.variable

entscheide :: PolyInterProcessor -> Trs -> IO (SMT.Sat PolyOrder)
entscheide p prob = do
  res :: SMT.Sat (M.Map CoefficientVar Int, M.Map StrictVar Int) <- SMT.solve SMT.minismt $ do
    SMT.setLogic "QF_NIA"
    -- encode abstract interpretation
    (ebsi,coefficientEncoder) <- SMT.memo $ PI.PolyInter `liftM` T.mapM encode absi
    -- encode strict vars
    (svars, strictVarEncoder) <- SMT.memo $ mapM  (SMT.snvarm . StrictVar) rules

    let
      encodeStrictVar   = SMT.fm . (strictVarEncoder M.!)

    let
      p1 `gte` p2 = SMT.bigAnd [ c SMT..>= SMT.zero | c <- P.coefficients $ p1 `add` neg p2 ]
      interpreted = [ (r, interpret ebsi (R.lhs r), interpret ebsi (R.rhs r)) | r <- rules ]
      orderConstraints     =
        [ lhs `gte`  (rhs `add` P.constant (encodeStrictVar $ strict r))
        | (r,lhs,rhs) <- interpreted ]
      monotoneConstraints = [ SMT.fm c SMT..> SMT.zero | c <- M.elems coefficientEncoder ]
      rulesConstraint     = [ SMT.fm s SMT..> SMT.zero | r <- (strictRules prob), let s = encodeStrictVar (StrictVar r) ]

    SMT.assert $ SMT.bigAnd orderConstraints
    SMT.assert $ SMT.bigAnd monotoneConstraints
    SMT.assert $ SMT.bigOr rulesConstraint

    return $ SMT.decode (coefficientEncoder, strictVarEncoder)
  return $ mkOrder `fmap` res
  where
    encode :: Monad m
      => P.PolynomialView (PI.CoefficientVar Fun) PI.SomeIndeterminate
      -> SMT.MemoSMT CoefficientVar m (PI.SomePolynomial SMT.Expr)
    encode = P.pfromViewWithM enc where
      enc c
        | PI.restrict c = SMT.fm `liftM` SMT.snvarm c
        | otherwise     = SMT.fm `liftM` SMT.nvarm c
    rules = allRules prob
    sig   = signature prob
    absi  = M.mapWithKey (curry (PI.mkInterpretation kind)) sig
    kind  =
      if withBasicTerms prob
        then PI.ConstructorBased (shape p) (constructors prob)
        else PI.Unrestricted (shape p)
    mkOrder (inter, stricts) = (PolyOrder strict' weak' pint kind)
      where
        pint = PI.PolyInter $ M.map (P.pfromViewWith (inter M.!)) absi
        strictVar r = case M.lookup (strict r) stricts of
          Just i  -> i > (0::Int)
          Nothing -> False
        strictOrder (R.Rule lhs rhs) = P.constantValue (interpret pint lhs `add` neg (interpret pint rhs)) > 0
        (strict',weak') = L.partition (\r -> strictVar r || strictOrder r) rules


--- Proofdata --------------------------------------------------------------------------------------------------------

instance PP.Pretty PolyOrder where
  pretty (PolyOrder s w i k) = PP.vcat
    [ PP.text "We apply a polynomial interpretation of kind" PP.<+> PP.pretty k PP.<> PP.char ':'
    , PP.indent 2 (PP.pretty i)
    , PP.text "Following rules are strictly oriented:"
    , PP.indent 2 (PP.vcat (map PP.pretty s))
    , PP.text "Following rules are weakly oriented:"
    , PP.indent 2 (PP.vcat (map PP.pretty w)) 
    , PP.text "" 
    , PP.vcat [ PP.pretty (interpret i rhs) PP.<+> PP.text "> " PP.<+> PP.pretty (interpret i lhs) | R.Rule rhs lhs <- s]
    , PP.text "" 
    , PP.vcat [ PP.pretty (interpret i rhs) PP.<+> PP.text ">=" PP.<+> PP.pretty (interpret i lhs) | R.Rule rhs lhs <- w]
    ]

instance Show PolyInterProof where 
  show (PolyInterProof order) = show order

instance PP.Pretty PolyInterProof 
  where pretty (PolyInterProof order) = PP.pretty order

instance Xml.Xml PolyInterProof where
  toXml = undefined

