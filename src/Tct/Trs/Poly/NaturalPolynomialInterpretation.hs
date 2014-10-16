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


import           Control.Monad                         (liftM)
import qualified Data.List                             as L
import qualified Data.Map.Strict                       as M
import qualified Data.Traversable                      as T

import qualified Data.Rewriting.Rule                   as R (Rule (..))
import qualified SmtLib.Logic.Core                     as SMT
import qualified SmtLib.Logic.Int                      as SMT
import qualified SmtLib.SMT                            as SMT
import qualified SmtLib.Solver                         as SMT

import           Tct.Common.Error                      (liftIO) -- TODO: export in TctM
import qualified Tct.Common.Pretty                     as PP
import           Tct.Common.Ring
import qualified Tct.Common.Xml                        as Xml
import           Tct.Core hiding (linear)
import           Tct.Core.Declaration.Parse ()
import qualified Tct.Common.Parser as P

import qualified Tct.Common.Polynomial                 ()
import qualified Tct.Common.Polynomial                 as P
import           Tct.Trs.Orientation                   (OrientationProof (..))
import qualified Tct.Trs.Poly.PolynomialInterpretation as PI
import           Tct.Trs


--- Instances --------------------------------------------------------------------------------------------------------

polyInterProcessor :: PolyInterProcessor
polyInterProcessor = PolyInterProc PI.StronglyLinear

poly ::Declaration ('[ Argument 'Required PI.Shape ] :-> Strategy (TrsProblem Fun Var))
poly = declaration polyInterProcessor

stronglyLinear, linear, quadratic :: Strategy (TrsProblem Fun Var)
stronglyLinear = Proc (PolyInterProc PI.StronglyLinear)
linear         = Proc (PolyInterProc PI.Linear)
quadratic      = Proc (PolyInterProc PI.Quadratic)

mixed :: Int -> Strategy (TrsProblem Fun Var)
mixed = Proc . PolyInterProc . PI.Mixed

-- TODO: to common.smt; do some re-exporting in it
instance Additive SMT.Expr where
  zero = SMT.zero
  add  = (SMT..+)

instance Multiplicative SMT.Expr where
  one = SMT.one
  mult = (SMT..*)

instance AdditiveGroup SMT.Expr where
  neg = SMT.nNeg

instance PP.Pretty SMT.Expr where
  pretty = PP.text . SMT.prettyExpr

data PolyInterProcessor = PolyInterProc
  { shape :: PI.Shape
  } deriving Show


newtype PolyInterProof = PolyInterProof (OrientationProof PolyOrder)

data PolyOrder = PolyOrder
  { strict_ :: [R.Rule Fun Var]
  , weak_   :: [R.Rule Fun Var]
  , inter_  :: PI.PolyInter Int
  , kind_   :: PI.Kind
  } deriving Show

degree :: PolyOrder -> Complexity
degree po = case kind_ po of
  PI.Unrestricted {}
    | deg1 && isStrong -> Poly (Just 1)
    | deg1             -> Exp (Just 1)
    | otherwise        -> Exp (Just 2)
    where
      deg1     = M.foldr' (\p b -> (P.degree p <= 1 && b)) True inters
      isStrong = M.foldr' ((&&) . P.isStronglyLinear) True inters
  PI.ConstructorBased _ cs -> Poly (Just deg)
    where deg = M.foldrWithKey' (\f p b -> max b $ if f `elem` cs then 0 else P.degree p) 0 inters
  where
    inters = PI.interpretations (inter_ po)

shape_ :: Argument Required (PI.Shape)
shape_ = arg { argName = "shape" }

instance SParsable prob PI.Shape where
  parseS = P.choice
    [ P.symbol "stronglyLinerar" >> return PI.StronglyLinear
    , P.symbol "linear"          >> return PI.Linear
    , P.symbol "quadratic"       >> return PI.Quadratic
    , P.symbol "mixed"           >> P.natural >>= return .PI.Mixed ]


instance Processor PolyInterProcessor where
  type ProofObject PolyInterProcessor = PolyInterProof
  type Problem PolyInterProcessor     = TrsProblem Fun Var
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
  declaration _ = declareProcessor "poly" [] (OneTuple shape_) (Proc . PolyInterProc)

newtype StrictVar = StrictVar (R.Rule Fun Var) deriving (Eq, Ord)

strict :: R.Rule Fun Var -> StrictVar
strict = StrictVar

newProblem :: PolyOrder -> TrsProblem Fun Var -> Optional Id (TrsProblem Fun Var)
newProblem order prob = Opt . Id $ prob 
  { strictRules = strictRules prob L.\\ (strict_ order)
  , weakRules   = L.nub $ weakRules prob ++ (strict_ order) }

certification :: PolyOrder -> Optional Id Certificate -> Certificate
certification order Null         = timeUBCert (degree order)
certification order (Opt (Id c)) = updateTimeUBCert c (`add` degree order)

entscheide :: PolyInterProcessor -> TrsProblem Fun Var -> IO (SMT.Sat PolyOrder)
entscheide p prob = do
  res :: SMT.Sat (M.Map PI.CoefficientVar Int, M.Map StrictVar Int) <- SMT.solve SMT.minismt $ do
    SMT.setLogic "QF_NIA"
    -- encode abstract interpretation
    (ebsi,coefficientEncoder) <- SMT.memo $ PI.PolyInter `liftM` T.mapM encode absi
    -- encode strict vars
    (svars, strictVarEncoder) <- SMT.memo $ mapM  (SMT.snvarm . StrictVar) rules

    let
      encodeStrictVar   = SMT.fm . (strictVarEncoder M.!)

    let
      p1 `gte` p2 = SMT.bigAnd [ c SMT..>= SMT.zero | c <- P.coefficients $ p1 `add` neg p2 ]
      interpreted = [ (r, PI.interpret ebsi (R.lhs r), PI.interpret ebsi (R.rhs r)) | r <- rules ]
      orderConstraints     =
        [ lhs `gte`  (rhs `add` P.constant (encodeStrictVar $ strict r))
        | (r,lhs,rhs) <- interpreted ]
      monotoneConstraints = [ SMT.fm c SMT..> SMT.zero | c <- M.elems coefficientEncoder ]
      rulesConstraint     = [ SMT.fm s SMT..> SMT.zero | r <- (strictRules prob), let s = encodeStrictVar (StrictVar r) ]
    --liftIO $ 
      --mapM_ putStrLn 
        --[ PP.display $ PP.pretty r PP.<$> PP.pretty lhs PP.<$> PP.pretty rhs PP.<$> PP.pretty (neg (rhs `add` P.constant (encodeStrictVar $ strict r))) PP.<$> PP.pretty (lhs `gte` (rhs `add` P.constant (encodeStrictVar $ strict r)))| (r,lhs,rhs) <- interpreted ]

    SMT.assert $ SMT.bigAnd orderConstraints
    SMT.assert $ SMT.bigAnd monotoneConstraints
    SMT.assert $ SMT.bigOr rulesConstraint

    return $ SMT.decode (coefficientEncoder, strictVarEncoder)
  return $ mkOrder `fmap`  res
  where
    encode :: Monad m => P.PolynomialView PI.CoefficientVar PI.SomeIndeterminate ->
      SMT.MemoSMT PI.CoefficientVar m (PI.SomePolynomial SMT.Expr)
    encode = P.pfromViewWithM enc where
      enc c
        | PI.restrict c = SMT.fm `liftM` SMT.snvarm c
        | otherwise  = SMT.fm `liftM` SMT.nvarm c
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
          Just i  -> i>0
          Nothing -> False
        strictOrder (R.Rule lhs rhs) = P.constantValue (PI.interpret pint lhs `add` neg (PI.interpret pint rhs)) > 0
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
    , PP.vcat [ PP.pretty (PI.interpret i rhs) PP.<+> PP.text "> " PP.<+> PP.pretty (PI.interpret i lhs) | R.Rule rhs lhs <- s]
    , PP.text "" 
    , PP.vcat [ PP.pretty (PI.interpret i rhs) PP.<+> PP.text ">=" PP.<+> PP.pretty (PI.interpret i lhs) | R.Rule rhs lhs <- w]
    ]

instance Show PolyInterProof where 
  show (PolyInterProof order) = show order

instance PP.Pretty PolyInterProof 
  where pretty (PolyInterProof order) = PP.pretty order

instance Xml.Xml PolyInterProof where
  toXml = undefined


