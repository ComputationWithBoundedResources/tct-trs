{-# LANGUAGE ScopedTypeVariables #-}
{- Matrix Interpretations

Overview:

We differentiate how the actual bound is obtained:

Max: M = max (M1,..,Mn)
  for RC M1,...,Mn restricts to constructor start terms

  Shape is used to restrict the shape of M1,...,Mn and thus the shape of M:
    Triangular: lower diagonal entries are zero; diagonal entries at most one; upper diagonal entries are unrestricted
    AlmostTriangular: requires that M^n is Triangular for some n
  -- MS: some information obtained from tests
  -- due to the monotonicity constraint this seems not to work for DC and dim 2;
  -- use even potences only; there can be alternating matrices
  -- in practice considering potences 2 (maybe 4) should be enough
    Unrestricted: no restriction

  Bound:
    Implicit: if M is Triangular then O(d); otherwise Exp
    Triangular: if M is Triangular then count (non Id) non-zero entries; otherwise Exp
    Algebraic: multiplicity of eigenvalues of (minimal) characteristic polynomial
    Automaton: ?

Joint: M_1,...,M_n
  for RC M1,...,Mn restricts to constructor start terms

  Shape:
    EDA: upper Triangular; all entries are either 0 or 1
  Bound:
    EDA:
    not IDA:
-}
module Tct.Trs.Processor.Matrix.MI
  ( MI (..)
  , Kind (..)
  , Shape (..)
  , Bound (..)
  ) where


import Data.Monoid ((<>))
import qualified Data.Foldable                   as F (toList)

import qualified Tct.Core.Common.Pretty          as PP
import qualified Tct.Core.Common.SemiRing        as SR
import qualified Tct.Core.Common.Xml             as Xml

import           SLogic.Logic.Matrix             (Matrix)
import qualified SLogic.Logic.Matrix             as Mat
import           SLogic.Smt                      (Formula, IExpr, (.&&), (.+), (.=<), (.==), (.=>), (.>), (.>=))
import qualified SLogic.Smt                      as Smt

import qualified Data.List                       as L (partition)
import qualified Data.Map                        as M
import qualified Data.Set                        as S

import qualified Data.Rewriting.Rule             as R
import           Data.Rewriting.Term             (Term)
import qualified Data.Rewriting.Term             as R

import qualified Tct.Trs.Data.Rules              as RS

import           Tct.Core.Common.Error           (throwError)


import           Tct.Common.ProofCombinators
import qualified Tct.Common.SMT                  as Smt (smtSolveTctM)

import           Tct.Trs.Data
import           Tct.Trs.Data.Arguments          (UsableArgs (..), UsableRules (..))
import qualified Tct.Trs.Data.Arguments          as Arg
import qualified Tct.Trs.Data.Problem            as Prob
import           Tct.Trs.Data.ProblemKind        (StartTerms (..))
-- import qualified Tct.Trs.Data.ProblemKind            as Prob
import qualified Tct.Trs.Data.Signature          as Sig
import           Tct.Trs.Encoding.Interpretation (Interpretation)
import qualified Tct.Trs.Encoding.Interpretation as I
import qualified Tct.Trs.Encoding.UsableRules    as UREnc

import qualified Tct.Core.Data                   as T


data MI = MI
  { miKind      :: Kind
  , miDimension :: Int
  , miUArgs     :: UsableArgs
  , miURules    :: UsableRules
  , miSelector  :: Maybe (ExpressionSelector F V)
  } deriving (Show)

-- |
data Kind
  = Maximal Shape Bound
  -- | Joint
  deriving (Show)

-- | shape restrictions for maximum matrix
data Shape
  = Triangular
  | AlmostTriangular Int
  -- | Unrestricted
  -- | Unrestricted
  deriving (Show)

--
data Bound
  = Implicit
  | Ones (Maybe Int)
  -- | Algebraic
  -- | Automaton
  deriving (Show)



-- TODO: 
-- mmul m1 m2 = Mat.matrix (Mat.nrows m1) (Mat.ncols m2) $ \(i,j) -> Smt.bigAdd [ (m1 Mat.! (i,k)) .*  (m2 Mat.! (k,j)) | k <- [1 .. Mat.ncols m1] ]

-- liProduct' m li = LInter
--   { coefficients = M.map (m `mmul`) (coefficients li)
--   , constant     = m `mmul` (constant li) }


--- * matrix ---------------------------------------------------------------------------------------------------------

-- | A type synonym for a nx1 dimensional Matrix.
type Vector c = Matrix c

-- | A type synonym for the dimension of a (square) Matrix.
type Dim = Int

zeroVector :: Num c => Dim -> Matrix c
zeroVector dim = Mat.fromList dim 1 $ replicate dim 0

eye :: Num c => Dim -> Matrix c
eye = Mat.identity

--- * linear interpretation ------------------------------------------------------------------------------------------


-- | Linear Interpretation where coefficents are (square) matrices of the same dimension and the constant a column vector.
data LinearInterpretation v c = LInter
  { coefficients :: M.Map v (Matrix c)
  , constant     :: Vector c
  } deriving (Show, Functor, Foldable, Traversable)

instance (Smt.Decode m c a) => Smt.Decode m (LinearInterpretation var c) (LinearInterpretation var a) where
  decode = traverse Smt.decode

-- | Restrict the interpretation to to constructor start-terms for RC.
restrictInterpretation :: Ord f => StartTerms f -> Interpretation f (LinearInterpretation v k) -> Interpretation f (LinearInterpretation v k)
restrictInterpretation AllTerms{} m = m
restrictInterpretation BasicTerms{constructors=cs} (I.Interpretation m) = I.Interpretation $ M.filterWithKey restrict m
  where restrict f _ = f `S.member` cs

-- | Multiply a matrix with the all coefficients and the constant of the linear interpretation.
liProduct :: Num c => Matrix c -> LinearInterpretation v c -> LinearInterpretation v c
liProduct m li = LInter
  { coefficients = M.map (m *) (coefficients li)
  , constant     = m * (constant li) }

-- | Adds up the coefficients and the constants (+ given Vector) of a linear interpretation.
liBigAdd :: (Num c, Ord v) => Vector c -> [LinearInterpretation v c] -> LinearInterpretation v c
liBigAdd v lis = LInter
  { coefficients = M.unionsWith (+) (coefficients `fmap` lis)
  , constant     = foldr (+) v (constant `fmap` lis) }


--- * abstract interpretation ----------------------------------------------------------------------------------------


-- | Canonical variable for abstract interpretations.
newtype ArgPos = ArgPos Int deriving (Eq, Ord, Show, Enum)

instance PP.Pretty ArgPos where pretty (ArgPos i) = PP.char 'x' <> PP.int i

-- | Abstract coefficients.
data AbsCoeff = Zero | One | ZeroOrOne | Unrestricted deriving Show

-- | generate vector with urnestricted variable entries
absVector :: Int -> Vector AbsCoeff
absVector dim = Mat.fromList dim 1 (repeat Unrestricted)

-- | generate matrix with unrestricted variable entries
absStdMatrix :: Int -> Matrix AbsCoeff
absStdMatrix dim = Mat.fromList dim dim (repeat Unrestricted)

-- | generate triangular matrix
absTriMatrix :: Int -> Matrix AbsCoeff
absTriMatrix dim =  Mat.matrix dim dim k where
  k (i,j)
    | i > j     = Zero
    | i == j    = ZeroOrOne
    | otherwise = Unrestricted

-- | Generates an abstract interpretation for a given signature.
-- Enforces following properties.
--
abstractInterpretation :: Ord f => StartTerms f -> Kind -> Int -> Signature f -> M.Map f (LinearInterpretation ArgPos AbsCoeff)
abstractInterpretation st kind dim sig = case kind of
  (Maximal (AlmostTriangular _) _) -> M.map (mk absStdMatrix) masse
  (Maximal Triangular _)           -> M.map (mk absStdMatrix) unrestricted `M.union` M.map (mk absTriMatrix) restricted
  where
    mk mat ar = LInter
      { coefficients = M.fromAscList $ (\i -> (ArgPos i, mat dim))`fmap` [1..ar]
      , constant     = absVector dim }

    masse                     = Sig.toMap sig
    (restricted,unrestricted) = M.partitionWithKey (\f _ -> isRestricted f) masse
      where isRestricted f = case st of { AllTerms{} -> True; BasicTerms{constructors=cs} -> f `S.member` cs }


-- | Interpretation of a term wrt. to the given linear interpretation.
interpret' :: (Ord v, Ord f, Num c) => Dim -> Interpretation f (LinearInterpretation v' c) -> Term f v -> LinearInterpretation v c
interpret' dim (I.Interpretation ebsi) = I.interpretTerm interpretFun interpretVar where

  interpretFun f ts = liBigAdd c $ zipWith liProduct (M.elems cs) ts
    where LInter{coefficients=cs, constant=c} = ebsi M.! f
  interpretVar v    = LInter { coefficients = M.singleton v (eye dim), constant = zeroVector dim }


-- | Maps the abstract coefficients of an abstract interpretation to SMT expressions.
encode' :: Smt.Fresh w => LinearInterpretation ArgPos AbsCoeff -> Smt.SolverSt (Smt.SmtState w) (LinearInterpretation ArgPos (IExpr w))
encode' = traverse k where
  k Zero         = return Smt.zero
  k One          = return Smt.one
  k ZeroOrOne    = Smt.snvarM'
  k Unrestricted = Smt.nvarM'

setMonotone' :: LinearInterpretation ArgPos (IExpr w) ->  [Int] -> Formula w
setMonotone' LInter{coefficients=cs} poss = Smt.bigAnd $ k `fmap` poss
  where k i = let m = cs M.! (ArgPos i) in m Mat.! (1,1) .> Smt.zero

setInFilter' :: LinearInterpretation ArgPos (IExpr v) -> (Int -> Formula v) -> Formula v
setInFilter' LInter{coefficients=cs} inFilter = Smt.bigAnd (M.mapWithKey k cs)
  where k (ArgPos i) m = Smt.bigOr ((.> Smt.zero) `fmap` m) .=> inFilter i

addConstant' :: LinearInterpretation v (IExpr w) -> IExpr w -> LinearInterpretation v (IExpr w)
addConstant' li@LInter{constant=c} e = let v = c Mat.! (1,1) in li{constant=Mat.unsafeSet (v .+ e) (1,1) c}

gte' :: Ord v => LinearInterpretation v (IExpr w) -> LinearInterpretation v (IExpr w) -> Formula w
gte' LInter{coefficients=cs1,constant=c1} LInter{coefficients=cs2,constant=c2} = gteMatrices cs1 cs2 .&& gteMatrix c1 c2
  where
    gteMatrices ms1 ms2 = Smt.bigAnd $ M.intersectionWith gteMatrix ms1 ms2
    gteMatrix m1 m2     = Smt.bigAnd $ zipWith (.>=) (Mat.toList m1) (Mat.toList m2)

instance I.AbstractInterpretation MI where
  type A MI = LinearInterpretation ArgPos AbsCoeff
  type B MI = LinearInterpretation ArgPos (IExpr Int)
  type C MI = LinearInterpretation V      (IExpr Int)

  encode _      = encode'
  interpret mi  = interpret' (miDimension mi)
  setMonotone _ = setMonotone'
  setInFilter _ = setInFilter'
  addConstant _ = addConstant'
  gte _         = gte'



--- * kind constraints -----------------------------------------------------------------------------------------------

-- | limit non-zero entries in the maximal matrix
diagOnesConstraint :: Int -> Interpretation f (LinearInterpretation v (IExpr w)) -> Formula w
diagOnesConstraint deg inter = Smt.num deg .>= sum nonZeros
  where
    nonZeros  = F.toList . fmap signum' . sum . fmap diag $ (matrices inter)
    diag mx   = Mat.fromList 1 (Mat.nrows mx) $ F.toList (Mat.getDiag mx) -- FIXME: do not use sum on
    signum' a = Smt.ite (a .> 0) Smt.one Smt.zero

diagOnesConstraint' :: Int -> Matrix (IExpr w) -> Formula w
diagOnesConstraint' deg m =  Smt.num deg .>= sum (F.toList $ Mat.getDiag m)

-- | M1,...,Mn
matrices :: Interpretation f (LinearInterpretation v k) -> [Matrix k]
matrices (I.Interpretation m) = concatMap (M.elems . coefficients) $ M.elems m

-- | the maximal matrix
maxMatrix :: Num k => Interpretation f (LinearInterpretation v k) -> Matrix k
maxMatrix = sum . matrices

-- TODO: MS: class Boolean, AbstrOrd, SemiRing...

triangularConstraint :: Matrix (IExpr v) -> Formula v
triangularConstraint m = Smt.bigAnd
  [ k i j v  | let dim = Mat.nrows m, i <- [1..dim], j <- [1..dim] , i >= j, let v = Mat.unsafeGet i j m  ]
  where
    k i j v
      | i > j     = v .== Smt.zero
      | i == j    = v .=< Smt.one
      | otherwise = Smt.top


-- | ensure almost triangular


kindConstraints :: Ord f => StartTerms f -> Kind -> Interpretation f (LinearInterpretation v (IExpr w)) -> Formula w
kindConstraints st kind inter = case kind of
  Maximal Triangular (Ones (Just deg))             -> diagOnesConstraint deg inter'
  Maximal (AlmostTriangular pot) (Ones (Just deg)) -> Smt.bigOr (triangularConstraint `fmap` take (min 1 pot) (iterate (*mm) mm)) .&& diagOnesConstraint' deg mm
  Maximal (AlmostTriangular pot) _                 -> Smt.bigOr $ triangularConstraint `fmap` take (min 1 pot) (iterate (*mm) mm)
  _                                            -> Smt.top
  where
    inter' = restrictInterpretation st inter
    mm     = maxMatrix inter'


entscheide :: MI -> Trs -> T.TctM (T.Return MI)
entscheide p prob = do
  let
    orientM = do
      res@(_, (pint,_), _) <- I.orient p prob absi shift (miUArgs p == Arg.UArgs) (miURules p == Arg.URules)
      Smt.assertM $ return (kindConstraints (Prob.startTerms prob) (miKind p) pint)
      return $ res
    (ret, encoding)           = Smt.runSolverSt orientM Smt.initialState
    (apint,decoding,forceAny) = ret
    aorder = MatrixOrder
      { kind_ = miKind p
      , dim_  = miDimension p
      , mint_ = apint }

  entscheide1 p aorder encoding decoding forceAny prob
  where

    absi =  I.Interpretation $ abstractInterpretation (Prob.startTerms prob) (miKind p) (miDimension p) sig
    sig   = Prob.signature prob
    shift = maybe I.All I.Shift (miSelector p)


data MatrixOrder c = MatrixOrder
  { kind_ :: Kind
  , dim_  :: Dim
  , mint_ :: I.InterpretationProof (LinearInterpretation ArgPos c) (LinearInterpretation V c)
  } deriving (Show)

type NaturalMIProof = OrientationProof (MatrixOrder Int)

instance T.Processor MI where
  type ProofObject MI = ApplicationProof NaturalMIProof
  type In  MI         = Prob.Trs
  type Out MI         = Prob.Trs
  type Forking MI     = T.Optional T.Id

  execute p prob
    | Prob.isTrivial prob = T.abortWith (Closed :: ApplicationProof NaturalMIProof)
    | otherwise           = entscheide p prob


entscheide1 ::
  MI
  -> MatrixOrder c
  -> Smt.SmtState Int
  -> (I.Interpretation F (LinearInterpretation ArgPos (IExpr Int)), Maybe (UREnc.UsableEncoder F Int))
  -> I.ForceAny
  -> Prob.Trs
  -> T.TctM (T.Return MI)
entscheide1 p aorder encoding decoding forceAny prob
  | Prob.isTrivial prob = T.abortWith (Closed :: ApplicationProof NaturalMIProof)
  | otherwise           = do
    res :: Smt.Result (I.Interpretation F (LinearInterpretation ArgPos Int), Maybe (UREnc.UsableSymbols F))
      <- Smt.solve (Smt.smtSolveTctM prob) (encoding `assertx` forceAny srules) (Smt.decode decoding)
    case res of
      Smt.Sat a -> T.succeedWith  (Applicable $ Order order) (certification (Prob.startTerms prob) p order) (I.newProblem prob (mint_ order))
        where order = mkOrder a

      Smt.Error s -> throwError (userError s)
      _           -> T.abortWith (Applicable Incompatible :: ApplicationProof NaturalMIProof)
      where

        assertx st e = st {Smt.asserts = e: Smt.asserts st}
        srules = F.toList $ Prob.strictComponents prob

        mkOrder (inter, ufuns) = aorder { mint_ = mkInter (mint_ aorder) inter ufuns }
        mkInter aproof inter ufuns = aproof
          { I.inter_     = inter
          , I.ufuns_     = UREnc.runUsableSymbols `fmap` ufuns
          , I.strictDPs_ = sDPs
          , I.strictTrs_ = sTrs
          , I.weakDPs_   = wDPs'
          , I.weakTrs_   = wTrs' }
          where


          (sDPs,wDPs) = L.partition (\(r,i) -> r `RS.member` Prob.strictComponents prob && uncurry isStrict i) (rs $ Prob.dpComponents prob)
          (sTrs,wTrs) = L.partition (\(r,i) -> r `RS.member` Prob.strictComponents prob && uncurry isStrict i) (rs $ Prob.trsComponents prob)
          wDPs' = filter (uncurry isWeak . snd) wDPs
          wTrs' = filter (uncurry isWeak . snd) wTrs
          rs trs =
            [ (r, (interpret' (miDimension p) inter  lhs, interpret' (miDimension p) inter  rhs))
            | r@(R.Rule lhs rhs) <- F.toList trs
            , isUsable ufuns r]

          isUsable Nothing _ = True
          isUsable (Just fs) (R.Rule lhs _) = either (const False) (`S.member` UREnc.runUsableSymbols fs) (R.root lhs)


instance PP.Pretty Kind where
  pretty = PP.text . show

instance Show a => PP.Pretty (Matrix a) where
  pretty = PP.text . Mat.prettyMatrix

instance (Eq a, Show a, PP.Pretty a, PP.Pretty var, Num a) => PP.Pretty (LinearInterpretation var a) where
  pretty = pprintLInter "" 0 PP.pretty
  -- pretty LInter{coefficients=cs,constant=c} = PP.list' (M.elems cs ++ [c])


-- | pretty print a linear interpretation
pprintLInter :: (Eq a, PP.Pretty a, Num a)
  => String -- ^ name of linear interpretation
  -> Int -- ^ indendtation
  -> (var -> PP.Doc) -- ^ pretty print function for variables
  -> LinearInterpretation var a -- ^ the linear interpretation
  -> PP.Doc
pprintLInter name indend ppVar (LInter ms vec) =
  PP.vcat [ PP.text (whenBaseLine i (alignRight indend name))
         PP.<> ppRow i | i <- [1..d] ]
  where
    d  = Mat.nrows vec
    vs = [ (var, (show .  PP.pretty) `fmap` m) | (var, m) <- M.toList ms, m /= zeroMatrix]

    alignRight pad str = replicate diff ' ' ++ str
      where diff = pad - length str
    whenBaseLine :: Int -> String -> String
    whenBaseLine i str
      | floor mid  == i = str
      | otherwise = [' ' | _ <- str]
      where mid = fromIntegral (d + 1) / (2 :: Rational)

    ppConstant i = PP.brackets $ PP.pretty (Mat.unsafeGet i 1 vec)


    ppVariableCoefficient i m =
      PP.brackets (PP.fillSep [PP.text $ alignRight w cell | (cell, w) <- zip rs widths ])
      where
        rs = F.toList $ elts $ Mat.getRow i m
        widths = [collWidth j | j <- [1..d]]
        collWidth j = maximum $ 0 : [ length e | e <- F.toList $ elts $ Mat.getCol j m ]

    ppRow i = PP.hsep $
              PP.punctuate (PP.text $ whenBaseLine i " +") $
              [ ppVariableCoefficient i m
                PP.<+> PP.text (whenBaseLine i (show (ppVar var))) | (var,m) <- vs] ++ [ppConstant i]


    zeroMatrix = Mat.fromList d d (repeat 0)
    elts es = es


instance Xml.Xml (Matrix Int) where
  toXml mx = Xml.elt "matrix" $ k `fmap` [ Mat.getCol j mx | j <- [1..Mat.ncols mx] ]
    where k cs = Xml.elt "vector" [ Xml.elt "coefficient" [ Xml.elt "integer" [Xml.int c] ] | c <- F.toList cs]
  toCeTA   = Xml.toXml


instance Xml.Xml (LinearInterpretation ArgPos Int) where
  toXml lint = xsum (xcons (constant lint) :map xcoeff (M.toList $ coefficients lint) )
    where
      xpol p = Xml.elt "polynomial" [p]
      xsum   = xpol . Xml.elt "sum"
      xmul   = xpol . Xml.elt "product"
      xelm   = xpol . Xml.elt "coefficient"

      xcons c = xelm [ Xml.toXml c ]
      xcoeff (v,m) = xmul [ xelm [Xml.toXml m], xvar v]
      xvar (ArgPos i) = xpol $ Xml.elt "variable" [Xml.int i]


instance PP.Pretty (MatrixOrder Int) where
  pretty order = PP.vcat
    [ PP.text "We apply a matrix interpretation of kind " PP.<> PP.pretty (kind_ order) PP.<> PP.char ':'
    , PP.pretty $ PP.pretty (mint_ order) ]

instance Xml.Xml (MatrixOrder Int) where
  toXml order = 
    I.xmlProof (mint_ order) xtype where
      xtype = Xml.elt "type" [Xml.elt "matrixInterpretation" [xdom, xdim, xsdim]]
      xdom  = Xml.elt "domain" [Xml.elt "naturals" []]
      xdim  = Xml.elt "dimension" [ Xml.int (dim_ order)]
      xsdim = Xml.elt "strictDimension" [ Xml.int (1::Int) ]
  toCeTA order
    | True      = Xml.toXml order
    | otherwise = Xml.unsupported

isStrict :: LinearInterpretation a Int -> LinearInterpretation a Int -> Bool
isStrict l@LInter{constant=c1} r@LInter{constant=c2} = isWeak l r &&  Mat.unsafeGet 1 1 c1 > Mat.unsafeGet 1 1 c2

isWeak :: LinearInterpretation a Int -> LinearInterpretation a Int -> Bool
isWeak LInter{constant=c1} LInter{constant=c2} = and $ zipWith (>=) (F.toList c1) (F.toList c2)

certification :: StartTerms F -> MI -> MatrixOrder Int -> T.Optional T.Id T.Certificate -> T.Certificate
certification st mi order cert = case cert of
  T.Null         -> T.timeUBCert bound
  T.Opt (T.Id c) -> T.updateTimeUBCert c (`SR.add` bound)
  where
    bound = upperbound st (miDimension mi) (miKind mi) (I.inter_ $ mint_ order)

countNonZeros :: Num c => Matrix c -> c
countNonZeros = sum . fmap signum . Mat.getDiag

upperbound :: StartTerms F -> Dim -> Kind -> I.Interpretation F (LinearInterpretation ArgPos Int) -> T.Complexity
upperbound st dim kind li = case kind of
  Maximal Triangular Implicit         -> T.Poly (Just dim)
  Maximal Triangular (Ones _)         -> T.Poly (Just $ countNonZeros (maxMatrix li'))
  Maximal AlmostTriangular{} Implicit -> T.Poly (Just dim)
  Maximal AlmostTriangular{} (Ones _) -> T.Poly (Just $ countNonZeros (maxMatrix li'))
  where li' = restrictInterpretation st li

