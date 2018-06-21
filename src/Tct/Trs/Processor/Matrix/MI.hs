{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module Tct.Trs.Processor.Matrix.MI
  (
  MI (..)
  , Kind (..)
  , MaximalMatrix (..)
  , TriangularBound (..)
  , jordan'
  , binaryJordan'
  , triangular'
  , almostTriangular'
  , algebraic'
  , catDirectImplicit'
  , sturm'
  , subresultantPRS'
  , budan'
  , eda'
  , ida'
  , mxeda
  , mxida
  ) where

import qualified Data.Foldable                   as F (toList)
import qualified Data.Ix                         as Ix
import qualified Data.List                       as L (partition, transpose)
import qualified Data.Map                        as M
import qualified Data.Set                        as S
import qualified Data.Vector                     as V
import qualified Data.Graph                      as G

import           SLogic.Logic.Matrix             (Matrix)
import qualified SLogic.Logic.Matrix             as Mat
import           SLogic.Smt                      ((.&&), (.*), (.+), (.<), (.<=), (.<=>), (.==), (.=>), (.>), (.>=))
import qualified SLogic.Smt                      as Smt

import qualified Tct.Core.Common.Pretty          as PP
import qualified Tct.Core.Common.SemiRing        as SR
import qualified Tct.Core.Common.Xml             as Xml
import qualified Tct.Core.Data                   as T

import           Tct.Common.ProofCombinators
import qualified Tct.Common.SMT                  as Smt (smtSolveTctM)

import qualified Data.Rewriting.Rule             as R
import           Data.Rewriting.Term             (Term)
import qualified Data.Rewriting.Term             as R

import           Tct.Trs.Data
import           Tct.Trs.Data.Arguments          (UsableArgs (..), UsableRules (..))
import qualified Tct.Trs.Data.Arguments          as Arg
import qualified Tct.Trs.Data.Problem            as Prob
import           Tct.Trs.Data.ProblemKind        (StartTerms (..))
import qualified Tct.Trs.Data.Rules              as RS
import qualified Tct.Trs.Data.RuleSelector       as RS
import qualified Tct.Trs.Data.Signature          as Sig
import           Tct.Trs.Encoding.Interpretation (Interpretation)
import qualified Tct.Trs.Encoding.Interpretation as I
import qualified Tct.Trs.Encoding.UsableRules    as UREnc


data MI = MI
  { miKind      :: Kind
  , miDimension :: Int
  , miUArgs     :: UsableArgs
  , miURules    :: UsableRules
  , miSelector  :: Maybe (ExpressionSelector F V)
  } deriving (Show)


data Kind
  = MaximalMatrix MaximalMatrix -- ^ use maximal matrices
  | Automaton (Maybe Int)       -- ^ use automaton
  | Unrestricted                -- ^ no restriction
  deriving (Show)

-- | shape restrictions for maximum matrix
data MaximalMatrix
  = UpperTriangular TriangularBound -- ^ restrict to upper triangular maximal matrices
  | LowerTriangular TriangularBound -- ^ restrict to lower triangular maximal matrices
  | AlmostTriangular Int            -- ^ restrict to almost triangular maximal matrices, ie if mat^k is triangular for some k
  | CaTDirectImplicit               -- ^ use constraints also implemented in the tool CaT
  | Sturm                           -- ^ use constraints derived from Sturm's Theorem
  | SubresultantPRS                 -- ^ use constraints derived from Subresultant PRS algorithm
  | Budan                           -- ^ use (incomplete) constraints derived from Budan-Fourier theorem
  | LikeJordan                      -- ^ restrict to maximal matrices which are similar to JNF
  | LikeBinaryJordan                -- ^ restrict to maximal matrices which are similar to JNF; entries are restricted to 0,1
  | MaxAutomaton (Maybe Int)        -- ^ use EDA/IDA on maximal matrix
  deriving (Show)

data TriangularBound
  = Implicit
  | Multiplicity (Maybe Int)
  deriving (Show)


--- * linear interpretation ------------------------------------------------------------------------------------------

-- | A type synonym for a nx1 dimensional Matrix.
type Vector c = Matrix c

-- | A type synonym for the dimension of a (square) Matrix.
type Dim = Int

type Deg = Int

-- | Canonical variable for the (abstract) interpretation.
newtype ArgPos = ArgPos Int deriving (Eq, Ord, Show, Enum)
instance PP.Pretty ArgPos where pretty (ArgPos i) = PP.text "x_" PP.<> PP.int i

-- | Linear Interpretation where coefficents are (square) matrices of the same dimension and the constant a column vector.
data LinearInterpretation v c = LInter
  { coefficients :: M.Map v (Matrix c)
  , constant     :: Vector c
  } deriving (Show, Functor, Foldable, Traversable)

instance (Smt.Decode m c a) => Smt.Decode m (LinearInterpretation var c) (LinearInterpretation var a) where
  decode = traverse Smt.decode

-- | Multiply a matrix with the all coefficients and the constant of the linear interpretation.
liProduct :: Smt.SSemiRing c => Matrix c -> LinearInterpretation v c -> LinearInterpretation v c
liProduct m li = LInter
  { coefficients = M.map (m .*) (coefficients li)
  , constant     = m .* constant li }

-- | Adds up the coefficients and the constants (+ given Vector) of a linear interpretation.
liBigAdd :: (Smt.AAdditive c, Ord v) => Vector c -> [LinearInterpretation v c] -> LinearInterpretation v c
liBigAdd v lis = LInter
  { coefficients = M.unionsWith (.+) (coefficients `fmap` lis)
  , constant     = foldr (.+) v (constant `fmap` lis) }

-- | Interpretation of a term wrt. to the given linear interpretation.
interpret' :: (Ord v, Ord f, Smt.SSemiRing c) => Dim -> Interpretation f (LinearInterpretation v' c) -> Term f v -> LinearInterpretation v c
interpret' dim (I.Interpretation ebsi) = I.interpretTerm interpretFun interpretVar where

  interpretFun f ts = liBigAdd c $ zipWith liProduct (M.elems cs) ts
    where LInter{coefficients=cs, constant=c} = ebsi M.! f
  interpretVar v    = LInter { coefficients = M.singleton v (Mat.eye dim), constant = Mat.zeros dim 1 }

-- | Returns coefficient matrices M1,...,Mn of a matrix interpretation
matrices :: Interpretation f (LinearInterpretation v k) -> [Matrix k]
matrices (I.Interpretation m) = concatMap (M.elems . coefficients) $ M.elems m

-- | Returns the maximal matrix of a matrix interpretation.
maximalMatrix' :: Dim -> Interpretation f (LinearInterpretation v Int) -> Matrix Int
maximalMatrix' dim mi = foldr (Mat.elementwise max) (Mat.zeros dim dim) (matrices mi)

-- | Returns the maximal (non Id) matrix of a matrix interpretation.
maxmimalNonIdMatrix :: Dim -> Interpretation f (LinearInterpretation v Int) -> Matrix Int
maxmimalNonIdMatrix dim mi =
  if mmx == zem && elem idm mxs
    then Mat.setEntry 1 (1,1) zem
    else mmx
  where
    mxs = matrices mi
    mmx = foldr (Mat.elementwise max) zem $ filter (/= idm) (matrices mi)
    idm = Mat.eye dim
    zem = Mat.zeros dim dim

-- | Restrict the interpretation to constructor start-terms for RC.
restrictInterpretation :: Ord f => StartTerms f -> Interpretation f (LinearInterpretation v k) -> Interpretation f (LinearInterpretation v k)
restrictInterpretation AllTerms{}                                    m  = m
restrictInterpretation BasicTerms{constructors=cs} (I.Interpretation m) = I.Interpretation $ M.filterWithKey restrict m
  where restrict f _ = f `S.member` cs


--- * abstract interpretation ----------------------------------------------------------------------------------------

-- | Abstract coefficients.
data AbsCoeff = Zero | One | ZeroOrOne | Natural deriving Show

-- | generate vector with urnestricted variable entries
absVector :: Dim -> Vector AbsCoeff
absVector dim = Mat.fromList dim 1 (repeat Natural)

-- | generate matrix with unrestricted variable entries
absStdMatrix :: Dim -> Matrix AbsCoeff
absStdMatrix dim = Mat.fromList dim dim (repeat Natural)

-- | generate matrix with unrestricted variable entries
absBinaryStdMatrix :: Dim -> Matrix AbsCoeff
absBinaryStdMatrix dim = Mat.fromList dim dim (repeat ZeroOrOne)

-- | generate matrix where entries in the diagonal are restricted
absMaxMatrix :: Dim -> Matrix AbsCoeff
absMaxMatrix = absEdaMatrix

-- | generate triangular matrix
absUTriMatrix, absLTriMatrix :: Dim -> Matrix AbsCoeff
absUTriMatrix dim =  Mat.matrix dim dim k where
  k (i,j)
    | i > j     = Zero
    | i == j    = ZeroOrOne
    | otherwise = Natural
absLTriMatrix dim =  Mat.matrix dim dim k where
  k (i,j)
    | i < j     = Zero
    | i == j    = ZeroOrOne
    | otherwise = Natural

absEdaMatrix :: Dim -> Matrix AbsCoeff
absEdaMatrix dim = Mat.matrix dim dim k
  where k (i,j) = if i == j then ZeroOrOne else Natural


-- | Generates an abstract interpretation for a given signature.
abstractInterpretation :: Ord f => StartTerms f -> Dim -> Kind -> Signature f -> M.Map f (LinearInterpretation ArgPos AbsCoeff)
abstractInterpretation st dim kind sig = case kind of
  MaximalMatrix (UpperTriangular _)  -> M.map (mk absStdMatrix) notrestricted `M.union` M.map (mk absUTriMatrix) restricted
  MaximalMatrix (LowerTriangular _)  -> M.map (mk absStdMatrix) notrestricted `M.union` M.map (mk absLTriMatrix) restricted
  MaximalMatrix (AlmostTriangular _) -> M.map (mk absStdMatrix) notrestricted `M.union` M.map (mk absMaxMatrix) restricted
  MaximalMatrix LikeJordan           -> M.map (mk absStdMatrix) masse
  MaximalMatrix LikeBinaryJordan     -> M.map (mk absBinaryStdMatrix) masse
  MaximalMatrix CaTDirectImplicit    -> M.map (mk absStdMatrix) masse
  MaximalMatrix Sturm                -> M.map (mk absStdMatrix) masse
  MaximalMatrix SubresultantPRS      -> M.map (mk absStdMatrix) masse
  MaximalMatrix Budan                -> M.map (mk absStdMatrix) masse
  MaximalMatrix (MaxAutomaton _)     -> M.map (mk absStdMatrix) notrestricted `M.union` M.map (mk absEdaMatrix) restricted

  Unrestricted                       -> M.map (mk absStdMatrix) masse
  Automaton _                        -> M.map (mk absStdMatrix) notrestricted `M.union` M.map (mk absEdaMatrix) restricted

  where
    mk mat ar = LInter
      { coefficients = M.fromAscList $ (\i -> (ArgPos i, mat dim))`fmap` [1..ar]
      , constant     = absVector dim }

    masse                     = Sig.toMap sig
    (restricted,notrestricted) = M.partitionWithKey (\f _ -> isRestricted f) masse
      where isRestricted f = case st of { AllTerms{} -> True; BasicTerms{constructors=cs} -> f `S.member` cs }

type Formula = Smt.Formula Int
type SmtM    = Smt.SmtSolverSt Int
type IExpr   = Smt.IExpr Int

-- | Maps the abstract coefficients of an abstract interpretation to SMT expressions.
encode' :: LinearInterpretation ArgPos AbsCoeff -> SmtM (LinearInterpretation ArgPos IExpr)
encode' = traverse k where
  k Zero      = return Smt.zero
  k One       = return Smt.one
  k ZeroOrOne = Smt.snvarM'
  k Natural   = Smt.nvarM'

setMonotone' :: LinearInterpretation ArgPos IExpr ->  [Int] -> Formula
setMonotone' LInter{coefficients=cs} poss = Smt.bigAnd $ k `fmap` poss
  where k i = let m = cs M.! ArgPos i in m Mat.!. (1,1) .> Smt.zero

setInFilter' :: LinearInterpretation ArgPos IExpr -> (Int -> Formula) -> Formula
setInFilter' LInter{coefficients=cs} inFilter = Smt.bigAnd (M.mapWithKey k cs)
  where k (ArgPos i) m = Smt.bigOr ((.> Smt.zero) `fmap` m) .=> inFilter i

addConstant' :: LinearInterpretation v IExpr -> IExpr -> LinearInterpretation v IExpr
addConstant' li@LInter{constant=c} e = let v = c Mat.!. (1,1) in li{constant=Mat.setEntry (v .+ e) (1,1) c}

gte' :: Ord v => LinearInterpretation v IExpr -> LinearInterpretation v IExpr -> Formula
gte' LInter{coefficients=cs1,constant=c1} LInter{coefficients=cs2,constant=c2} = gteMatrices cs1 cs2 .&& gteMatrix c1 c2
  where
    gteMatrices ms1 ms2 = Smt.bigAnd $ M.intersectionWith gteMatrix ms1 ms2
    gteMatrix m1 m2     = Smt.bigAnd $ zipWith (.>=) (Mat.toList m1) (Mat.toList m2)

instance I.AbstractInterpretation MI where
  type A MI = LinearInterpretation ArgPos AbsCoeff
  type B MI = LinearInterpretation ArgPos IExpr
  type C MI = LinearInterpretation V      IExpr

  encode _      = encode'
  interpret mi  = interpret' (miDimension mi)
  setMonotone _ = setMonotone'
  setInFilter _ = setInFilter'
  addConstant _ = addConstant'
  gte _         = gte'

entscheide :: MI -> Trs -> T.TctM (T.Return MI)
entscheide p@MI{miDimension=dim, miKind=kind} prob = do
  res :: Smt.Result ((I.InterpretationProof () (), I.Interpretation F (LinearInterpretation ArgPos Int), Maybe (UREnc.UsableSymbols F)), KindMatrices Int)
    <- Smt.smtSolveSt (Smt.smtSolveTctM prob) $ do
      encoding@(_,pint,_) <- I.orient p prob absi shift (miUArgs p == Arg.UArgs) (miURules p == Arg.URules)
      mp <- kindConstraints (Prob.startTerms prob) dim kind pint
      return $ Smt.decode (encoding, mp)
  case res of
    Smt.Sat (a,kmxs) -> let order = mkOrder a kmxs in
      T.succeedWith
        (Applicable $ Order order)
        (certification (Prob.startTerms prob) p order)
        (I.newProblem prob (mint_ order))

    Smt.Error s -> error ("Tct.Trs.Processor.Matrix.MI.entscheide: " ++ s) -- throwError (userError $ "Tct.Trs.Processor.Matrix.MI.entscheide: " ++ s)
    Smt.Unsat   -> error "Tct.Trs.Processor.Matrix.MI.entscheide: unsat"
    _           -> T.abortWith "Incompatible"

  where

    absi =  I.Interpretation $ abstractInterpretation (Prob.startTerms prob) dim kind sig
    sig   = Prob.signature prob
    shift = maybe I.All I.Shift (miSelector p)

    mkOrder (proof, inter, ufuns) kmxs = MatrixOrder
      { kind_         = kind
      , kindMatrices_ = kmxs
      , dim_          = dim
      , mint_         = proof
        { I.inter_     = inter
        , I.ufuns_     = UREnc.runUsableSymbols `fmap` ufuns
        , I.strictDPs_ = sDPs
        , I.strictTrs_ = sTrs
        , I.weakDPs_   = wDPs
        , I.weakTrs_   = wTrs }}
      where

          (sDPs,wDPs) = L.partition isStrict' (rs $ Prob.dpComponents prob)
          (sTrs,wTrs) = L.partition isStrict' (rs $ Prob.trsComponents prob)
          isStrict' (r,i) = r `RS.member` Prob.strictComponents prob && uncurry isStrict i

          rs trs =
            [ (r, (interpret' (miDimension p) inter  lhs, interpret' (miDimension p) inter  rhs))
            | r@(R.Rule lhs rhs) <- F.toList trs
            , isUsable ufuns r]

          isUsable Nothing _ = True
          isUsable (Just fs) (R.Rule lhs _) = either (const False) (`S.member` UREnc.runUsableSymbols fs) (R.root lhs)


--- * kind constraints -----------------------------------------------------------------------------------------------

-- | sums up the diagonal entries of the coefficients and constraints number of the non-zero entries
diagNonZerosConstraint :: Dim -> Int -> Interpretation f (LinearInterpretation v IExpr) -> SmtM ()
diagNonZerosConstraint dim deg inter = Smt.assert $
  if deg < dim
    then Smt.num deg .>= Smt.bigAdd nonZeros
    else Smt.top
  where
    nonZeros  = fmap (signum' . Smt.bigAdd) . Mat.getDiagonal . Mat.fold (Mat.zeros dim dim) $ matrices inter
    signum' a = Smt.ite (a .> Smt.zero) Smt.one Smt.zero

-- | restricts the trace of a matrix; if the matrix is triangular it restricts the number of the one entries
-- traceConstraint :: Int -> Matrix IExpr -> Formula
-- traceConstraint deg m =  Smt.num deg .>= Smt.bigAdd (Mat.getDiagonal m)

-- | constraints based on
-- |   Revisiting Matrix Interpretations for Polynomial Derivational Complexity of Term Rewriting [Neurauter, Zankl, Middeldorp],
-- |   methods (A) and (B)
-- | corresponds to CaT strategies "direct" and "implicit"; supports dimensions 2 and 3
catDirectImplicitConstraint :: Matrix IExpr -> SmtM (KindMatrices IExpr)
catDirectImplicitConstraint m =
  let dim = Mat.nrows m
  in case dim of
       1 ->
         Smt.assert (Mat.getEntry (1, 1) m .<= Smt.IVal 1) >> return (MMatrix m)
       2 -> Smt.assert direct >> return (MMatrix m)
         where direct -- "CaT direct": Revisiting Matrix Interpretations for Polynomial Derivational Complexity of Term Rewriting [Neurauter, Zankl, Middeldorp] (A)
                =
                 Smt.bigAnd
                   [ Smt.bigAdd
                       [ Smt.IVal 2
                       , Smt.INeg (Mat.getEntry (1, 1) m)
                       , Smt.INeg (Mat.getEntry (2, 2) m)
                       ] .>=
                     Smt.IVal 0
                   , Smt.bigAdd
                       [ Smt.IMul
                           (Mat.getEntry (1, 1) m)
                           (Mat.getEntry (2, 2) m)
                       , Smt.INeg
                           (Smt.IMul
                              (Mat.getEntry (1, 2) m)
                              (Mat.getEntry (2, 1) m))
                       , Smt.INeg (Mat.getEntry (1, 1) m)
                       , Smt.INeg (Mat.getEntry (2, 2) m)
                       , Smt.IVal 1
                       ] .>=
                     Smt.IVal 0
                   ]
       3 -> Smt.assert implicit >> return (MMatrix m)
         where p =
                 Smt.bigAdd
                   [ Mat.getEntry (1, 1) m
                   , Mat.getEntry (2, 2) m
                   , Mat.getEntry (3, 3) m
                   ]
               q =
                 Smt.bigAdd
                   [ Smt.IMul (Mat.getEntry (1, 2) m) (Mat.getEntry (2, 1) m)
                   , Smt.IMul (Mat.getEntry (1, 3) m) (Mat.getEntry (3, 1) m)
                   , Smt.IMul (Mat.getEntry (2, 3) m) (Mat.getEntry (3, 2) m)
                   , Smt.INeg
                       (Smt.IMul (Mat.getEntry (1, 1) m) (Mat.getEntry (2, 2) m))
                   , Smt.INeg
                       (Smt.IMul (Mat.getEntry (1, 1) m) (Mat.getEntry (3, 3) m))
                   , Smt.INeg
                       (Smt.IMul (Mat.getEntry (2, 2) m) (Mat.getEntry (3, 3) m))
                   ]
               r =
                 Smt.bigAdd
                   [ Smt.bigMul
                       [ Mat.getEntry (1, 1) m
                       , Mat.getEntry (2, 2) m
                       , Mat.getEntry (3, 3) m
                       ]
                   , Smt.bigMul
                       [ Mat.getEntry (1, 2) m
                       , Mat.getEntry (2, 3) m
                       , Mat.getEntry (3, 1) m
                       ]
                   , Smt.bigMul
                       [ Mat.getEntry (1, 3) m
                       , Mat.getEntry (2, 1) m
                       , Mat.getEntry (3, 2) m
                       ]
                   , Smt.INeg
                       (Smt.bigMul
                          [ Mat.getEntry (1, 3) m
                          , Mat.getEntry (2, 2) m
                          , Mat.getEntry (3, 1) m
                          ])
                   , Smt.INeg
                       (Smt.bigMul
                          [ Mat.getEntry (1, 2) m
                          , Mat.getEntry (2, 1) m
                          , Mat.getEntry (3, 3) m
                          ])
                   , Smt.INeg
                       (Smt.bigMul
                          [ Mat.getEntry (1, 1) m
                          , Mat.getEntry (2, 3) m
                          , Mat.getEntry (3, 2) m
                          ])
                   ]
               discriminant =
                 Smt.bigAdd
                   [ Smt.bigMul [p, p, q, q]
                   , Smt.INeg (Smt.bigMul [Smt.IVal 4, q, q, q])
                   , Smt.INeg (Smt.bigMul [Smt.IVal 4, p, p, p, r])
                   , Smt.INeg (Smt.bigMul [Smt.IVal 27, r, r])
                   , Smt.bigMul [Smt.IVal 18, p, q, r]
                   ]
               chiAtOne = Smt.bigAdd [Smt.INeg (Smt.IVal 1), p, q, r]
               chiAtMinusOne = Smt.bigAdd [Smt.IVal 1, p, Smt.INeg q, r]
               chiPrimeGeqZero =
                 Smt.Or
                   (Smt.IAdd (Smt.IMul p p) (Smt.INeg (Smt.IMul (Smt.IVal 3) q)) .<=
                    Smt.IVal 0)
                   (Smt.bigAnd
                      [ Smt.INeg (Smt.IVal 3) .<= p
                      , p .<= Smt.IVal 3
                      , Smt.INeg (Smt.IAdd q (Smt.IVal 3)) .<=
                        Smt.IMul (Smt.IVal 2) p
                      , Smt.IMul (Smt.IVal 2) p .<= Smt.IAdd q (Smt.IVal 3)
                      ])
               implicit -- "CaT implicit": Revisiting Matrix Interpretations for Polynomial Derivational Complexity of Term Rewriting [Neurauter, Zankl, Middeldorp] (B)
                =
                 Smt.Or
                   (Smt.bigAnd
                      [ discriminant .< Smt.IVal 0
                      , chiAtMinusOne .<= Smt.IVal 0
                      , chiAtOne .>= Smt.IVal 0
                      ])
                   (Smt.bigAnd
                      [ chiAtMinusOne .<= Smt.IVal 0
                      , chiAtOne .>= Smt.IVal 0
                      , chiPrimeGeqZero
                      ])
       _ -> error "dimension not supported" -- TODO: use factor method (C)

-- | constraints based on Sturm's Theorem; supports dimensions 2 and 3
sturmConstraint :: Matrix IExpr -> SmtM (KindMatrices IExpr)
sturmConstraint m =
  let dim = Mat.nrows m
  in case dim of
       1 ->
         Smt.assert (Mat.getEntry (1, 1) m .<= Smt.IVal 1) >> return (MMatrix m)
       2 -> Smt.assert sturm2D >> return (MMatrix m)
         where sturm2D =
                 Smt.bigAnd
                   [ Smt.bigAdd
                       [ Smt.IVal 1
                       , Smt.INeg (Mat.getEntry (1, 1) m)
                       , Smt.INeg (Mat.getEntry (2, 2) m)
                       , Smt.IMul
                           (Mat.getEntry (1, 1) m)
                           (Mat.getEntry (2, 2) m)
                       , Smt.INeg
                           (Smt.IMul
                              (Mat.getEntry (1, 2) m)
                              (Mat.getEntry (2, 1) m))
                       ] .>=
                     Smt.IVal 0
                   , Smt.bigAdd
                       [ Smt.IVal 2
                       , Smt.INeg (Mat.getEntry (1, 1) m)
                       , Smt.INeg (Mat.getEntry (2, 2) m)
                       ] .>=
                     Smt.IVal 0
                   ]
       3 -> Smt.assert sturm3D >> return (MMatrix m)
         where p =
                 Smt.bigAdd
                   [ Mat.getEntry (1, 1) m
                   , Mat.getEntry (2, 2) m
                   , Mat.getEntry (3, 3) m
                   ]
               q =
                 Smt.bigAdd
                   [ Smt.IMul (Mat.getEntry (1, 2) m) (Mat.getEntry (2, 1) m)
                   , Smt.IMul (Mat.getEntry (1, 3) m) (Mat.getEntry (3, 1) m)
                   , Smt.IMul (Mat.getEntry (2, 3) m) (Mat.getEntry (3, 2) m)
                   , Smt.INeg
                       (Smt.IMul (Mat.getEntry (1, 1) m) (Mat.getEntry (2, 2) m))
                   , Smt.INeg
                       (Smt.IMul (Mat.getEntry (1, 1) m) (Mat.getEntry (3, 3) m))
                   , Smt.INeg
                       (Smt.IMul (Mat.getEntry (2, 2) m) (Mat.getEntry (3, 3) m))
                   ]
               r =
                 Smt.bigAdd
                   [ Smt.bigMul
                       [ Mat.getEntry (1, 1) m
                       , Mat.getEntry (2, 2) m
                       , Mat.getEntry (3, 3) m
                       ]
                   , Smt.bigMul
                       [ Mat.getEntry (1, 2) m
                       , Mat.getEntry (2, 3) m
                       , Mat.getEntry (3, 1) m
                       ]
                   , Smt.bigMul
                       [ Mat.getEntry (1, 3) m
                       , Mat.getEntry (2, 1) m
                       , Mat.getEntry (3, 2) m
                       ]
                   , Smt.INeg
                       (Smt.bigMul
                          [ Mat.getEntry (1, 3) m
                          , Mat.getEntry (2, 2) m
                          , Mat.getEntry (3, 1) m
                          ])
                   , Smt.INeg
                       (Smt.bigMul
                          [ Mat.getEntry (1, 2) m
                          , Mat.getEntry (2, 1) m
                          , Mat.getEntry (3, 3) m
                          ])
                   , Smt.INeg
                       (Smt.bigMul
                          [ Mat.getEntry (1, 1) m
                          , Mat.getEntry (2, 3) m
                          , Mat.getEntry (3, 2) m
                          ])
                   ]
               z = Smt.IVal 0
               i = Smt.bigAdd [p, q, r, Smt.INeg (Smt.IVal 1)]
               ii =
                 Smt.bigAdd [Smt.IMul (Smt.IVal 2) p, q, Smt.INeg (Smt.IVal 3)]
               iii =
                 Smt.bigAdd
                   [ Smt.INeg (Smt.bigMul [Smt.IVal 2, p, p])
                   , Smt.INeg (Smt.IMul (Smt.IVal 6) q)
                   , Smt.INeg (Smt.IMul p q)
                   , Smt.INeg (Smt.IMul (Smt.IVal 9) r)
                   ]
               iv = Smt.IAdd (Smt.INeg (Smt.IMul p p)) (Smt.IMul (Smt.IVal 3) q)
               -- TODO: one disjunct is missing as we can't (or can we?) have fractions in our SMT encoding
               sturm3D =
                 Smt.bigOr
                   [ Smt.bigAnd [i .< z, ii .<= z, iii .<= z, iv .<= z]
                   , Smt.bigAnd [i .< z, ii .<= z, iii .> z, iv .> z]
                   , Smt.bigAnd [i .< z, ii .> z, iii .>= z, iv .> z]
                   , Smt.bigAnd [i .== z, ii .< z, iii .<= z, iv .<= z]
                   , Smt.bigAnd [i .== z, ii .< z, iii .> z, iv .> z]
                   , Smt.bigAnd [i .== z, ii .== z, iii .< z, iv .<= z]
                   --constraints where v is involved are missing
                   ]
       _ -> error "dimension not supported"

-- | constraints based on the Subresultant PRS algorithm; supports dimensions 2 and 3
subresultantPRSConstraint :: Matrix IExpr -> SmtM (KindMatrices IExpr)
subresultantPRSConstraint m =
 let dim = Mat.nrows m
 in case dim of
      1 -> Smt.assert (Mat.getEntry (1, 1) m .<= Smt.IVal 1) >> return (MMatrix m)
      2 -> Smt.assert subresultant2D >> return (MMatrix m) -- the subresultant algorithm constraint has additional disjuncts for the 2D case
        where subresultant2D =
                Smt.bigOr
                  [ Smt.bigAnd
                    [ Smt.bigAdd
                        [ Smt.IVal 1
                        , Smt.INeg (Mat.getEntry (1, 1) m)
                        , Smt.INeg (Mat.getEntry (2, 2) m)
                        , Smt.IMul
                            (Mat.getEntry (1, 1) m)
                            (Mat.getEntry (2, 2) m)
                        , Smt.INeg
                            (Smt.IMul
                               (Mat.getEntry (1, 2) m)
                               (Mat.getEntry (2, 1) m))
                        ] .>=
                      Smt.IVal 0
                    , Smt.bigAdd
                        [ Smt.IVal 2
                        , Smt.INeg (Mat.getEntry (1, 1) m)
                        , Smt.INeg (Mat.getEntry (2, 2) m)
                        ] .>=
                      Smt.IVal 0
                    ]
                  , Smt.bigAnd
                      [ Smt.bigAdd
                          [ Smt.IMul
                              (Smt.IAdd
                                 (Mat.getEntry (1, 1) m)
                                 (Smt.INeg (Mat.getEntry (2, 2) m)))
                              (Smt.IAdd
                                 (Mat.getEntry (1, 1) m)
                                 (Smt.INeg (Mat.getEntry (2, 2) m)))
                          , Smt.bigMul
                              [ Smt.IVal 4
                              , Mat.getEntry (1, 2) m
                              , Mat.getEntry (2, 1) m
                              ]
                          ] .<
                        Smt.IVal 0
                      , Smt.bigAdd
                          [ Smt.IMul
                              (Mat.getEntry (1, 1) m)
                              (Mat.getEntry (2, 2) m)
                          , Smt.INeg
                              (Smt.IMul
                                 (Mat.getEntry (1, 2) m)
                                 (Mat.getEntry (2, 1) m))
                          , Smt.INeg (Mat.getEntry (1, 1) m)
                          , Smt.INeg (Mat.getEntry (2, 2) m)
                          , Smt.IVal 1
                          ] .>
                        Smt.IVal 0
                      ]
                  , Smt.bigAnd
                      [ Smt.bigAdd
                          [ Smt.IMul
                              (Smt.IAdd
                                 (Mat.getEntry (1, 1) m)
                                 (Smt.INeg (Mat.getEntry (2, 2) m)))
                              (Smt.IAdd
                                 (Mat.getEntry (1, 1) m)
                                 (Smt.INeg (Mat.getEntry (2, 2) m)))
                          , Smt.bigMul
                              [ Smt.IVal 4
                              , Mat.getEntry (1, 2) m
                              , Mat.getEntry (2, 1) m
                              ]
                          ] .==
                        Smt.IVal 0
                      , Smt.bigAdd
                          [ Smt.IVal 2
                          , Smt.INeg (Mat.getEntry (1, 1) m)
                          , Smt.INeg (Mat.getEntry (2, 2) m)
                          ] .<
                        Smt.IVal 0
                      , Smt.bigAdd
                          [ Smt.IMul
                              (Mat.getEntry (1, 1) m)
                              (Mat.getEntry (2, 2) m)
                          , Smt.INeg
                              (Smt.IMul
                                 (Mat.getEntry (1, 2) m)
                                 (Mat.getEntry (2, 1) m))
                          , Smt.INeg (Mat.getEntry (1, 1) m)
                          , Smt.INeg (Mat.getEntry (2, 2) m)
                          , Smt.IVal 1
                          ] .==
                        Smt.IVal 0
                      ]
                  , Smt.bigAnd
                      [ Smt.bigAdd
                          [ Smt.IMul
                              (Smt.IAdd
                                 (Mat.getEntry (1, 1) m)
                                 (Smt.INeg (Mat.getEntry (2, 2) m)))
                              (Smt.IAdd
                                 (Mat.getEntry (1, 1) m)
                                 (Smt.INeg (Mat.getEntry (2, 2) m)))
                          , Smt.bigMul
                              [ Smt.IVal 4
                              , Mat.getEntry (1, 2) m
                              , Mat.getEntry (2, 1) m
                              ]
                          ] .==
                        Smt.IVal 0
                      , Smt.bigAdd
                          [ Smt.IVal 2
                          , Smt.INeg (Mat.getEntry (1, 1) m)
                          , Smt.INeg (Mat.getEntry (2, 2) m)
                          ] .<=
                        Smt.IVal 0
                      , Smt.bigAdd
                          [ Smt.IMul
                              (Mat.getEntry (1, 1) m)
                              (Mat.getEntry (2, 2) m)
                          , Smt.INeg
                              (Smt.IMul
                                 (Mat.getEntry (1, 2) m)
                                 (Mat.getEntry (2, 1) m))
                          , Smt.INeg (Mat.getEntry (1, 1) m)
                          , Smt.INeg (Mat.getEntry (2, 2) m)
                          , Smt.IVal 1
                          ] .<
                        Smt.IVal 0
                      ]
                  ]
      3 -> Smt.assert subresultant3D >> return (MMatrix m)
        where p =
                Smt.bigAdd
                  [ Mat.getEntry (1, 1) m
                  , Mat.getEntry (2, 2) m
                  , Mat.getEntry (3, 3) m
                  ]
              q =
                Smt.bigAdd
                  [ Smt.IMul (Mat.getEntry (1, 2) m) (Mat.getEntry (2, 1) m)
                  , Smt.IMul (Mat.getEntry (1, 3) m) (Mat.getEntry (3, 1) m)
                  , Smt.IMul (Mat.getEntry (2, 3) m) (Mat.getEntry (3, 2) m)
                  , Smt.INeg
                      (Smt.IMul (Mat.getEntry (1, 1) m) (Mat.getEntry (2, 2) m))
                  , Smt.INeg
                      (Smt.IMul (Mat.getEntry (1, 1) m) (Mat.getEntry (3, 3) m))
                  , Smt.INeg
                      (Smt.IMul (Mat.getEntry (2, 2) m) (Mat.getEntry (3, 3) m))
                  ]
              r =
                Smt.bigAdd
                  [ Smt.bigMul
                      [ Mat.getEntry (1, 1) m
                      , Mat.getEntry (2, 2) m
                      , Mat.getEntry (3, 3) m
                      ]
                  , Smt.bigMul
                      [ Mat.getEntry (1, 2) m
                      , Mat.getEntry (2, 3) m
                      , Mat.getEntry (3, 1) m
                      ]
                  , Smt.bigMul
                      [ Mat.getEntry (1, 3) m
                      , Mat.getEntry (2, 1) m
                      , Mat.getEntry (3, 2) m
                      ]
                  , Smt.INeg
                      (Smt.bigMul
                         [ Mat.getEntry (1, 3) m
                         , Mat.getEntry (2, 2) m
                         , Mat.getEntry (3, 1) m
                         ])
                  , Smt.INeg
                      (Smt.bigMul
                         [ Mat.getEntry (1, 2) m
                         , Mat.getEntry (2, 1) m
                         , Mat.getEntry (3, 3) m
                         ])
                  , Smt.INeg
                      (Smt.bigMul
                         [ Mat.getEntry (1, 1) m
                         , Mat.getEntry (2, 3) m
                         , Mat.getEntry (3, 2) m
                         ])
                  ]
              z = Smt.IVal 0
              e =
                Smt.bigAdd
                  [ Smt.bigMul [Smt.IVal 3, p, q]
                  , Smt.IMul (Smt.IVal 6) p
                  , Smt.IMul (Smt.IVal 8) q
                  , Smt.INeg (Smt.IMul (Smt.IVal 9) r)
                  , Smt.INeg (Smt.IVal 4)
                  ]
              f =
                Smt.bigAdd
                  [ Smt.INeg (Smt.bigMul [Smt.IVal 3, p, p, q, q])
                  , Smt.bigMul [Smt.IVal 8, p, q, q]
                  , Smt.bigMul [Smt.IVal 18, p, q, r]
                  , Smt.INeg (Smt.bigMul [Smt.IVal 12, p, r])
                  , Smt.INeg (Smt.bigMul [Smt.IVal 4, q, q, q])
                  , Smt.INeg (Smt.bigMul [Smt.IVal 4, q, q])
                  , Smt.INeg (Smt.bigMul [Smt.IVal 27, r, r])
                  , Smt.IMul (Smt.IVal 8) r
                  ]
              i = Smt.bigAdd [p, q, r, Smt.IVal 1]
              ii =
                Smt.bigAdd [Smt.IMul (Smt.IVal 2) p, q, Smt.INeg (Smt.IVal 3)]
              iii =
                Smt.bigAdd
                  [ Smt.IMul (Smt.IVal 6) p
                  , Smt.INeg (Smt.IMul (Smt.IVal 6) q)
                  , Smt.INeg (Smt.IVal 4)
                  ]
              subresultant3D =
                Smt.bigOr
                  [ Smt.bigAnd [i .== z, ii .< z, e .> z, iii .< z, f .== z]
                  , Smt.bigAnd [i .> z, ii .< z, e .> z, iii .< z, f .> z]
                  , Smt.bigAnd [i .> z, ii .== z, e .== z, iii .< z, f .> z]
                  , Smt.bigAnd [i .< z, ii .<= z, e .<= z, iii .>= z, f .== z]
                  , Smt.bigAnd [i .< z, e .> z, iii .< z, f .== z]
                  , Smt.bigAnd [i .< z, ii .> z, e .== z, iii .< z, f .== z]
                  , Smt.bigAnd [i .== z, ii .< z, e .<= z, iii .>= z, f .== z]
                  , Smt.bigAnd [i .== z, ii .== z, e .< z, iii .>= z, f .== z]
                  , Smt.bigAnd [i .== z, ii .== z, e .> z, iii .<= z, f .< z]
                  , Smt.bigAnd [i .== z, ii .== z, e .> z, iii .> z]
                  , Smt.bigAnd [i .== z, ii .== z, e .>= z, iii .>= z, f .>= z]
                  , Smt.bigAnd [i .== z, ii .> z, e .< z, iii .< z]
                  , Smt.bigAnd [i .== z, ii .> z, e .< z, f .< z]
                  , Smt.bigAnd [i .>= z, ii .> z, e .>= z, iii .>= z]
                  , Smt.bigAnd [i .== z, ii .> z, e .>= z, iii .< z, f .< z]
                  , Smt.bigAnd [i .> z, ii .< z, e .<= z, iii .>= z, f .< z]
                  , Smt.bigAnd [i .> z, ii .== z, e .< z, iii .>= z, f .< z]
                  , Smt.bigAnd [i .> z, ii .== z, e .== z, iii .>= z, f .<= z]
                  , Smt.bigAnd [i .> z, ii .== z, e .> z, iii .>= z]
                  , Smt.bigAnd [i .> z, ii .> z, e .< z, iii .>= z, f .< z]
                  , Smt.bigAnd [i .> z, ii .< z, e .== z, iii .< z]
                  , Smt.bigAnd [i .> z, e .< z, iii .< z]
                  ]
      _ -> error "dimension not supported"

-- | constraints based on Budan-Fourier theorem; these constraints are for dimension 3 but can easily be extended to other dimensions
budanConstraint :: Matrix IExpr -> SmtM (KindMatrices IExpr)
budanConstraint m =
  let dim = Mat.nrows m
  in case dim of
       3 -> Smt.assert noRootsGreaterOne >> return (MMatrix m)
         where p =
                 Smt.bigAdd
                   [ Mat.getEntry (1, 1) m
                   , Mat.getEntry (2, 2) m
                   , Mat.getEntry (3, 3) m
                   ]
               q =
                 Smt.bigAdd
                   [ Smt.IMul (Mat.getEntry (1, 2) m) (Mat.getEntry (2, 1) m)
                   , Smt.IMul (Mat.getEntry (1, 3) m) (Mat.getEntry (3, 1) m)
                   , Smt.IMul (Mat.getEntry (2, 3) m) (Mat.getEntry (3, 2) m)
                   , Smt.INeg
                       (Smt.IMul (Mat.getEntry (1, 1) m) (Mat.getEntry (2, 2) m))
                   , Smt.INeg
                       (Smt.IMul (Mat.getEntry (1, 1) m) (Mat.getEntry (3, 3) m))
                   , Smt.INeg
                       (Smt.IMul (Mat.getEntry (2, 2) m) (Mat.getEntry (3, 3) m))
                   ]
               r =
                 Smt.bigAdd
                   [ Smt.bigMul
                       [ Mat.getEntry (1, 1) m
                       , Mat.getEntry (2, 2) m
                       , Mat.getEntry (3, 3) m
                       ]
                   , Smt.bigMul
                       [ Mat.getEntry (1, 2) m
                       , Mat.getEntry (2, 3) m
                       , Mat.getEntry (3, 1) m
                       ]
                   , Smt.bigMul
                       [ Mat.getEntry (1, 3) m
                       , Mat.getEntry (2, 1) m
                       , Mat.getEntry (3, 2) m
                       ]
                   , Smt.INeg
                       (Smt.bigMul
                          [ Mat.getEntry (1, 3) m
                          , Mat.getEntry (2, 2) m
                          , Mat.getEntry (3, 1) m
                          ])
                   , Smt.INeg
                       (Smt.bigMul
                          [ Mat.getEntry (1, 2) m
                          , Mat.getEntry (2, 1) m
                          , Mat.getEntry (3, 3) m
                          ])
                   , Smt.INeg
                       (Smt.bigMul
                          [ Mat.getEntry (1, 1) m
                          , Mat.getEntry (2, 3) m
                          , Mat.getEntry (3, 2) m
                          ])
                   ]
               noRootsGreaterOne =
                 Smt.bigAnd
                   [ Smt.IAdd p (Smt.INeg $ Smt.IVal 3) .<= Smt.IVal 0
                   , Smt.bigAdd
                       [Smt.IMul (Smt.IVal 2) p, q, Smt.INeg $ Smt.IVal 3] .<=
                     Smt.IVal 0
                   , Smt.bigAdd [p, q, r, Smt.INeg $ Smt.IVal 1] .<= Smt.IVal 0
                   ]
       _ -> error "dimension not supported"

-- maximalMatrix :: (Smt.AAdditive a, Smt.Order a, Smt.Ite a, Smt.Boolean (Smt.B a)) => Int -> Interpretation f (LinearInterpretation v a) -> Matrix a
maximalMatrix :: Int -> Interpretation f (LinearInterpretation v IExpr) -> Matrix IExpr
maximalMatrix dim li = case matrices li of
  [] -> Mat.fromList dim dim (repeat Smt.zero)
  ms -> foldr1 (Mat.elementwise k) ms
    where k c acc = Smt.ite (c .> acc) c acc

-- | returns maximal matrix
maximalMatrixM :: Dim -> Interpretation f (LinearInterpretation v IExpr) -> SmtM (Matrix IExpr)
maximalMatrixM dim li = do
  mx1 <- sequenceA $ Mat.fromList dim dim (repeat Smt.nvarM')
  let mx2 = maximalMatrix dim li
  Smt.assert $ Smt.bigAnd (Mat.elementwise (.==) mx1 mx2)
  return mx1

triangularConstraint :: (Smt.SSemiRing a, Smt.Order a, Smt.Boolean (Smt.B a)) => Matrix a -> Smt.B a
triangularConstraint m = Smt.bigAnd
  [ k i j v  | let dim = Mat.nrows m, i <- [1..dim], j <- [1..dim] , i >= j, let v = Mat.entry i j m  ]
  where
    k i j v
      | i > j     = v .== Smt.zero
      | i == j    = v .<= Smt.one
      | otherwise = Smt.top

almostTriangularConstraint :: Int -> Matrix IExpr -> SmtM (KindMatrices IExpr)
almostTriangularConstraint pot m = Smt.assert (Smt.bany triangularConstraint mxs) >> return (AlmostTriangularMatrices mxs)
  where mxs = take (max 1 pot) (iterate (.*m) m)

-- | For a given maximal matrix finds a similar matrix in Jordan Normal Form. That is find P,J such that M = PJP-, J
-- in JNF and PP- = I.
-- When we restrict to natural numbers then P,P- are permutation matrices; hence we can restrict to 0,1 entries.
likeJordanConstraint' :: SmtM IExpr -> Matrix IExpr -> SmtM (KindMatrices IExpr)
likeJordanConstraint' varM m = do
  p <- someMatrix
  q <- someMatrix
  j <- someJordanMatrix
  Smt.assert $ (p.*q)    .==. idm
  Smt.assert $ (p.*m.*q) .==. j
  return $ LikeJordanMatrices (p,m,q,j)
  where
    someJordanMatrix  = someJordanMatrixM >>= \mx -> Smt.assert (Smt.bigAnd [ block (mx Mat.!.) i | i <- [1..pred dim] ]) >> return mx
      where
        block mx i = let j = succ i in mx (i,j) .== Smt.one .=> mx (i,i) .== mx (j,j)
        someJordanMatrixM = sequenceA $ Mat.matrix dim dim k
        k (i,j)
          | i == j      = Smt.snvarM'
          | succ i == j = Smt.snvarM'
          | otherwise   = return Smt.zero
    someMatrix = sequenceA $ Mat.fromList dim dim (repeat varM)
    m1 .==. m2 = Smt.bigAnd $ Mat.elementwise (.==) m1 m2
    idm = Mat.matrix dim dim $ \(i,j) -> if i == j then Smt.one else Smt.zero
    dim = Mat.nrows m

likeJordanConstraint :: Matrix IExpr -> SmtM (KindMatrices IExpr)
likeJordanConstraint = likeJordanConstraint' Smt.nvarM'

-- like 'likeJordanConstraint' but restricted to 0,1 entries
likeBinaryJordanConstraint :: Matrix IExpr -> SmtM (KindMatrices IExpr)
likeBinaryJordanConstraint = likeJordanConstraint' Smt.snvarM'

-- | Kind related matrices for proof output.
data KindMatrices a
  = NoMatrix
  | MMatrix (Matrix a)
  | AlmostTriangularMatrices [Matrix a]
  | LikeJordanMatrices (Matrix a, Matrix a, Matrix a, Matrix a)
  deriving (Show, Functor, Foldable, Traversable)

instance (Smt.Decode m c a) => Smt.Decode m (KindMatrices c) (KindMatrices a) where
  decode = traverse Smt.decode

-- nearlyTriangularConstraint :: Dim -> Interpretation f (LinearInterpretation v IExpr) -> SmtM ()
-- nearlyTriangularConstraint dim mi = Smt.assert $
--   Smt.bigAnd [ mij | let m = mtwo mxm, i <- [1..dim], j <- [1..dim], i > j, let mij = m Mat.!. (i,j) ]
--   where
--     mtwo mx = Mat.matrix dim dim $ \(i,j) -> Smt.bigAnd [ isZero (mx Mat.!. (i,k)) .|| isZero (mx Mat.!. (k,j)) | k <- [1..dim] ]
--     isZero = Smt.ball (.== Smt.zero)
--     mxm = Mat.fold (Mat.zeros dim dim) $ matrices mi

-- TODO: return JNF und AT matrix here
kindConstraints :: Ord f => StartTerms f -> Dim -> Kind -> Interpretation f (LinearInterpretation v IExpr) -> SmtM (KindMatrices IExpr)
kindConstraints st dim kind inter = case kind of
  MaximalMatrix (UpperTriangular (Multiplicity (Just deg))) -> diagNonZerosConstraint dim deg inter' >> return NoMatrix
  MaximalMatrix (LowerTriangular (Multiplicity (Just deg))) -> diagNonZerosConstraint dim deg inter' >> return NoMatrix
  MaximalMatrix (UpperTriangular _)                         -> return NoMatrix
  MaximalMatrix (LowerTriangular _)                         -> return NoMatrix

  MaximalMatrix (AlmostTriangular pot)                      -> mm >>= almostTriangularConstraint pot
  MaximalMatrix LikeJordan                                  -> mm >>= likeJordanConstraint
  MaximalMatrix LikeBinaryJordan                            -> mm >>= likeBinaryJordanConstraint
  MaximalMatrix CaTDirectImplicit                           -> mm >>= catDirectImplicitConstraint >> return NoMatrix
  MaximalMatrix Sturm                                       -> mm >>= sturmConstraint >> return NoMatrix
  MaximalMatrix SubresultantPRS                             -> mm >>= subresultantPRSConstraint >> return NoMatrix
  MaximalMatrix Budan                                       -> mm >>= budanConstraint >> return NoMatrix
  MaximalMatrix (MaxAutomaton mDeg)                         -> mm >>= \mx -> automatonConstraints st dim Nothing inter (Just mx) >> return (MMatrix mx) -- TODO: provide special instances

  Automaton mDeg                                            -> automatonConstraints st dim mDeg inter Nothing >> return NoMatrix
  Unrestricted                                              -> return NoMatrix
  where
    inter' = restrictInterpretation st inter
    mm     = maximalMatrixM dim inter'


--- ** automaton ------------------------------------------------------------------------------------------------------

type Q    = Int
type GOne = Q -> Q -> Formula
type GTwo = Q -> Q -> Q -> Q -> Formula
type DOne = Q -> Q -> Q -> Formula
type DTwo = Q -> Q -> Q -> Formula

ggeq :: [Matrix IExpr] -> Int -> Int -> Formula
ggeq mxs i j = Smt.bany k mxs
  where k m = Mat.entry i j m .> Smt.zero

ggrt :: [Matrix IExpr] -> Int -> Int -> Formula
ggrt mxs i j = Smt.bany k mxs
  where k m = Mat.entry i j m .> Smt.one

gOneConstraints :: [Q] -> [Matrix IExpr] -> GOne -> SmtM ()
gOneConstraints qs mxs gOne = reflexivity >> transitivity >> compatibility >> nocycle where
  reflexivity   = Smt.assert $ Smt.bigAnd [ gOne x x | x <- qs ]
  transitivity  = Smt.assert $ Smt.bigAnd [ (gOne x y .&& gOne y z) .=> gOne x z | x <- qs, y <- qs, z <- qs ]
  compatibility = Smt.assert $ Smt.bigAnd [ ggeq mxs x y .=> gOne x y | x <- qs, y <- qs ]
  nocycle       = Smt.assert $ Smt.bigAnd [ (gOne 1 y .&& ggrt mxs x y) .=> Smt.bnot (gOne y x) | x <- qs, y <- qs ]

-- (i,i') -> (j,j') iff there exists an A st A(i,j) > 0 and A(i',j') > 0
gTwoConstraints :: [Q] -> [Matrix IExpr] -> GTwo -> SmtM ()
gTwoConstraints qs mxs gtwo = Smt.assert $ Smt.bigAnd [ f i i' j j' | i <- qs, i' <- qs, j <- qs, j' <- qs ] where
  f i i' j j'   = gtwo i i' j j' .<=> Smt.bany (g i i' j j') mxs
  g i i' j j' m = (Mat.entry i j m .> Smt.zero) .&& (Mat.entry i' j' m .> Smt.zero)

-- difference to CAI paper
-- * restrict to reachable states
-- * for RC
dConstraints :: [Q] -> GOne -> GTwo -> DOne -> DTwo -> SmtM ()
dConstraints qs gOne gTwo dOne dTwo = foreapprox >> forecompat >> backapprox >> backcompat >> exactness where
  foreapprox  = Smt.assert $ Smt.bigAnd [ gOne 1 x .=> dOne x x x | x <- qs ]
  forecompat  = Smt.assert $ Smt.bigAnd [ (dOne i x y .&&  gTwo x y z u) .=>  dOne i z u | i <- qs, x <- qs, y <- qs, z <- qs, u <- qs ]
  backapprox  = Smt.assert $ Smt.bigAnd [ gOne 1 x .=>  dTwo x x x | x <- qs ]
  backcompat  = Smt.assert $ Smt.bigAnd [ (dTwo i x y .&&  gTwo z u x y) .=> dTwo i z u | i <- qs, x <- qs, y <- qs, z <- qs, u <- qs ]
  exactness   = Smt.assert $ Smt.bigAnd [ Smt.bnot (dOne i x y .&&  dTwo i x y) | i <- qs, x <- qs, y <- qs, x /= y ]

automatonConstraints :: Ord f => StartTerms f -> Dim -> Maybe Deg -> Interpretation f (LinearInterpretation v IExpr) -> Maybe (Matrix IExpr) -> SmtM ()
automatonConstraints st dim mDeg mi@(I.Interpretation m) mM = do
  gOneV <- V.replicateM (dim*dim) Smt.bvarM'
  let
    gOne i j     = gOneV V.! ix2 (i,j)
  mi' <- case st of
    BasicTerms{defineds=ds, constructors=cs} -> rcConstraints qs (matrices mids) gOne >> return mics
      where (mids, mics) = (I.Interpretation $ M.filterWithKey (restrict ds) m, I.Interpretation $ M.filterWithKey (restrict cs) m)
    _            -> return mi
  let
    mxs = case mM of
     Just mx -> [mx]
     Nothing -> matrices mi'
  case mDeg of
    Nothing    -> do
      gTwoV <- V.replicateM (dim*dim*dim*dim) Smt.bvarM'
      dOneV <- V.replicateM (dim*dim*dim) Smt.bvarM'
      dTwoV <- V.replicateM (dim*dim*dim) Smt.bvarM'
      let
        gTwo i j k l = gTwoV V.! ix4 (i,j,k,l)
        dOne i j k   = dOneV V.! ix3 (i,j,k)
        dTwo i j k   = dTwoV V.! ix3 (i,j,k)
      edaConstraints qs mxs gOne gTwo dOne dTwo

    (Just deg) -> do
      gThreeV <- V.replicateM (dim*dim*dim*dim*dim*dim) Smt.bvarM'
      trelV <- V.replicateM (dim*dim*dim) Smt.bvarM'
      irelV <- V.replicateM (dim*dim) Smt.bvarM'
      jrelV <- V.replicateM (dim*dim) Smt.bvarM'
      hrelV <- V.replicateM (dim*dim) Smt.bvarM'
      let
        gThree i j k x y z = gThreeV V.! ix6 ((i,j,k),(x,y,z))
        trel i j k   = trelV V.! ix3 (i,j,k)
        irel i j     = irelV V.! ix2 (i,j)
        jrel i j     = jrelV V.! ix2 (i,j)
        hrel i j     = hrelV V.! ix2 (i,j)

      idaConstraints qs mxs (max deg 1) gOne gThree trel irel jrel hrel

  where

    restrict fs f _ = f `S.member` fs

    qs = [1..dim]
    ix2 = Ix.index ((1,1),(dim,dim))
    ix3 = Ix.index ((1,1,1),(dim,dim,dim))
    ix4 = Ix.index ((1,1,1,1),(dim,dim,dim,dim))
    ix6 = Ix.index (((1,1,1),(1,1,1)),((dim,dim,dim),(dim,dim,dim)))


-- G(S)    - max (weighted) adjacency Matrix
-- G^2(S)  - (i,i') -> (j,j') if Ai,j and Ai',j' are positive
rcConstraints :: [Q] -> [Matrix IExpr] -> GOne -> SmtM ()
rcConstraints qs mxs gOne = Smt.assert $ Smt.bigAnd [ ggeq mxs 1 x .=> gOne 1 x | x <- qs ]

edaConstraints :: [Q] -> [Matrix IExpr] -> GOne -> GTwo -> DOne -> DTwo -> SmtM ()
edaConstraints qs mxs gOne gTwo dOne dTwo = gOneConstraints qs mxs gOne >> gTwoConstraints qs mxs gTwo >> dConstraints qs gOne gTwo dOne dTwo

type GThree = Q -> Q -> Q -> Q -> Q -> Q -> Formula
type T = Q -> Q -> Q -> Formula
type I = Q -> Q -> Formula
type J = Q -> Q -> Formula
type H = Q -> Q -> Formula


idaConstraints :: [Q] -> [Matrix IExpr] -> Deg -> GOne -> GThree -> T -> I -> J -> H -> SmtM ()
idaConstraints qs mxs deg gOne gThree trel irel jrel hrel = do
  gOneConstraints qs mxs gOne
  gThreeConstraints qs mxs gThree
  tConstraints qs gOne gThree trel
  iConstraints qs trel irel
  jConstraints qs gOne irel jrel
  hConstraints qs deg jrel hrel


-- G3
gThreeConstraints :: [Q] -> [Matrix IExpr] -> GThree -> SmtM ()
gThreeConstraints qs mxs gThree = Smt.assert $ Smt.bigAnd [ f i j k x y z | i <- qs, j <- qs, k <- qs, x <- qs, y <- qs, z <- qs ] where
  f i j k x y z   = gThree i j k x y z .<=> Smt.bany (g i j k x y z) mxs
  g i j k x y z m = (Mat.entry i x m .>= SR.one) .&& (Mat.entry j y m .>= SR.one) .&& (Mat.entry k z m .>= SR.one)

-- p /= q => T(p,p,q) /\ G3(T) => T
tConstraints :: [Q] -> GOne -> GThree -> T -> SmtM ()
tConstraints qs gOne gThree trel = Smt.assert $ initial .&& gThreeStep where
  initial    = Smt.bigAnd [ (gOne 1 x .&& gOne 1 y) .=> trel x x y | x <- qs, y <- qs, x /= y ]
  gThreeStep = Smt.bigAnd [ (trel x y z .&& gThree x y z u v w) .=> trel u v w | x <- qs, y <- qs, z <- qs, u <- qs, v <- qs, w <- qs ]

-- T(p,q,q) => I(p,q)
iConstraints :: [Q] -> T -> I -> SmtM ()
iConstraints qs trel irel = Smt.assert $ Smt.bigAnd [ trel x y y .=> irel x y | x <- qs, y <- qs, x /= y ]

-- J = I . R
jConstraints :: [Q] -> GOne -> I -> J -> SmtM ()
jConstraints qs gOne irel jrel = Smt.assert $ Smt.bigAnd [ f i j | i <- qs, j <- qs ]
  where f i j = jrel i j .<=> Smt.bany (\ k -> irel i k .&& gOne k j) qs

-- J(p,q) => h(p) > h(q)
hConstraints :: [Q] -> Int -> J -> H -> SmtM ()
hConstraints qs deg jrel hrel = Smt.assert $ unaryNotation .&& jDecrease where
  unaryNotation = Smt.bigAnd [ hrel x h .=> hrel x (h - 1) | x <- qs, h <- [2..deg - 1] ]
  jDecrease     = Smt.bigAnd [ f i j | i <- qs, j <- qs ]
  f i j         = jrel i j .=> Smt.bany (\ h -> hrel i h .&& Smt.bnot (hrel j h)) [1..deg - 1]


--- * processors -----------------------------------------------------------------------------------------------------

data MatrixOrder c = MatrixOrder
  { kind_         :: Kind
  , kindMatrices_ :: KindMatrices c
  , dim_          :: Dim
  , mint_         :: I.InterpretationProof (LinearInterpretation ArgPos c) (LinearInterpretation V c)
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

instance PP.Pretty Kind where
  pretty = PP.text . show

instance Show a => PP.Pretty (Matrix a) where
  pretty = PP.hcat . fmap PP.text . lines . Mat.prettyMatrix

ppMatrices :: Show a => [Matrix a] -> PP.Doc
ppMatrices = PP.vcat . fmap PP.hcat . L.transpose . fmap (fmap (PP.text . (' ':)) . lines . Mat.prettyMatrix)

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

    ppConstant i = PP.brackets $ PP.pretty (Mat.entry i 1 vec)


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
  toXml mx = case Mat.toCols mx of { [c] -> k c; cs -> Xml.elt "matrix" (k `fmap` cs)}
    where k cs  = Xml.elt "vector" [ Xml.elt "coefficient" [ Xml.elt "integer" [Xml.int c] ] | c <- cs]
  toCeTA   = Xml.toXml


instance Xml.Xml (LinearInterpretation ArgPos Int) where
  toXml lint = xsum (xcons (constant lint) :map xcoeff (M.toList $ coefficients lint) )
    where
      xpol p = Xml.elt "polynomial" [p]
      xsum   = xpol . Xml.elt "sum"
      xmul   = xpol . Xml.elt "product"
      xelm   = xpol . Xml.elt "coefficient"

      xcons c         = xelm [ Xml.toXml c ]
      xcoeff (v,m)    = xmul [ xelm [Xml.toXml m], xvar v ]
      xvar (ArgPos i) = xpol $ Xml.elt "variable" [Xml.int i]
  toCeTA = Xml.toXml

instance PP.Pretty (KindMatrices Int) where
  pretty NoMatrix                       = PP.empty
  pretty (MMatrix m)                    = ppMatrices [m]
  pretty (AlmostTriangularMatrices mxs) = ppMatrices mxs
  pretty (LikeJordanMatrices (p,m,q,j)) = ppMatrices [p,m,q,j]

instance PP.Pretty (MatrixOrder Int) where
  pretty order = PP.vcat
    [ PP.text "We apply a matrix interpretation of kind " PP.<> PP.pretty (kind_ order) PP.<> PP.char ':'
    , PP.pretty (kindMatrices_ order)
    , PP.pretty (mint_ order) ]

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
isStrict l@LInter{constant=c1} r@LInter{constant=c2} = isWeak l r &&  Mat.entry 1 1 c1 > Mat.entry 1 1 c2

isWeak :: LinearInterpretation a Int -> LinearInterpretation a Int -> Bool
isWeak LInter{constant=c1} LInter{constant=c2} = and $ zipWith (>=) (F.toList c1) (F.toList c2)

certification :: StartTerms F -> MI -> MatrixOrder Int -> T.Optional T.Id T.Certificate -> T.Certificate
certification st mi order cert = case cert of
  T.Null         -> T.timeUBCert bound
  T.Opt (T.Id c) -> T.updateTimeUBCert c (`SR.add` bound)
  where
    bound = upperbound st (miDimension mi) (miKind mi) (I.inter_ $ mint_ order)

countNonZeros :: Num c => Matrix c -> c
countNonZeros = sum . fmap signum . F.toList . Mat.getDiagonal


-- computes the degree of an automaton
-- cf. A. Weber and H. Seidl, On the degree of ambiguity of finite automata
--
-- For deg(M) = d, we have bound O(n^{d+1}).
--
-- * assumes not(EDA) or equivalently polynomial growth product matrix components
-- * does not trim the automaton
-- * returns O(n) if all matrices are zero-marices
-- * for maximalautomaton should be certifiable
--
-- TODO: test against CeTA and EDA/IDA
degM :: [Q] -> [Matrix Int] -> T.Complexity
degM [] _   = T.Poly (Just 0)
degM _  []  = T.Poly (Just 0)
degM q1 mxs = T.Poly $ Just $ succ $ maximum $ 0:[ height qi q5 | qi <- q5 ]
  where

  a .~ b = \m -> Mat.entry a b m > 0
  edges qs k     = [ (p, p, succs) | p <- qs, let succs = [ q | q <- qs, k p q ] ]
  fromEdges qs k = G.graphFromEdges $ edges qs k

  -- G1
  -- graph of the automaton
  (g1,_,v1) = G.graphFromEdges e1
  e1 = edges q1 to
    where to p q = any ( p .~ q ) mxs
  p `hasEdge1` q = ((\a b -> (a,b) `elem` G.edges g1) <$> v1 p <*> v1 q) == Just True

  -- G3
  -- graph of the triple product automaton
  q3 = [ (i,j,k) | i <- q1, j <- q1, k <- q1 ]
  (g3,_,v3) = fromEdges q3 to
    where to (i,j,k) (x,y,z) = any (\m -> (i .~ x) m && (j .~ y) m && (k .~ z) m) mxs
  p `hasPath3` q = (G.path g3 <$> v3 p <*> v3 q) == Just True

  -- G5
  -- SCC components of G1
  q5    = reverse $ G.flattenSCC `fmap` G.stronglyConnComp e1
  -- walk along SCC components of G1
  -- edges between components (bridges) have weight
  -- (i)  zero if they originate from G1, or
  -- (ii) one  if they they originate from G3 (ie compy with IDA)
  height _ []  = 0
  height _ [_] = 0
  height qk (ql:qs)
    | qk == ql  = maximum $ 0:[ k qk ql' (height ql' qs) | ql' <- qs ]
    | otherwise = height qk qs
    where
      k qi qj d
        | qi .>> qj = 1 + d
        | qi .~> qj = d
        | otherwise = 0
      qi .>> qj = or $ [ (p,p,q) `hasPath3` (p,q,q) | p <- qi, q <- qj ]
      qi .~> qj = or $ [       p `hasEdge1` q       | p <- qi, q <- qj ]



-- TODO: improve bound by explicitly computing it with IDA criterion
upperbound :: StartTerms F -> Dim -> Kind -> I.Interpretation F (LinearInterpretation ArgPos Int) -> T.Complexity
upperbound st dim kind li = case kind of
  MaximalMatrix (UpperTriangular Implicit)       -> T.Poly (Just dim)
  MaximalMatrix (UpperTriangular Multiplicity{}) -> degM [1..dim] [mm]
  MaximalMatrix (LowerTriangular Implicit)       -> T.Poly (Just dim)
  MaximalMatrix (LowerTriangular Multiplicity{}) -> T.Poly (Just $ countNonZeros mm)
  MaximalMatrix AlmostTriangular{}               -> T.Poly (Just dim) -- TODO: improve bound - take minimal multiplicty wrt. given triangular matrix
  MaximalMatrix LikeJordan                       -> T.Poly (Just dim) -- TODO: improve bound - take biggest jordan block
  MaximalMatrix LikeBinaryJordan                 -> T.Poly (Just dim) -- TODO: improve bound - take biggest jordan block
  MaximalMatrix CaTDirectImplicit                -> T.Poly (Just dim)
  MaximalMatrix Sturm                            -> T.Poly (Just dim)
  MaximalMatrix SubresultantPRS                  -> T.Poly (Just dim)
  MaximalMatrix Budan                            -> T.Poly (Just dim)
  MaximalMatrix (MaxAutomaton Nothing)           -> degM [1..dim] [mm]
  MaximalMatrix (MaxAutomaton (Just deg))        -> T.Poly (Just deg)

  Automaton Nothing                              -> T.Poly (Just dim)
  Automaton (Just deg)                           -> T.Poly (Just deg)
  Unrestricted                                   -> T.Exp  (Just 1)
  where
    li' = restrictInterpretation st li
    mm  = maximalMatrix' dim li'
-- TODO: change maximalNonIdMatrix; if M = eye then linear; otherwise count M', where M' = filter eye M

-- dimArg :: T.Argument 'T.Required Int
-- dimArg = T.nat "dimension" ["Specifies the dimension of the matrices used in the interpretation."]

-- degArg :: T.Argument 'T.Required Int
-- degArg = T.nat "degree" ["Specifies the maximal degree of the matrices used in the interpretation."]

-- mis :: String -> (Maybe Int -> Kind) -> T.Declaration ('[T.Argument 'T.Optional Int, T.Argument 'T.Optional (Maybe Int)] T.:-> T.Strategy Trs Trs)
-- mis s k = T.strategy s (dimArg `T.optional` 1, T.some degArg `T.optional` Nothing) $ \dim degM ->
--   T.processor $ MI{miKind=k degM, miDimension=dim,miUArgs=UArgs,miURules=URules,miSelector=Just (RS.selAnyOf RS.selStricts)}

-- mis :: Maybe (ExpressionSelector F V) -> Int -> Kind -> MI
-- mis sel dim kind = MI{miKind=kind, miDimension=dim,miUArgs=UArgs,miURules=URules,miSelector=sel}

-- upperTriangular, lowerTriangular, automaton :: Maybe (ExpressionSelector F V) -> Int -> Int -> T.Strategy Trs Trs
-- upperTriangular sel dim deg  = T.processor . mis sel dim . MaximalMatrix . UpperTriangular . Multiplicity $ if deg < dim then Just deg else Nothing
-- lowerTriangular sel dim deg  = T.processor . mis sel dim . MaximalMatrix . LowerTriangular . Multiplicity $ if deg < dim then Just deg else Nothing
-- automaton sel dim deg  = T.processor . mis sel dim . Automaton $ if deg < dim && deg > 0 then Just deg else Nothing

-- almostTriangular, likeJordan, maxAutomaton, unrestricted :: Maybe (ExpressionSelector F V) -> Int -> T.Strategy Trs Trs
-- almostTriangular sel dim  = T.processor . mis sel dim . MaximalMatrix $ AlmostTriangular 2
-- likeJordan sel dim        = T.processor . mis sel dim . MaximalMatrix $ LikeJordan
-- maxAutomaton sel dim      = T.processor . mis sel dim . MaximalMatrix $ MaxAutomaton
-- unrestricted sel dim      = T.processor . mis sel dim $ Unrestricted

-- 11cai setup

mkmi :: Int -> Kind -> TrsStrategy
mkmi dim kind = T.processor MI{miKind=kind, miDimension=dim,miUArgs=NoUArgs,miURules=NoURules,miSelector=Nothing}

jordan'           = \dim     -> mkmi dim (MaximalMatrix LikeJordan)
binaryJordan'     = \dim     -> mkmi dim (MaximalMatrix LikeBinaryJordan)
almostTriangular' = \dim     -> mkmi dim (MaximalMatrix $ AlmostTriangular 1)
triangular'       = \dim     -> mkmi dim (MaximalMatrix $ UpperTriangular (Multiplicity Nothing))
algebraic'        = \dim deg -> mkmi dim (MaximalMatrix $ UpperTriangular (Multiplicity (Just deg)))
catDirectImplicit' = \dim    -> mkmi dim (MaximalMatrix CaTDirectImplicit)
sturm'            = \dim     -> mkmi dim (MaximalMatrix Sturm)
subresultantPRS'  = \dim     -> mkmi dim (MaximalMatrix SubresultantPRS)
budan'            = \dim     -> mkmi dim (MaximalMatrix Budan)

eda' = \dim     -> mkmi' dim (Automaton Nothing)
ida' = \dim deg -> mkmi' dim (Automaton (Just deg))


mkmi' dim kind =
  T.processor MI{ miKind=kind
                , miDimension=dim
                , miUArgs=UArgs
                , miURules=URules
                , miSelector=Just (RS.selAnyOf RS.selStricts)
                }

mxida dim deg uargs urules sel =
  T.processor MI
    { miKind      = Automaton $ if deg' < dim' then Just deg' else Nothing
    , miDimension = dim'
    , miUArgs     = uargs
    , miURules    = urules
    , miSelector  = sel }
  where
    dim' = max 1 dim
    deg' = max 0 deg

mxeda dim = mxida dim dim
