{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Tct.Trs.Processor.Matrix.MatrixInterpretation
Description : Matrix interpretation over naturals
Copyright   : (c) since tct-trs
                  Martin Avanzini <martin.avanzini@uibk.ac.at>,
                  Andreas Kochesser <andreas.kochesser@uibk.ac.at>,
                  Georg Moser <georg.moser@uibk.ac.at>,
                  Michael Schaper <michael.schaper@uibk.ac.at>,
                  Maria Schett <maria.schett@uibk.ac.at>
              (c) since tct 2
                  Martin Avanzini <martin.avanzini@uibk.ac.at>,
                  Georg Moser <georg.moser@uibk.ac.at>,
                  Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     : see LICENSE
Maintainer  : andreas.kochesser@uibk.ac.at
Stability   : unstable
Portability : unportable

-}

module Tct.Trs.Processor.Matrix.NaturalMI
  (
  -- * Matrix interpretation
    matrixDeclaration
  , matrix
  , matrix'

  -- * Arguments
  , NaturalMIKind (..)
  , UsableArgs (..)
  , UsableRules (..)

  -- * Complexity Pair
  , matrixCPDeclaration
  , matrixCP
  , matrixCP'

  -- * Weight gap
  , WgOn (..)
  , weightGapDeclaration
  , weightgap
  , weightgap'
  ) where

-- general imports
import           Data.Monoid                                ((<>))
import qualified Control.Monad                              as CM
import qualified Data.Foldable                              as DF
import qualified Data.List                                  as List
import qualified Data.Map                                   as Map
import qualified Data.Maybe                                 as DM
import qualified Data.Set                                   as Set

import qualified Data.Traversable                           as DT


-- imports term-rewriting
import qualified Data.Rewriting.Rule                        as RR (Rule (..))
import qualified Data.Rewriting.Term                        as RT
import qualified Tct.Trs.Data                               as TD

-- imports tct-common
import qualified Tct.Common.ProofCombinators                as PC
import           Tct.Common.SMT                             (one, zero, (.<=>), (.==), (.=>), (.>), (.>=), (.&&), (.+))
import qualified Tct.Common.SMT                             as SMT


-- imports tct-core
import           Tct.Core.Common.Error                      (throwError)
import qualified Tct.Core.Common.Pretty                     as PP
import qualified Tct.Core.Common.SemiRing                   as SR
import qualified Tct.Core.Common.Xml                        as Xml
import qualified Tct.Core.Data                              as CD
import           Tct.Core.Parse            ()

-- imports tct-trs
import Tct.Trs.Data
import qualified Tct.Trs.Data.Arguments                     as Arg
import           Tct.Trs.Data.Arguments                     (UsableArgs (..), UsableRules (..))

import qualified Tct.Trs.Data.ComplexityPair as CP
import qualified Tct.Trs.Data.Problem                       as Prob
import qualified Tct.Trs.Data.ProblemKind                   as ProbK
import qualified Tct.Trs.Data.RuleSelector                  as RS
import qualified Tct.Trs.Data.Signature                     as Sig
import qualified Tct.Trs.Data.Rules as RS
import qualified Tct.Trs.Encoding.Interpretation            as I
import qualified Tct.Trs.Encoding.UsableRules               as UREnc
import qualified Tct.Trs.Encoding.UsablePositions           as UPEnc
import qualified Tct.Trs.Encoding.Matrix.MatrixInterpretation as MI
import qualified Tct.Trs.Encoding.Matrix.Matrix               as EncM

----------------------------------------------------------------------
-- keywords for text search:
-- #MI   matrix interpretation
-- ##MID matrix interpretation datatypes
-- ##MIF matrix interpretation functions
-- ##MIS matrix interpretation strategy declaration
-- ##MIP matrix interpretation processor
-- ##MIC matrix interpretation complexity pair
-- ##MIX matrix interpretation xml and pretty print
-- #WG   weightgap
-- ##WGD weightgap data types
-- ##WGP weightgap processor
-- ##WGS weightgap strategy declaration
-- ##WGX weightgap xml and prettyprint
----------------------------------------------------------------------


----------------------------------------------------------------------
-- #MI matrix interpretation
----------------------------------------------------------------------

{-

Interpret functions as linear equations over matrices, to orient
rules of a rewrite system.

Example:

f(x,y) = [ 1 0 ] * x + [ 2 1 ] * y + [ 1 ]
         [ 0 2 ]       [ 0 1 ]     + [ 1 ]

            ^             ^            ^
            |             |            |
             coefficients           constant

Variables x,y are vectors in matrix interpretations.
Usually the matrix interpretations require restrictions, like
a triangular shape for the coefficient to produce usable complexity
results.

-}


----------------------------------------------------------------------
-- ##MIF data types
----------------------------------------------------------------------

-- | Kind of the Matrix Interpretation
data NaturalMIKind
  = Algebraic    -- ^ Count number of ones in diagonal to compute induced complexity function.
  -- | Automaton    -- ^ Use automaton techniques to compute induced complexity function.
  | Triangular   -- ^ Use triangular matrices only.
  | Unrestricted -- ^ Put no further restrictions on the interpretations.
  deriving (Bounded, Enum, Eq, Show)


-- | Proof information for matrix Interpretations.
data MatrixOrder a
  = MatrixOrder { kind_ :: MI.MatrixKind F -- ^ restictions of the matrices used in the proof
                , dim_  :: Int -- ^ dimensions of the matrices used in the proof
                , mint_ :: I.InterpretationProof (MI.LinearInterpretation MI.SomeIndeterminate a) (MI.LinearInterpretation V a) -- ^ a proof which interprets canonical variables to user variables
                } deriving (Show)


-- | Type of the NatualMI processor. Stores information required to run the matrix interpretation processor
data NaturalMI = NaturalMI
                 { miDimension :: Int -- ^ dimension of matrices generated for the interpretation
                 , miDegree    :: Int -- ^ maximal allowed degree of the interpretation matrices
                 , miKind      :: NaturalMIKind -- ^ kind of interpretation
                 , uargs       :: Arg.UsableArgs -- ^ usable arguments
                 , urules      :: Arg.UsableRules -- ^ usable rules
                 , selector    :: Maybe (TD.ExpressionSelector F V)
                 } deriving (Show)

-- | Proof type of matrix interpretations
type NaturalMIProof = PC.OrientationProof (MatrixOrder Int)

-- | Type abbreviation
type SomeLInter a = MI.LinearInterpretation MI.SomeIndeterminate a

----------------------------------------------------------------------
-- ##MIF functions
----------------------------------------------------------------------

{- | update the certification (complexity result) depending on the matrix interpretation order.
  -}
certification ::
  NaturalMI
  -> MatrixOrder Int
  -> CD.Optional CD.Id CD.Certificate
  -> CD.Certificate
certification mi order cert = case cert of
  CD.Null         -> CD.timeUBCert bound
  CD.Opt (CD.Id c) -> CD.updateTimeUBCert c (`SR.add` bound)
  where
    bound = upperbound (miDimension mi) (miKind mi) (kind_ order) (I.inter_ $ mint_ order)

{- | convert an abstract linear interpretation into an SMT interpretation -}
toSMTLinearInterpretation :: SMT.Fresh w => SomeLInter (MI.MatrixInterpretationEntry fun) -> SMT.SmtSolverSt w (SomeLInter (SMT.IExpr w))
toSMTLinearInterpretation li = do
  constant <- toSMTVector $ MI.constant li
  coefficients <- mapM toSMTMatrix $ Map.assocs $ MI.coefficients li
  return $ MI.LInter (Map.fromList coefficients) constant
  where
    -- toSMTVector :: EncM.Vector (MI.MatrixInterpretationEntry fun)
    --                 -> SMT.SmtSolverSt w (EncM.Vector SMT.IExpr)
    toSMTVector (EncM.Vector vec) =
      fmap EncM.Vector (mapM entryToSMT vec)
    -- toSMTMatrix :: (MI.SomeIndeterminate, EncM.Matrix (MI.MatrixInterpretationEntry fun))
    --             -> SMT.SmtSolverSt w (SomeLInter SMT.IExpr) (EncM.Vector SMT.IExpr)(MI.SomeIndeterminate, EncM.Matrix SMT.IExpr)
    toSMTMatrix (i , EncM.Matrix vecs) = mapM toSMTVector vecs >>= (\m -> return (i, EncM.Matrix m))

{- | converts an abstract interpretation variable into a SMT variable -}
entryToSMT :: SMT.Fresh w => MI.MatrixInterpretationEntry fun
           -> SMT.SmtSolverSt w (SMT.IExpr w)
entryToSMT ent@(MI.MIVar{}) =
  if MI.restrict ent
  then SMT.snvarM'
  else SMT.nvarM'
entryToSMT MI.MIConstZero = return zero --SMT.numM 0
entryToSMT MI.MIConstOne = return one  -- SMT.numM 1


{- | Takes the SMT interpretations of functions to build an interpretation of a term -}
interpretf :: (SR.SemiRing a)
           => Int
           -> I.Interpretation F (SomeLInter a)
           -> RT.Term F V
           -> MI.LinearInterpretation V a
interpretf dim ebsi = I.interpretTerm interpretFun interpretVar
  where
    interpretFun f ts = addAll $ zipWith handleArg [1..] ts
      where
        find e a m =
          DM.fromMaybe
            (error $ "Tct.RS.Method.Matrix.NatrualMI.interpretf: Matrix " ++ e ++ " not found")
            (Map.lookup a m)
        finter = find ("interpretation " ++ show f) f (I.interpretations ebsi)
        coeffs = MI.coefficients finter
        fmatrix i = find ("coefficient " ++ show (f,i)) (MI.SomeIndeterminate i) coeffs
        addAll = MI.liBigAdd (MI.constant finter)
        handleArg = MI.liProduct . fmatrix

    interpretVar v = MI.LInter (Map.singleton v (EncM.identityMatrix dim)) (EncM.zeroVector dim)


{- | Counts non-zero entries (the degree) in the diagonal of a matrix. -}
countDiagonal :: NaturalMIKind
              -> Int
              -> (EncM.Matrix Int -> Int)
countDiagonal Triangular dim = const dim
countDiagonal _ _            = EncM.diagonalNonZeros

{- | Counts the degree depending of an interpretation on the matrix kind -}
upperbound ::
  Int -- ^ dimension
  -> NaturalMIKind
  -> MI.MatrixKind F
  -> I.Interpretation F (SomeLInter Int)
  -> CD.Complexity
upperbound dim intKind ordKind inter =
  case ordKind of
   MI.UnrestrictedMatrix{}                    -> CD.Exp (Just 1)
   MI.TriangularMatrix{}                      -> CD.Poly $ Just $ countDiagonal (intKind) (dim) $ maxNonIdMatrix (dim) inter
   MI.ConstructorBased cs _                   -> CD.Poly $ Just $ countDiagonal (intKind) (dim) $ maxNonIdMatrix (dim) inter'
     where inter' = inter{I.interpretations = filterCs $ I.interpretations inter}
           filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
   MI.EdaMatrix Nothing                       -> CD.Poly $ Just (dim)
   MI.EdaMatrix (Just n)                      -> CD.Poly $ Just n
   MI.ConstructorEda _ Nothing                -> CD.Poly $ Just (dim)
   MI.ConstructorEda _ (Just n)               -> CD.Poly $ Just n


{- | Checks wheter a matrix is different to the identity matrix of a given dimension. -}
maxNonIdMatrix :: Int
               -> I.Interpretation fun (MI.LinearInterpretation var Int)
               -> EncM.Matrix Int
maxNonIdMatrix dim mi =
  if any (elem (EncM.unit d) . Map.elems . MI.coefficients) (Map.elems $ I.interpretations mi) && maxi == EncM.zeroMatrix d d
    then EncM.unit 1
    else maxi
  where maxi = EncM.maximumMatrix max (d, d) $ Map.map (EncM.maximumMatrix max (d, d) . Map.filter (/= (EncM.unit d)) . MI.coefficients) $ I.interpretations mi
        d    = dim


{- | Checks if an concrete interpretation is of left-hand-side term and right-hand-side term is strict -}
isStrict :: MI.LinearInterpretation a Int -> MI.LinearInterpretation a Int -> Bool
isStrict l@(MI.LInter _ lconst) r@(MI.LInter _ rconst) = isWeak l r &&  EncM.vEntry 1 lconst  > EncM.vEntry 1 rconst

isWeak :: MI.LinearInterpretation a Int -> MI.LinearInterpretation a Int -> Bool
isWeak (MI.LInter _ lconst) (MI.LInter _ rconst) = and $ zipWith (>=) (DF.toList lconst) (DF.toList rconst)


{- | assert the matrix diagonal to be greather one iff a variable is one -}
diagOnesConstraint :: SMT.Fresh w => Int
                   -> I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w))
                   -> SMT.SmtSolverSt w (SMT.Formula w)
diagOnesConstraint deg mi = return $ SMT.num deg .>= SMT.bigAdd diagOnes
  where
    mis      = I.interpretations mi
    dim      = if Map.null mis then 0 else EncM.vDim $ MI.constant $ head $ Map.elems mis
    toD      = [1..dim]
    diagOnes = [ SMT.ite (f x) SMT.one SMT.zero | x <- toD ]
    f x      = SMT.bigOr $ map (SMT.bigOr . map (\ m -> EncM.mEntry x x m .>= SMT.one) . Map.elems . MI.coefficients) $ Map.elems mis

edaConstraints :: Int
               -> (Int -> Int -> SMT.Formula w)
               -> (Int -> Int -> Int -> SMT.Formula w)
               -> (Int -> Int -> Int -> SMT.Formula w)
               -> (Int -> Int -> Int -> Int -> SMT.Formula w)
               -> I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w))
               -> SMT.SmtSolverSt w (SMT.Formula w)
edaConstraints dim rel done dtwo gtwo mi =
  rConstraints dim rel mi
    `SMT.bandM` dConstraints dim rel done dtwo gtwo mi
    `SMT.bandM` gtwoConstraints dim gtwo mi
     -- goneConstraints do not exist

idaConstraints :: Int
               -> Int
               -> (Int -> Int -> SMT.Formula w)
               -> (Int -> Int -> SMT.Formula w)
               -> (Int -> Int -> SMT.Formula w)
               -> (Int -> Int -> SMT.Formula w)
               -> (Int -> Int -> Int -> SMT.Formula w)
               -> (Int -> Int -> Int -> Int -> Int -> Int -> SMT.Formula w)
               -> I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w))
               ->  SMT.SmtSolverSt w (SMT.Formula w)
idaConstraints dim deg rel irel jrel hrel trel gthree mi =
  rConstraints dim rel mi
    `SMT.bandM` tConstraints dim rel trel gthree mi
    `SMT.bandM` iConstraints dim irel trel mi
    `SMT.bandM` jConstraints dim rel irel jrel mi
    `SMT.bandM` hConstraints dim deg jrel hrel mi
    `SMT.bandM` gThreeConstraints dim gthree mi
    -- edaConstraints are not needed

dConstraints :: Int
             -> (Int -> Int -> SMT.Formula w)
             -> (Int -> Int -> Int -> SMT.Formula w)
             -> (Int -> Int -> Int -> SMT.Formula w)
             -> (Int -> Int -> Int -> Int -> SMT.Formula w)
             -> I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w))
             -> SMT.SmtSolverSt w (SMT.Formula w)
dConstraints dim rel done dtwo gtwo _ =
  return $ foreapprox .&& forecompat .&& backapprox .&& backcompat .&& exactness
  where
    toD         = [1..dim]
    foreapprox  = SMT.bigAnd [ rel 1 x .=>  done x x x | x <- toD ]
    forecompat  = SMT.bigAnd [ (done i x y .&& gtwo x y z u) .=> done i z u | i <- toD, x <- toD, y <- toD, z <- toD, u <- toD ]
    backapprox  = SMT.bigAnd [ rel 1 x .=> dtwo x x x | x <- toD ]
    backcompat  = SMT.bigAnd [ (dtwo i x y .&& gtwo z u x y) .=> dtwo i z u | i <- toD, x <- toD, y <- toD, z <- toD, u <- toD ]
    exactness   = SMT.bigAnd [ if x == y then SMT.top else SMT.bnot (done i x y .&& dtwo i x y) | i <- toD, x <- toD, y <- toD ]


hConstraints :: Int
             -> Int
             -> (Int -> Int -> SMT.Formula w)
             -> (Int -> Int -> SMT.Formula w)
             -> I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w))
             -> SMT.SmtSolverSt w (SMT.Formula w)
hConstraints dim deg jrel hrel _ = return $ unaryNotation .&& jDecrease
  where
    toD = [1..dim]
    unaryNotation = SMT.bigAnd [ hrel x h .=> hrel x (h - 1) | x <- toD, h <- [2..deg - 1] ]
    jDecrease = SMT.bigAnd [ f i j | i <- toD, j <- toD ]
    f i j = jrel i j .=> SMT.bigOr (map (\ h -> hrel i h .&& SMT.bnot (hrel j h)) [1..deg - 1])


iConstraints :: Int
             -> (Int -> Int -> SMT.Formula w)
             -> (Int -> Int -> Int -> SMT.Formula w)
             -> I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w))
             -> SMT.SmtSolverSt w (SMT.Formula w)
iConstraints dim irel trel _ = return $
  SMT.bigAnd [ if x == y then SMT.top else trel x y y .=> irel x y | x <- toD, y <- toD ]
  where
    toD = [1..dim]

jConstraints :: Int
             -> (Int -> Int -> SMT.Formula w)
             -> (Int -> Int -> SMT.Formula w)
             -> (Int -> Int -> SMT.Formula w)
             -> I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w))
             -> SMT.SmtSolverSt w (SMT.Formula w)
jConstraints dim rel irel jrel _ =
  return $ SMT.bigAnd [ f i j | i <- toD, j <- toD ]
  where
    toD = [1..dim]
    f i j = jrel i j .<=> SMT.bigOr (map (\ k -> irel i k .&& rel k j) toD)


rConstraints :: Int
             -> (Int -> Int -> SMT.Formula w)
             -> I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w))
             -> SMT.SmtSolverSt w (SMT.Formula w)
rConstraints dim rel mi =
  return $ reflexivity .&& transitivity .&& compatibility .&& nocycle
  where
    toD = [1..dim]
    reflexivity   = SMT.bigAnd $ map (\ x -> rel x x) toD
    transitivity  = SMT.bigAnd [ (rel x y .&& rel y z) .=> rel x z | x <- toD, y <- toD, z <- toD ]
    compatibility = SMT.bigAnd [ ggeqConstraint mi x y .=> rel x y | x <- toD, y <- toD ]
    nocycle       = SMT.bigAnd [ (rel 1 y .&& ggrtConstraint mi x y) .=> SMT.bnot (rel y x) | x <- toD, y <- toD ]

rcConstraints :: Int
              -> (Int -> Int -> SMT.Formula w)
             -> I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w))
              -> SMT.SmtSolverSt w (SMT.Formula w)
rcConstraints dim rel mi = return $ SMT.bigAnd [ ggeqConstraint mi 1 x .=> rel 1 x | x <- toD ]
  where
    toD = [1..dim]

tConstraints :: Int
             -> (Int -> Int -> SMT.Formula w)
             -> (Int -> Int -> Int -> SMT.Formula w)
             -> (Int -> Int -> Int -> Int -> Int -> Int -> SMT.Formula w)
             -> I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w))
             -> SMT.SmtSolverSt w (SMT.Formula w)
tConstraints dim rel trel gthree _ =
  return $ initial .&& gThreeStep
  where
    toD = [1..dim]
    initial = SMT.bigAnd [ if x == y then SMT.top else (rel 1 x .&& rel 1 y) .=> trel x x y | x <- toD, y <- toD ]
    gThreeStep = SMT.bigAnd [ (trel x y z .&& gthree x y z u v w) .=> trel u v w | x <- toD, y <- toD, z <- toD, u <- toD, v <- toD, w <- toD ]


gThreeConstraints :: Int
             -> (Int -> Int -> Int -> Int -> Int -> Int -> SMT.Formula w)
             -> I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w))
             -> SMT.SmtSolverSt w (SMT.Formula w)
gThreeConstraints dim gthree mi = return $
  SMT.bigAnd [ f i j k x y z | i <- toD, j <- toD, k <- toD, x <- toD, y <- toD, z <- toD ]
  where
    toD       = [1..dim]
    f i j k x y z = (gthree i j k x y z) .<=> SMT.bigOr (map (SMT.bigOr . map (g i j k x y z) . Map.elems . MI.coefficients) $ Map.elems $ I.interpretations mi)
    g i j k x y z m = (EncM.mEntry i x m .>= one) .&& (EncM.mEntry j y m .>= one) .&& (EncM.mEntry k z m .>= one)


gtwoConstraints :: Int
                -> (Int -> Int -> Int -> Int -> SMT.Formula w)
                -> I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w))
                -> SMT.SmtSolverSt w (SMT.Formula w)
gtwoConstraints dim gtwo mi =
  return $ SMT.bigAnd [ f i j k l | i <- toD, j <- toD, k <- toD, l <- toD ]
  where
    toD = [1..dim]
    f i j k l   = (gtwo i j k l) .<=> SMT.bigOr (map (SMT.bigOr . map (g i j k l) . Map.elems . MI.coefficients) $ Map.elems $ I.interpretations mi)
    g i j k l m = (EncM.mEntry i k m .>= one) .&& (EncM.mEntry j l m .>= one)


ggeqConstraint :: I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w)) -> Int -> Int
     -> SMT.Formula w
ggeqConstraint mi i j = SMT.bigOr (map (SMT.bigOr . map (\ m -> EncM.mEntry i j m .>= SR.one) . Map.elems . MI.coefficients) $ Map.elems $ I.interpretations mi)

ggrtConstraint :: I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w)) -> Int -> Int
     -> SMT.Formula w
ggrtConstraint mi i j = SMT.bigOr (map (SMT.bigOr . map (\ m -> EncM.mEntry i j m .> SR.one) . Map.elems . MI.coefficients) $ Map.elems $ I.interpretations mi)

mxKind :: NaturalMIKind -> Int -> Int -> StartTerms fun -> MI.MatrixKind fun
mxKind kind dim deg  st = case (kind, st) of
  (Unrestricted, _)                  -> MI.UnrestrictedMatrix
  (Triangular,   ProbK.BasicTerms{}) -> MI.ConstructorBased cs Nothing
  (Triangular,   ProbK.AllTerms{})   -> MI.TriangularMatrix Nothing
  (Algebraic,    ProbK.BasicTerms{}) -> MI.ConstructorBased cs md
  (Algebraic,    ProbK.AllTerms{})   -> MI.TriangularMatrix md
  -- (Automaton,    ProbK.BasicTerms{}) -> MI.ConstructorEda cs (min 1 `fmap` md)
  -- (Automaton,    ProbK.AllTerms{})   -> MI.TriangularMatrix (min 1 `fmap` md)
  where
    cs = ProbK.constructors st
    md = let d = max 0 deg in if d < dim then Just d else Nothing


{- | build constraints for an interpretation depending on the matrix kind -}
kindConstraints :: (Ord fun, SMT.Fresh w)
                => MI.MatrixKind fun
                -> I.Interpretation fun (MI.LinearInterpretation a (SMT.IExpr w))
                -> SMT.SmtSolverSt w (SMT.Formula w)
kindConstraints MI.UnrestrictedMatrix _                   = return SMT.top
kindConstraints (MI.TriangularMatrix Nothing) _           = return SMT.top
kindConstraints (MI.TriangularMatrix (Just deg)) absmi    = diagOnesConstraint deg absmi
kindConstraints (MI.ConstructorBased _  Nothing) _        = return SMT.top
kindConstraints (MI.ConstructorBased cs (Just deg)) absmi = diagOnesConstraint deg absmi'
  where absmi' = absmi{I.interpretations = filterCs $ I.interpretations absmi}
        filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
kindConstraints (MI.EdaMatrix Nothing) absmi = do
  relss  <- CM.replicateM dim $ CM.replicateM dim SMT.nvarM' -- index i,j represents relation(i,j)
  doness <- CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  dtwoss <- CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  gtwoss <- CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  let
    rel i j = relss!!i!!j .== one
    done i j k = doness!!i!!j!!k .== one
    dtwo i j k = dtwoss!!i!!j!!k .== one
    gtwo i j k l = gtwoss!!i!!j!!k!!l .== one

  edaConstraints dim rel done dtwo gtwo absmi
  where
    ints = I.interpretations absmi
    -- should we give dim as parameter to kindConstraints or extract it in the way done below?
    dim = if Map.null ints
          then 0
          else EncM.vDim $ MI.constant $ snd $ head $ Map.assocs ints
kindConstraints (MI.EdaMatrix (Just deg)) absmi = do
  relss    <- CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  iss      <- CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  jss      <- CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  hss      <- CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  tss      <- CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  gthreess <- CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim SMT.nvarM'

  let
    rel i j = relss!!i!!j .== one
    irel i j = iss!!i!!j .== one
    jrel i j = jss!!i!!j .== one
    hrel i j = hss!!i!!j .== one
    trel i j k = tss!!i!!j!!k .== one
    gthree i j k x y z = gthreess!!i!!j!!k!!x!!y!!z .== one

  idaConstraints dim deg rel irel jrel hrel trel gthree absmi
  where
    ints = I.interpretations absmi
    dim = if Map.null ints
          then 0
          else EncM.vDim $ MI.constant $ snd $ head $ Map.assocs ints
kindConstraints (MI.ConstructorEda cs mdeg) absmi = do
  relss    <- CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  iss      <- CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  jss      <- CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  hss      <- CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  tss      <- CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  gthreess <- CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  doness <- CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  dtwoss <- CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  gtwoss <- CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim $ CM.replicateM dim SMT.nvarM'
  let
    rel i j = relss!!i!!j .== one
    irel i j = iss!!i!!j .== one
    jrel i j = jss!!i!!j .== one
    hrel i j = hss!!i!!j .== one
    trel i j k = tss!!i!!j!!k .== one
    gthree i j k x y z = gthreess!!i!!j!!k!!x!!y!!z .== one
    done i j k = doness!!i!!j!!k .== one
    dtwo i j k = dtwoss!!i!!j!!k .== one
    gtwo i j k l = gtwoss!!i!!j!!k!!l .== one

  rcConstraints dim rel (absmi' ds)
    `SMT.bandM` maybe (edaConstraints dim rel done dtwo gtwo (absmi' cs))
                      (\ deg -> idaConstraints dim deg rel irel jrel hrel trel gthree (absmi' cs))
                      mdeg
  where
    ints = I.interpretations absmi
    dim = if Map.null ints
          then 0
          else EncM.vDim $ MI.constant $ snd $ head $ Map.assocs ints
    ds = (Map.keysSet $ I.interpretations absmi) Set.\\ cs
    absmi' fs = absmi{I.interpretations = filterFs fs $ I.interpretations absmi}
    filterFs fs = Map.filterWithKey (\f _ -> f `Set.member` fs)


entscheide :: NaturalMI -> Trs -> CD.TctM (CD.Return NaturalMI)
entscheide p@NaturalMI{miDimension=dim} prob = do
  res :: SMT.Result (I.InterpretationProof () (), I.Interpretation F (SomeLInter Int), Maybe (UREnc.UsableSymbols F))
    <- SMT.smtSolveSt (SMT.smtSolveTctM prob) $ do
      encoding@(_,pint,_) <- I.orient p prob absi shift (uargs p == Arg.UArgs) (urules p == Arg.URules)
      SMT.assertM $ kindConstraints kind pint
      return $ SMT.decode encoding
  case res of
    SMT.Sat a -> let order = mkOrder a in
      CD.succeedWith
        (PC.Applicable $ PC.Order order)
        (certification p order)
        (I.newProblem prob (mint_ order))

    SMT.Error s -> throwError (userError s)
    _           -> CD.abortWith "Incompatible"

  where

    absi =  I.Interpretation $ Map.mapWithKey (curry $ MI.abstractInterpretation kind (miDimension p)) (Sig.toMap sig)
    sig   = Prob.signature prob
    shift = maybe I.All I.Shift (selector p)
    kind = mxKind (miKind p) dim (miDegree p) (Prob.startTerms prob)

    mkOrder (proof, inter, ufuns) = MatrixOrder
      { kind_ = kind
      , dim_  = dim
      , mint_ = proof
        { I.inter_     = inter
        , I.ufuns_     = UREnc.runUsableSymbols `fmap` ufuns
        , I.strictDPs_ = sDPs
        , I.strictTrs_ = sTrs
        , I.weakDPs_   = wDPs
        , I.weakTrs_   = wTrs }}
      where

          (sDPs,wDPs) = List.partition isStrict' (rs $ Prob.dpComponents prob)
          (sTrs,wTrs) = List.partition isStrict' (rs $ Prob.trsComponents prob)
          isStrict' (r,i) = r `RS.member` Prob.strictComponents prob && uncurry isStrict i

          rs trs =
            [ (r, (interpretf (miDimension p) inter  lhs, interpretf (miDimension p) inter  rhs))
            | r@(RR.Rule lhs rhs) <- RS.toList trs
            , isUsable ufuns r]

          isUsable Nothing _ = True
          isUsable (Just fs) (RR.Rule lhs _) = either (const False) (`Set.member` UREnc.runUsableSymbols fs) (RT.root lhs)


-- entscheide1 ::
--   NaturalMI
--   -> MatrixOrder c
--   -> SMT.SmtState Int
--   -> (I.Interpretation F (SomeLInter (SMT.IExpr Int)), Maybe (UREnc.UsableEncoder F Int))
--   -> Prob.Trs
--   -> CD.TctM (CD.Return NaturalMI)
-- entscheide1 p aorder encoding decoding forceAny prob
--   | Prob.isTrivial prob = CD.abortWith (PC.Closed :: PC.ApplicationProof NaturalMIProof)
--   | otherwise           = do
--     res :: SMT.Result (I.Interpretation F (SomeLInter Int), Maybe (UREnc.UsableSymbols F))
--       <- SMT.solve (SMT.smtSolveTctM prob) (encoding `assertx` forceAny srules) (SMT.decode decoding)
--     case res of
--       SMT.Sat a -> CD.succeedWith  (PC.Applicable $ PC.Order order) (certification p order) (I.newProblem prob (mint_ order))
--         where order = mkOrder a

--       SMT.Error s -> throwError (userError s)
--       _           -> CD.abortWith (PC.Applicable PC.Incompatible :: PC.ApplicationProof NaturalMIProof)
--       where

--         assertx st e = st {SMT.asserts = e: SMT.asserts st}
--         srules = RS.toList $ Prob.strictComponents prob

--         mkOrder (inter, ufuns) = aorder { mint_ = mkInter (mint_ aorder) inter ufuns }
--         mkInter aproof inter ufuns = aproof
--           { I.inter_     = inter
--           , I.ufuns_     = UREnc.runUsableSymbols `fmap` ufuns
--           , I.strictDPs_ = sDPs
--           , I.strictTrs_ = sTrs
--           , I.weakDPs_   = wDPs'
--           , I.weakTrs_   = wTrs' }
--           where


--           (sDPs,wDPs) = List.partition (\(r,i) -> r `RS.member` Prob.strictComponents prob && uncurry isStrict i) (rs $ Prob.dpComponents prob)
--           (sTrs,wTrs) = List.partition (\(r,i) -> r `RS.member` Prob.strictComponents prob && uncurry isStrict i) (rs $ Prob.trsComponents prob)
--           wDPs' = filter (uncurry isWeak . snd) wDPs
--           wTrs' = filter (uncurry isWeak . snd) wTrs
--           rs trs =
--             [ (r, (interpretf (miDimension p) inter  lhs, interpretf (miDimension p) inter  rhs))
--             | r@(RR.Rule lhs rhs) <- RS.toList trs
--             , isUsable ufuns r]

--           isUsable Nothing _ = True
--           isUsable (Just fs) (RR.Rule lhs _) = either (const False) (`Set.member` UREnc.runUsableSymbols fs) (RT.root lhs)


----------------------------------------------------------------------
-- ##MIS matrix strategy declaration
----------------------------------------------------------------------


{- | create options/ configuration  for the NaturalMI strategy -}
matrixStrategy :: Int -> Int -> NaturalMIKind -> Arg.UsableArgs -> Arg.UsableRules
               -> Maybe (TD.ExpressionSelector F V)
               -> CD.Strategy Prob.Trs Prob.Trs
matrixStrategy dim deg nmiKind ua ur sl = CD.Apply $
  NaturalMI { miDimension = dim
            , miDegree = deg
            , miKind = nmiKind
            , uargs = ua
            , urules = ur
            , selector = sl
            }


{- | describes the strategy -}
description :: [String]
description =  [ "description of the matrix interpretation processor: TODO"               ]

{- | argument for the NaturalMIKind -}
nmiKindArg :: CD.Argument 'CD.Required NaturalMIKind
nmiKindArg = CD.flag "kind"
  ["Specifies the kind of the matrix interpretation."]

{- | dimension argument -}
dimArg :: CD.Argument 'CD.Required Int
dimArg = CD.nat "dimension" ["Specifies the dimension of the matrices used in the interpretation."]

{- | degree argument -}
degArg :: CD.Argument 'CD.Required Int
degArg = CD.nat "degree" ["Specifies the maximal degree of the matrices used in the interpretation."]

{- | rule selctor argument -}
slArg :: (Ord f, Ord v) => CD.Argument 'CD.Required (Maybe (TD.ExpressionSelector f v))
slArg = CD.some $ RS.selectorArg
  `CD.withName` "shift"
  `CD.withHelp`
    [ "This argument specifies which rules to orient strictly and shift to the weak components." ]

args ::
  ( CD.Argument 'CD.Optional Int
  , CD.Argument 'CD.Optional Int
  , CD.Argument 'CD.Optional NaturalMIKind
  , CD.Argument 'CD.Optional Arg.UsableArgs
  , CD.Argument 'CD.Optional Arg.UsableRules
  , CD.Argument 'CD.Optional (Maybe (RS.ExpressionSelector F V)) )
args =
  ( dimArg          `CD.optional` 1
  , degArg          `CD.optional` 1
  , nmiKindArg      `CD.optional` Algebraic
  , Arg.usableArgs  `CD.optional` Arg.UArgs
  , Arg.usableRules `CD.optional` Arg.URules
  , slArg           `CD.optional` Just (RS.selAnyOf RS.selStricts) )

{- | declare the matrix strategy -}
matrixDeclaration :: CD.Declaration (
  '[ CD.Argument 'CD.Optional Int
   , CD.Argument 'CD.Optional Int
   , CD.Argument 'CD.Optional NaturalMIKind
   , CD.Argument 'CD.Optional Arg.UsableArgs
   , CD.Argument 'CD.Optional Arg.UsableRules
   , CD.Argument 'CD.Optional (Maybe (RS.ExpressionSelector F V))
  ] CD.:-> CD.Strategy Prob.Trs Prob.Trs)
matrixDeclaration = CD.declare "matrix" description args matrixStrategy

matrix :: CD.Strategy Prob.Trs Prob.Trs
matrix = CD.deflFun matrixDeclaration

matrix' :: Int -> Int -> NaturalMIKind -> Arg.UsableArgs -> Arg.UsableRules
               -> Maybe (TD.ExpressionSelector F V)
               -> CD.Strategy Prob.Trs Prob.Trs
matrix' = CD.declFun matrixDeclaration


----------------------------------------------------------------------
-- ##MIP MI processor and abstract interpretation ##
----------------------------------------------------------------------

instance I.AbstractInterpretation NaturalMI where
  -- | Type of abstract matrix interpretations.
  type (A NaturalMI) = SomeLInter (MI.MatrixInterpretationEntry F)
  -- | Type of SMT interpretations. Abstract Varaibles replaced by SMT variables.
  type (B NaturalMI) = SomeLInter (SMT.IExpr Int)
  -- | Type of concrete interpretations. SMT variables replaced by integers.
  type (C NaturalMI) = MI.LinearInterpretation V (SMT.IExpr Int)

  {- transforms a single abstract interpretation of a function into an SMT interpretation. -}
  -- | encode :: NaturalMI -> A NaturalMI -> SMT.SolverStM SMT.Expr (B NaturalMI)
  encode _ = toSMTLinearInterpretation

  {- | Set the monotonicity requirement for a single function interpretation.
       Namely require the top left entry of the function parameters given in poss
       to be greater then one. -}
  -- setMonotone :: NaturalMI -> B NaturalMI -> [Int] -> SMT.Expr
  setMonotone _ v ps = setMonotone v ps

  {- | apply the inFilter function on indices corresponding to a non-zero matrix -}
  -- setInFilter :: NaturalMI -> B NaturalMI -> (Int -> SMT.Expr) -> SMT.Expr
  setInFilter _ (MI.LInter vmmap _) inFilter =
    SMT.bigAnd (Map.mapWithKey func vmmap)
    where
      func (MI.SomeIndeterminate i) m = SMT.bigOr (fmap ( .> SMT.zero) m) .=> inFilter i

  {- | Given an abstract interpretation get a concrete interpretation  for a Trs-Term. -}
  -- interpret   :: NaturalMI -> I.Interpretation F (B NaturalMI) -> RT.Term F V -> C NaturalMI
  interpret = interpretf . miDimension

  {- | Add a SMT value (smtexpr) to the constant part of an interpretation.
       This way we can get a strict or weak decrease requirement.
    -}
  -- addConstant :: NaturalMI -> C NaturalMI -> SMT.IExpr -> C NaturalMI
  addConstant _ (MI.LInter coeffs vec) smtexpr =
    MI.LInter coeffs vec'
    where
      vec' = EncM.adjustVector (smtexpr .+) 1 vec

  {- | compares two concrete linear interpretations with the 'greater or equal' relation -}
  -- gte :: NaturalMI -> C NaturalMI -> C NaturalMI -> SMT.Expr
  gte _ lint1 lint2 = gte lint1 lint2

gte :: Ord f => MI.LinearInterpretation f (SMT.IExpr w) -> MI.LinearInterpretation f (SMT.IExpr w) -> SMT.Formula w
gte (MI.LInter lcoeffs lconst) (MI.LInter rcoeffs rconst) =
  SMT.bigAnd zipmaps SMT..&& gteVec lconst rconst
  where
    zipmaps = Map.intersectionWith gteMatrix lcoeffs rcoeffs
    gteMatrix (EncM.Matrix m1) (EncM.Matrix m2) =
      SMT.bigAnd (zipWith gteVec m1 m2)
    gteVec (EncM.Vector v1) (EncM.Vector v2) =
      SMT.bigAnd $ zipWith (SMT..>=) v1 v2

setMonotone :: MI.SomeLinearInterpretation (SMT.IExpr w) -> [Int] -> (SMT.Formula w)
setMonotone (MI.LInter vmmap _) poss =
  SMT.bigAnd $ map setMonotonePos poss
  where
    toSI = MI.SomeIndeterminate
    setMonotonePos pos =
      case Map.lookup (toSI pos) vmmap of
      Just m -> EncM.mEntry 1 1 m SMT..> SMT.zero
      Nothing -> error "Tct.RS.Method.Matrix.NatrualMI.setMonotone: Argument Position not found"

setStronglyLinear :: SR.SemiRing c => Int -> MI.SomeLinearInterpretation c -> [Int] -> MI.SomeLinearInterpretation c
setStronglyLinear dim (MI.LInter vmmap cs) poss = MI.LInter (foldr k vmmap poss) cs
  where k pos = Map.adjust (const $ EncM.identityMatrix dim) (toEnum pos)


instance CD.Processor NaturalMI where
  type ProofObject NaturalMI = PC.ApplicationProof NaturalMIProof
  type In  NaturalMI         = Prob.Trs
  type Out NaturalMI         = Prob.Trs
  type Forking NaturalMI     = CD.Optional CD.Id

  {- | Decides whether applying the NaturalMI processor makes progress or not -}
  execute p prob
    | Prob.isTrivial prob = CD.abortWith (PC.Closed :: PC.ApplicationProof NaturalMIProof)
    | otherwise           = entscheide p prob


----------------------------------------------------------------------
-- ##MIC matrix interpretation complexity pair
----------------------------------------------------------------------


instance CP.IsComplexityPair NaturalMI where
  solveComplexityPair p sel prob = do
  pt <- CD.evaluate (CD.Apply p{selector=Just sel}) (CD.Open prob)
  return $ if CD.isFailing pt
    then Left $ "application of cp failed"
    else case CD.open pt of
      [nprob] -> Right $ CP.ComplexityPairProof
        { CP.result = pt
        , CP.removableDPs = Prob.strictDPs prob `RS.difference` Prob.strictDPs nprob
        , CP.removableTrs = Prob.strictTrs prob `RS.difference` Prob.strictTrs nprob }
      _ -> error "Tct.RS.Method.Poly.NaturalMI.solveComplexityPair: the impossible happened"

matrixComplexityPair :: Int -> Int -> NaturalMIKind -> Arg.UsableArgs -> Arg.UsableRules -> CP.ComplexityPair
matrixComplexityPair dim deg nmiKind ua ur = CP.toComplexityPair $
  NaturalMI { miDimension = dim
            , miDegree = deg
            , miKind = nmiKind
            , uargs = ua
            , urules = ur
            , selector = Nothing
            }

matrixCPDeclaration :: CD.Declaration (
  '[ CD.Argument 'CD.Optional Int
   , CD.Argument 'CD.Optional Int
   , CD.Argument 'CD.Optional NaturalMIKind
   , CD.Argument 'CD.Optional Arg.UsableArgs
   , CD.Argument 'CD.Optional Arg.UsableRules ]
  CD.:-> CP.ComplexityPair )
matrixCPDeclaration = CD.declare "matrixCP" description argsCP matrixComplexityPair
  where
    argsCP =
      ( dimArg          `CD.optional` 1
      , degArg          `CD.optional` 1
      , nmiKindArg      `CD.optional` Algebraic
      , Arg.usableArgs  `CD.optional` Arg.UArgs
      , Arg.usableRules `CD.optional` Arg.URules )

matrixCP :: CP.ComplexityPair
matrixCP = CD.deflFun matrixCPDeclaration

matrixCP' :: Int -> Int -> NaturalMIKind -> Arg.UsableArgs -> Arg.UsableRules -> CP.ComplexityPair
matrixCP' = CD.declFun matrixCPDeclaration


----------------------------------------------------------------------
-- ##MIX matrix interpretation prettyprint and xml
----------------------------------------------------------------------


instance PP.Pretty (MatrixOrder Int) where
  pretty order = PP.vcat
    [ PP.text "We apply a matrix interpretation of kind " PP.<> PP.pretty (kind_ order) PP.<> PP.char ':'
    , PP.pretty $ PP.pretty (mint_ order) ]

instance Xml.Xml (MatrixOrder Int) where
  toXml order = I.xmlProof (mint_ order) xtype where
    xtype = Xml.elt "type" [Xml.elt "matrixInterpretation" [xdom, xdim, xsdim]]
    xdom  = Xml.elt "domain" [Xml.elt "naturals" []]
    xdim  = Xml.elt "dimension" [ Xml.int (dim_ order)]
    xsdim = Xml.elt "strictDimension" [ Xml.int (1::Int) ]
  toCeTA order
    | True      = Xml.toXml order -- FIXME: MS: add sanity check; ceta supports definitely triangular; does it support algebraic ?
    | otherwise = Xml.unsupported


----------------------------------------------------------------------
-- #WG weightgap
----------------------------------------------------------------------

----------------------------------------------------------------------
-- ##WGD datatypes
----------------------------------------------------------------------


data WgOn
  = WgOnTrs -- ^ Orient at least all non-DP rules.
  | WgOnAny -- ^ Orient some rule.
  deriving (Eq, Show, Bounded, Enum)

data WeightGap = WeightGap
  { wgDimension :: Int
  , wgDegree    :: Int
  , wgKind      :: NaturalMIKind
  , wgUArgs     :: UsableArgs
  , wgOn        :: WgOn
  } deriving (Show)

data WeightGapOrder =  WeightGapOrder
  { wgProof       :: MatrixOrder Int
  , wgConstGrowth :: Bool }
  deriving (Show)

type WeightGapProof = PC.OrientationProof WeightGapOrder

----------------------------------------------------------------------
-- ##WGP weightgap processor
----------------------------------------------------------------------

instance CD.Processor WeightGap where
  type ProofObject WeightGap = PC.ApplicationProof WeightGapProof
  type In  WeightGap         = Prob.Trs
  type Out WeightGap         = Prob.Trs

  execute p prob
    | Prob.isTrivial prob = CD.abortWith (PC.Closed :: PC.ApplicationProof WeightGapProof)
    | (wgOn p == WgOnTrs) && RS.null (Prob.strictTrs prob) = incompatible
    | otherwise = do
      res <- wgEntscheide p prob
      case res of
        SMT.Sat order -> CD.succeedWith (PC.Applicable $ PC.Order order) cert (CD.toId nprob)
          where
            nprob = I.newProblem' prob (mint_ $ wgProof order)
            bound = upperbound (wgDimension p) (wgKind p) (kind_ $ wgProof order) (I.inter_ $ mint_ (wgProof order))
            cert  = (flip CD.updateTimeUBCert (`SR.add` bound) . CD.fromId)

        SMT.Error s -> throwError (userError s)
        _           -> incompatible
      where incompatible = CD.abortWith (PC.Applicable PC.Incompatible :: PC.ApplicationProof WeightGapProof)

wgEntscheide :: WeightGap -> Trs -> CD.TctM (SMT.Result WeightGapOrder)
wgEntscheide p prob = do
  res :: SMT.Result (I.Interpretation F (SomeLInter Int))
    <- SMT.smtSolveSt (SMT.smtSolveTctM prob) $ do

    SMT.setLogic SMT.QF_NIA

    amint <- DT.mapM toSMTLinearInterpretation absi
    strictVarEncoder <- Map.fromList `fmap` DT.mapM (\r -> SMT.bvarM' >>= \v -> return (r,v)) rules

    let
      strict = (strictVarEncoder Map.!)
      (.>=.) = gte

      slamint = foldr k amint (UPEnc.usablePositions usablePositions)
        where k (f,is) am = I.Interpretation $ Map.adjust (\a -> setStronglyLinear dim a is) f (I.interpretations am)
      interpret = interpretf (wgDimension p) slamint

      monotoneConstraints =
        SMT.bigAnd [ setMonotone (I.interpretations slamint `find` f) is | (f,is)  <- UPEnc.usablePositions usablePositions ]
          where find m f = error ("Interpretation.monotonConstraints: not found:" ++ show f) `DM.fromMaybe` Map.lookup f m

      wOrderConstraints = SMT.bigAnd [ interpret (RR.lhs r) .>=. interpret (RR.rhs r) | r <- wrules ]

      wgOrderConstraints = SMT.bigAnd [ ruleConstraint r | r <- rules ]
        where
          ruleConstraint r = wgConstraint .&& (strict r .=> orientConstraint)
            where
              li = interpret (RR.lhs r)
              ri = interpret (RR.rhs r)
              geqVec v1 v2 = SMT.bigAnd $ zipWith (.>=) (DF.toList v1) (DF.toList v2)
              gtVec v1 v2  = geqVec v1 v2 .&& EncM.vEntry 1 v1 .> EncM.vEntry 1 v2

              wgConstraint = SMT.bigAnd $ Map.intersectionWith k (MI.coefficients li) (MI.coefficients ri)
                where k lm rm = geqVec (EncM.mRow 1 lm) (EncM.mRow 1 rm)
              orientConstraint = SMT.bigAnd (Map.intersectionWith k (MI.coefficients li) (MI.coefficients ri)) .&& gtVec (MI.constant li) (MI.constant ri)
                where k lm rm = SMT.bigAnd [ geqVec (EncM.mRow j lm) (EncM.mRow j rm) | j <- [2..dim]]


      wgOnConstraints = case wgOn p of
        WgOnTrs -> SMT.bigAnd [ strict r  | r <- strs ]
        WgOnAny -> SMT.bigOr  [ strict r  | r <- srules ]

    SMT.assert $ (SMT.top :: SMT.Formula Int)
    SMT.assert monotoneConstraints
    SMT.assert wOrderConstraints
    SMT.assert wgOrderConstraints
    SMT.assert wgOnConstraints
    SMT.assertM (kindConstraints kind slamint)

    return $ SMT.decode slamint
  return $ wgproof `fmap` res
  where

    usablePositions = UPEnc.usableArgsWhereApplicable prob False (wgUArgs p == Arg.UArgs)

    trs    = Prob.allComponents prob
    rules  = RS.toList trs
    strs   = RS.toList (Prob.strictTrs prob)
    srules = RS.toList (Prob.strictComponents prob)
    wrules = RS.toList (Prob.weakComponents prob)


    absi =  I.Interpretation $ Map.mapWithKey (curry $ MI.abstractInterpretation kind (wgDimension p)) (Sig.toMap sig)
    dim = wgDimension p

    isConstantGrowth = null strs || wgOn p == WgOnTrs

    sig   = Prob.signature prob
    kind = mxKind miKnd dim deg (Prob.startTerms prob)
      where
        miKnd
          | isConstantGrowth         = wgKind p
          | wgKind p == Unrestricted = Algebraic
          | otherwise                = wgKind p

        deg
          | isConstantGrowth = wgDegree p
          | otherwise        = 1

    wgproof mint = WeightGapOrder
      { wgProof       = mproof mint
      , wgConstGrowth = isConstantGrowth }

    mproof mint = MatrixOrder
     { kind_ = kind
     , dim_ = dim
     , mint_ = I.InterpretationProof
        { I.sig_       = sig
        , I.inter_     = mint
        , I.uargs_     = usablePositions
        , I.ufuns_     = Nothing
        , I.useURules_ = False
        , I.shift_     = I.Shift $ case wgOn p of
            WgOnAny -> RS.selAnyOf RS.selStricts
            WgOnTrs -> RS.selAllOf $ RS.selStricts `RS.selInter` RS.selRules
        , I.strictDPs_ = sDPs
        , I.strictTrs_ = sTrs
        , I.weakDPs_   = wDPs
        , I.weakTrs_   = wTrs }
      }
      where
      (sDPs,wDPs) = List.partition (\(r,i) -> r `RS.member` Prob.strictComponents prob && uncurry isStrict i) (rs $ Prob.dpComponents prob)
      (sTrs,wTrs) = List.partition (\(r,i) -> r `RS.member` Prob.strictComponents prob && uncurry isStrict i) (rs $ Prob.trsComponents prob)
      rs x = [ (r, (interpretf dim mint  lhs, interpretf dim mint rhs)) | r@(RR.Rule lhs rhs) <- RS.toList x ]


----------------------------------------------------------------------
-- ##WGS weightgap strategy declaration
----------------------------------------------------------------------

weightGapStrategy :: Int -> Int -> NaturalMIKind -> UsableArgs -> WgOn -> TrsStrategy
weightGapStrategy dim deg nmiKind ua on = CD.Apply WeightGap
  { wgDimension = dim
  , wgDegree    = deg
  , wgKind      = nmiKind
  , wgUArgs     = ua
  , wgOn        = on }

weightGapDeclaration :: CD.Declaration (
  '[ CD.Argument 'CD.Optional Int
   , CD.Argument 'CD.Optional Int
   , CD.Argument 'CD.Optional NaturalMIKind
   , CD.Argument 'CD.Optional Arg.UsableArgs
   , CD.Argument 'CD.Optional WgOn
  ] CD.:-> CD.Strategy Prob.Trs Prob.Trs)
weightGapDeclaration = CD.declare  "weightgap" wgDescription (argDim,argDeg, argNMIKind, argUA, argWgOn) weightGapStrategy
  where
   wgDescription = [ "Uses the weight gap principle to shift some strict rules to the weak part of the problem"]
   argDim = dimArg `CD.optional` 1
   argDeg = degArg `CD.optional` 1
   argNMIKind = nmiKindArg `CD.optional` Algebraic
   argUA = Arg.usableArgs  `CD.optional` Arg.UArgs
   argWgOn = CD.flag "on"
      [ "This flag determines which rule have to be strictly oriented by the the matrix interpretation for the weight gap principle. "
      , "Here 'trs' refers to all strict non-dependency-pair rules of the considered problem, "
      , "while 'any' only demands any rule at all to be strictly oriented. "
      , "The default value is 'trs'."]
     `CD.optional` WgOnAny

weightgap :: TrsStrategy
weightgap = CD.deflFun weightGapDeclaration

weightgap' ::  Int -> Int -> NaturalMIKind -> UsableArgs  -> WgOn -> TrsStrategy
weightgap' = CD.declFun weightGapDeclaration

----------------------------------------------------------------------
-- ##WGX weightgap prettyprint and xml
----------------------------------------------------------------------

instance PP.Pretty WeightGapOrder where
  pretty p@WeightGapOrder{} = PP.vcat
      [ PP.text "The weightgap principle applies using the following " <> PP.text growth <> PP.colon
      , PP.indent 2 $ PP.pretty (wgProof p)
      , PP.text "Further, it can be verified that all rules not oriented are covered by the weightgap condition." ]
    where
      growth
        | wgConstGrowth p = "constant growth matrix-interpretation"
        | otherwise       = "nonconstant growth matrix-interpretation"

instance Xml.Xml WeightGapOrder where
  toXml p@WeightGapOrder{} = Xml.elt "weightgap" [Xml.toXml (wgProof p)]
  toCeTA _                 = Xml.unsupported
