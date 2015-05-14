{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Tct.Trs.Method.Matrix.MatrixInterpretation
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

TODO: describe matrix interpretations
-}

module Tct.Trs.Method.Matrix.NaturalMI
  ( matrixDeclaration
  , matrix
  , matrix'
  , matrixCPDeclaration
  , matrixCP
  , matrixCP'

  , NaturalMIKind (..)
  , UsableArgs (..)
  , UsableRules (..)
  , Greedy (..)

  -- * Weight gap

  ) where

-- general imports
import Data.Monoid ((<>))
import           Control.Monad.Trans                        (liftIO)
import qualified Data.Foldable                              as DF
import qualified Data.List                                  as List
import qualified Data.Map                                   as Map
import qualified Data.Maybe                                 as DM
import qualified Data.Set                                   as Set

import qualified Data.Traversable                           as DT
import qualified Data.Typeable                              as DT


-- imports term-rewriting
import qualified Data.Rewriting.Rule                        as RR (Rule (..))
import qualified Data.Rewriting.Term                        as RT
import qualified Tct.Trs.Data                               as TD

-- imports tct-common
import qualified Tct.Common.ProofCombinators                as PC
import           Tct.Common.SMT                             (one, zero, (.<=>), (.==), (.==>), (.>))
import qualified Tct.Common.SMT                             as SMT


-- imports tct-core
import qualified Tct.Core.Common.Parser                     as P
import qualified Tct.Core.Common.Pretty                     as PP
import qualified Tct.Core.Common.SemiRing                   as SR
import qualified Tct.Core.Common.Xml                        as Xml
import qualified Tct.Core.Data                              as CD
import           Tct.Core.Parse            ()


-- imports tct-trs
import Tct.Trs.Data
import qualified Tct.Trs.Data.Arguments                     as Arg
import           Tct.Trs.Data.Arguments                     (UsableArgs (..), UsableRules (..), Greedy (..))

import qualified Tct.Trs.Data.ComplexityPair as CP
import qualified Tct.Trs.Data.Problem                       as Prob
import qualified Tct.Trs.Data.ProblemKind                   as ProbK
import qualified Tct.Trs.Data.RuleSelector                  as RS
import qualified Tct.Trs.Data.Signature                     as Sig
import qualified Tct.Trs.Data.Trs                           as Trs
import qualified Tct.Trs.Encoding.Interpretation            as I
import qualified Tct.Trs.Encoding.UsableRules               as UREnc
import qualified Tct.Trs.Encoding.UsablePositions           as UPEnc
import qualified Tct.Trs.Method.Matrix.MatrixInterpretation as MI
-- should be  Encoding.Matrix
import qualified Tct.Trs.Method.Matrix.Matrix               as EncM


----------------------------------------------------------------------
-- data types
----------------------------------------------------------------------

-- | Kind of the Matrix Interpretation
data NaturalMIKind
  = Algebraic    -- ^ Count number of ones in diagonal to compute induced complexity function.
  | Automaton    -- ^ Use automaton techniques to compute induced complexity function.
  | Triangular   -- ^ Use triangular matrices only.
  | Unrestricted -- ^ Put no further restrictions on the interpretations.
  deriving (DT.Typeable, Bounded, Enum, Eq, Show)


-- | Proof information for matrix Interpretations.
data MatrixOrder a
  = MatrixOrder { kind_ :: MI.MatrixKind Prob.F -- ^ restictions of the matrices used in the proof
                , dim_  :: Int -- ^ dimensions of the matrices used in the proof
                , mint_ :: I.InterpretationProof (MI.LinearInterpretation MI.SomeIndeterminate a) (MI.LinearInterpretation Prob.V a) -- ^ a proof which interprets canonical variables to user variables
                } deriving (Show)


-- | Type of the NatualMI processor. Stores information required to run the matrix interpretation processor
data NaturalMI = NaturalMI
                 { miDimension :: Int -- ^ dimension of matrices generated for the interpretation
                 , miDegree    :: Int -- ^ maximal allowed degree of the interpretation matrices
                 , miKind      :: NaturalMIKind -- ^ kind of interpretation
                 , uargs       :: Arg.UsableArgs -- ^ usable arguments
                 , urules      :: Arg.UsableRules -- ^ usable rules
                 , selector    :: Maybe (TD.ExpressionSelector Prob.F Prob.V)
                 , greedy      :: Arg.Greedy
                 } deriving (Show)

-- | Proof type of matrix interpretations
type NaturalMIProof = PC.OrientationProof (MatrixOrder Int)

-- | Type abbreviation
type SomeLInter a = MI.LinearInterpretation MI.SomeIndeterminate a

----------------------------------------------------------------------
-- functions
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
    bound = upperbound mi order (I.inter_ $ mint_ order)

{- | convert an abstract linear interpretation into an SMT interpretation -}
toSMTLinearInterpretation :: SomeLInter (MI.MatrixInterpretationEntry fun)
                          -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) (SomeLInter SMT.IExpr)
toSMTLinearInterpretation li = do
  constant <- toSMTVector $ MI.constant li
  coefficients <- mapM toSMTMatrix $ Map.assocs $ MI.coefficients li
  return $ MI.LInter (Map.fromList coefficients) constant
  where
    toSMTVector :: EncM.Vector (MI.MatrixInterpretationEntry fun)
                -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) (EncM.Vector SMT.IExpr)
    toSMTVector (EncM.Vector vec) =
      fmap EncM.Vector (mapM entryToSMT vec)
    toSMTMatrix :: (MI.SomeIndeterminate, EncM.Matrix (MI.MatrixInterpretationEntry fun))
                -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) (MI.SomeIndeterminate, EncM.Matrix SMT.IExpr)
    toSMTMatrix (i , EncM.Matrix vecs) = mapM toSMTVector vecs >>= (\m -> return (i, EncM.Matrix m))

{- | converts an abstract interpretation variable into a SMT variable -}
entryToSMT :: MI.MatrixInterpretationEntry fun
           -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) SMT.IExpr
entryToSMT ent@(MI.MIVar{}) =
  if MI.restrict ent
  then SMT.snvarM'
  else SMT.nvarM'
entryToSMT MI.MIConstZero = return zero --SMT.numM 0
entryToSMT MI.MIConstOne = return one  -- SMT.numM 1


{- | Takes the SMT interpretations of functions to build an interpretation of a term -}
interpretf :: (SR.SemiRing a)
           => Int
           -> I.Interpretation Prob.F (SomeLInter a)
           -> RT.Term Prob.F Prob.V
           -> MI.LinearInterpretation Prob.V a
interpretf dim ebsi = I.interpretTerm interpretFun interpretVar
  where
    interpretFun f ts = addAll $ zipWith handleArg [1..] ts
      where
        find e a m =
          DM.fromMaybe
            (error $ "Tct.Trs.Method.Matrix.NatrualMI.interpretf: Matrix " ++ e ++ " not found")
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
  NaturalMI
  -> MatrixOrder Int
  -> I.Interpretation Prob.F (SomeLInter Int)
  -> CD.Complexity
upperbound mi order inter =
  case kind_ order of
    MI.UnrestrictedMatrix{}                    -> CD.Exp (Just 1)
    MI.TriangularMatrix{}                      -> CD.Poly $ Just $ countDiagonal (miKind mi) (miDimension mi) $ maxNonIdMatrix (miDimension mi) inter
    MI.ConstructorBased cs _                   -> CD.Poly $ Just $ countDiagonal (miKind mi) (miDimension mi) $ maxNonIdMatrix (miDimension mi) inter'
      where inter' = inter{I.interpretations = filterCs $ I.interpretations inter}
            filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
    MI.EdaMatrix Nothing                       -> CD.Poly $ Just (miDimension mi)
    MI.EdaMatrix (Just n)                      -> CD.Poly $ Just n
    MI.ConstructorEda _ Nothing                -> CD.Poly $ Just (miDimension mi)
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
isStrict :: MI.LinearInterpretation a Int
         -> MI.LinearInterpretation a Int -> Bool
isStrict (MI.LInter _ lconst) (MI.LInter _ rconst) = allGEQ && EncM.vEntry 1 lconst  > EncM.vEntry 1 rconst
  where allGEQ = and $ zipWith (>=) (DF.toList lconst) (DF.toList rconst)


{- | assert the matrix diagonal to be greather one iff a variable is one -}
diagOnesConstraint :: Int
                   -> I.Interpretation fun (MI.LinearInterpretation a SMT.IExpr)
                   -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) (SMT.Formula SMT.IFormula)
diagOnesConstraint deg mi = SMT.bigAddM (map k diags) `SMT.lteM` SMT.numM deg
  where
    k ds = do
      v <- SMT.snvarM'
      SMT.assert $ (SMT.bigAdd ds .> SMT.zero) .<=> (v .== SMT.one)
      return v
    diags = List.transpose $ map diag' $ Map.elems (I.interpretations mi)
    diag'  = concatMap (DF.toList . EncM.diagonalEntries) . Map.elems . MI.coefficients


    -- kind = toKind (miKind p)
    -- -- matrix interpretation kind to matrix kind
    -- toKind Unrestricted = MI.UnrestrictedMatrix
    -- toKind Algebraic =
    --   if Prob.isRCProblem prob
    --   then MI.ConstructorBased cs md2
    --   else MI.TriangularMatrix md2
    -- toKind Triangular = 
    --   if Prob.isRCProblem prob
    --   then MI.ConstructorBased cs Nothing
    --   else MI.TriangularMatrix Nothing
    -- toKind Automaton =
    --   if Prob.isRCProblem prob
    --   then MI.ConstructorEda cs (Just md1)
    --   else MI.EdaMatrix (Just md1)

    -- cs = Sig.constructors sig
    -- md1 = max 0 (miDegree p)
    -- md2 = if md1 < (miDimension p) then Just md1 else Nothing




mxKind :: NaturalMIKind -> Int -> Int -> StartTerms fun -> MI.MatrixKind fun
mxKind kind dim deg  st = case (kind, st) of
  (Unrestricted, ProbK.BasicTerms{}) -> MI.UnrestrictedMatrix
  (Triangular,   ProbK.BasicTerms{}) -> MI.ConstructorBased cs Nothing
  (Triangular,   ProbK.AllTerms{})   -> MI.TriangularMatrix Nothing
  (Algebraic,    ProbK.BasicTerms{}) -> MI.ConstructorBased cs md
  (Algebraic,    ProbK.AllTerms{})   -> MI.TriangularMatrix md
  (Automaton,    ProbK.BasicTerms{}) -> MI.ConstructorEda cs (min 1 `fmap` md)
  (Automaton,    ProbK.AllTerms{})   -> MI.TriangularMatrix (min 1 `fmap` md)
  where
    cs = ProbK.constructors st
    md = let d = max 0 deg in if d < dim then Just d else Nothing

  



{- | build constraints for an interpretation depending on the matrix kind -}
kindConstraints :: Ord fun
                => MI.MatrixKind fun
                -> I.Interpretation fun (MI.LinearInterpretation a SMT.IExpr)
                -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) (SMT.Formula SMT.IFormula)
kindConstraints MI.UnrestrictedMatrix _                   = return SMT.top
kindConstraints (MI.TriangularMatrix Nothing) _           = return SMT.top
kindConstraints (MI.TriangularMatrix (Just deg)) absmi    = diagOnesConstraint deg absmi
kindConstraints (MI.ConstructorBased _  Nothing) _        = return SMT.top
kindConstraints (MI.ConstructorBased cs (Just deg)) absmi = diagOnesConstraint deg absmi'
  where absmi' = absmi{I.interpretations = filterCs $ I.interpretations absmi}
        filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
kindConstraints _ _ = return SMT.bot
-- kindConstraints (EdaMatrix Nothing) absmi = edaConstraints absmi
-- kindConstraints (EdaMatrix (Just deg)) absmi = idaConstraints deg absmi
-- kindConstraints (ConstructorEda cs mdeg) absmi =
--   rcConstraints (absmi' ds)
--   && maybe (edaConstraints (absmi' cs)) (\ deg -> idaConstraints deg (absmi' cs)) mdeg
--   where ds = F.symbols (signature absmi) Set.\\ cs
--         absmi' fs = absmi{interpretations = filterFs fs $ interpretations absmi}
--         filterFs fs = Map.filterWithKey (\f _ -> f `Set.member` fs)


entscheide :: NaturalMI -> Prob.TrsProblem -> CD.TctM (CD.Return (CD.ProofTree Prob.TrsProblem))
entscheide p prob = do
  let
    orientM = do
      res@(_, (pint,_), _) <- I.orient p prob absi shift (uargs p == Arg.UArgs) (urules p == Arg.URules)
      SMT.assertM $ (kindConstraints kind pint)
      return $ res
    (ret, encoding)           = SMT.runSolverM orientM SMT.initialState
    (apint,decoding,forceAny) = ret
    aorder = MatrixOrder
      { kind_ = kind
      , dim_  = miDimension p
      , mint_ = apint }

  toResult `fmap` entscheide1 p aorder encoding decoding forceAny prob
  where
    toResult pt = if CD.progress pt then CD.Continue pt else CD.Abort pt

    absi =  I.Interpretation $ Map.mapWithKey (curry $ MI.abstractInterpretation kind (miDimension p)) (Sig.toMap sig)

    sig   = Prob.signature prob
    kind = mxKind (miKind p) (miDimension p) (miDegree p) (Prob.startTerms prob)

    shift = maybe I.All I.Shift (selector p)



entscheide1 ::
  NaturalMI
  -> MatrixOrder c
  -> SMT.SolverState SMT.Expr
  -> (I.Interpretation Prob.F (SomeLInter SMT.IExpr), Maybe (UREnc.UsableEncoder Prob.F))
  -> I.ForceAny
  -> Prob.TrsProblem
  -> CD.TctM (CD.ProofTree (Prob.TrsProblem))
entscheide1 p aorder encoding decoding forceAny prob
  | Prob.isTrivial prob = return . I.toTree p prob $ CD.Fail (PC.Applicable PC.Incompatible)
  | otherwise           = do
    mto <- CD.remainingTime `fmap` CD.askStatus prob
    res :: SMT.Result (I.Interpretation Prob.F (SomeLInter Int), Maybe (UREnc.UsableSymbols Prob.F))
      <- liftIO $ SMT.solve (SMT.minismt mto) (encoding `assertx` forceAny srules) (SMT.decode decoding)
    case res of
      SMT.Sat a
        | Arg.useGreedy (greedy p) -> fmap CD.flatten $ again `DT.mapM` pt
        | otherwise                -> return pt

        where
          pt    = I.toTree p prob $ CD.Success (I.newProblem prob (mint_ order)) (PC.Applicable $ PC.Order order) (certification p order)
          order = mkOrder a

      _ -> return $ I.toTree p prob $ CD.Fail (PC.Applicable PC.Incompatible)
      where
        again = entscheide1 p aorder encoding decoding forceAny

        assertx st e = st {SMT.asserts = e: SMT.asserts st}
        srules = Trs.toList $ Prob.strictComponents prob

        mkOrder (inter, ufuns) = aorder { mint_ = mkInter (mint_ aorder) inter ufuns }
        mkInter aproof inter ufuns = aproof
          { I.inter_     = inter
          , I.ufuns_     = maybe Set.empty UREnc.runUsableSymbols ufuns
          , I.strictDPs_ = sDPs
          , I.strictTrs_ = sTrs
          , I.weakDPs_   = wDPs
          , I.weakTrs_   = wTrs }
          where


          (sDPs,wDPs) = List.partition (\(r,i) -> r `Trs.member` Prob.strictComponents prob && uncurry isStrict i) (rs $ Prob.dpComponents prob)
          (sTrs,wTrs) = List.partition (\(r,i) -> r `Trs.member` Prob.strictComponents prob && uncurry isStrict i) (rs $ Prob.trsComponents prob)
          rs trs =
            [ (r, (interpretf (miDimension p) inter  lhs, interpretf (miDimension p) inter  rhs))
            | r@(RR.Rule lhs rhs) <- Trs.toList trs
            , isUsable ufuns r]

          isUsable Nothing _ = True
          isUsable (Just fs) (RR.Rule lhs _) = either (const False) (`Set.member` UREnc.runUsableSymbols fs) (RT.root lhs)


----------------------------------------------------------------------
-- matrix strategy declaration
----------------------------------------------------------------------


{- | create options/ configuration  for the NaturalMI strategy -}
matrixStrategy :: Int -> Int -> NaturalMIKind -> Arg.UsableArgs -> Arg.UsableRules
               -> Maybe (TD.ExpressionSelector Prob.F Prob.V)
               -> Arg.Greedy
               -> CD.Strategy Prob.TrsProblem Prob.TrsProblem
matrixStrategy dim deg nmiKind ua ur sl gr = CD.Proc $
  NaturalMI { miDimension = dim
            , miDegree = deg
            , miKind = nmiKind
            , uargs = ua
            , urules = ur
            , selector = sl
            , greedy = gr
            }


{- | describes the strategy -}
description :: [String]
description =  [ "description of the matrix interpretation processor: TODO"               ]

{- | argument for the NaturalMIKind -}
nmiKindArg :: CD.Argument 'CD.Required NaturalMIKind
nmiKindArg = CD.arg
  `CD.withName` "miKind"
  `CD.withDomain` fmap show [(minBound :: NaturalMIKind)..]
  `CD.withHelp`  ["Specifies the kind of the matrix interpretation."]

{- | dimension argument -}
dimArg :: CD.Argument 'CD.Required Int
dimArg = CD.nat { CD.argName = "dimension" , CD.argDomain = "<nat>" }
         `CD.withHelp` ["Specifies the dimension of the matrices used in the interpretation."]

{- | degree argument -}
degArg :: CD.Argument 'CD.Required Int
degArg = CD.nat { CD.argName = "degree" , CD.argDomain = "<nat>" }
         `CD.withHelp` ["Specifies the maximal degree of the matrices used in the interpretation."]

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
  , CD.Argument 'CD.Optional (Maybe (RS.ExpressionSelector Prob.F Prob.V))
  , CD.Argument 'CD.Optional Arg.Greedy )
args =
  ( dimArg          `CD.optional` 1
  , degArg          `CD.optional` 1
  , nmiKindArg      `CD.optional` Algebraic
  , Arg.usableArgs  `CD.optional` Arg.UArgs
  , Arg.usableRules `CD.optional` Arg.URules
  , slArg           `CD.optional` Just (RS.selAnyOf RS.selStricts)
  , Arg.greedy      `CD.optional` Arg.Greedy )

{- | declare the matrix strategy -}
matrixDeclaration :: CD.Declaration (
  '[ CD.Argument 'CD.Optional Int
   , CD.Argument 'CD.Optional Int
   , CD.Argument 'CD.Optional NaturalMIKind
   , CD.Argument 'CD.Optional Arg.UsableArgs
   , CD.Argument 'CD.Optional Arg.UsableRules
   , CD.Argument 'CD.Optional (Maybe (RS.ExpressionSelector Prob.F Prob.V))
   , CD.Argument 'CD.Optional Arg.Greedy
  ] CD.:-> CD.Strategy Prob.TrsProblem Prob.TrsProblem)
matrixDeclaration = CD.declare "matrix" description args matrixStrategy

matrix :: CD.Strategy Prob.TrsProblem Prob.TrsProblem
matrix = CD.deflFun matrixDeclaration

matrix' :: Int -> Int -> NaturalMIKind -> Arg.UsableArgs -> Arg.UsableRules
               -> Maybe (TD.ExpressionSelector Prob.F Prob.V)
               -> Arg.Greedy
               -> CD.Strategy Prob.TrsProblem Prob.TrsProblem
matrix' = CD.declFun matrixDeclaration


----------------------------------------------------------------------
-- important instances
----------------------------------------------------------------------

instance I.AbstractInterpretation NaturalMI where
  -- | Type of abstract matrix interpretations.
  type (A NaturalMI) = SomeLInter (MI.MatrixInterpretationEntry Prob.F)
  -- | Type of SMT interpretations. Abstract Varaibles replaced by SMT variables.
  type (B NaturalMI) = SomeLInter SMT.IExpr
  -- | Type of concrete interpretations. SMT variables replaced by integers.
  type (C NaturalMI) = MI.LinearInterpretation Prob.V SMT.IExpr

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
      func (MI.SomeIndeterminate i) m = SMT.bigOr (fmap ( .> SMT.zero) m) .==> inFilter i

  {- | Given an abstract interpretation get a concrete interpretation  for a Trs-Term. -}
  -- interpret   :: NaturalMI -> I.Interpretation Prob.F (B NaturalMI) -> RT.Term Prob.F Prob.V -> C NaturalMI
  interpret = interpretf . miDimension

  {- | Add a SMT value (smtexpr) to the constant part of an interpretation.
       This way we can get a strict or weak decrease requirement.
    -}
  -- addConstant :: NaturalMI -> C NaturalMI -> SMT.IExpr -> C NaturalMI
  addConstant _ (MI.LInter coeffs vec) smtexpr =
    MI.LInter coeffs vec'
    where
      vec' = EncM.adjustVector (SMT.add smtexpr) 1 vec

  {- | compares two concrete linear interpretations with the 'greater or equal' relation -}
  -- gte :: NaturalMI -> C NaturalMI -> C NaturalMI -> SMT.Expr
  gte _ lint1 lint2 = gte lint1 lint2

gte (MI.LInter lcoeffs lconst) (MI.LInter rcoeffs rconst) =
  SMT.bigAnd zipmaps SMT..&& gteVec lconst rconst
  where
    zipmaps = Map.intersectionWith gteMatrix lcoeffs rcoeffs
    gteVec (EncM.Vector v1) (EncM.Vector v2) =
      SMT.bigAnd $ zipWith (SMT..>=) v1 v2

    gteMatrix (EncM.Matrix m1) (EncM.Matrix m2) =
      SMT.bigAnd (zipWith gteVec m1 m2)

setMonotone (MI.LInter vmmap _) poss =
  SMT.bigAnd $ map setMonotonePos poss
  where
    toSI = MI.SomeIndeterminate
    setMonotonePos pos =
      case Map.lookup (toSI pos) vmmap of
      Just m -> EncM.mEntry 1 1 m SMT..> SMT.zero
      Nothing -> error "Tct.Trs.Method.Matrix.NatrualMI.setMonotone: Argument Position not found"

setStronglyLinear dim (MI.LInter vmmap cs) poss = MI.LInter (foldr k vmmap poss) cs
  where k pos = Map.adjust (const $ EncM.identityMatrix dim) (toEnum pos)



instance CD.Processor NaturalMI where
  type ProofObject NaturalMI = PC.ApplicationProof NaturalMIProof
  type I NaturalMI           = Prob.TrsProblem
  type O NaturalMI           = Prob.TrsProblem
  type Forking NaturalMI     = CD.Optional CD.Id

  {- | Decides whether applying the NaturalMI processor makes progress or not -}
  solve p prob
    | Prob.isTrivial prob = return . CD.resultToTree p prob $ CD.Fail PC.Closed
    | otherwise           = entscheide p prob



--- ** complexity pair -----------------------------------------------------------------------------------------------


instance CP.IsComplexityPair NaturalMI where
  solveComplexityPair p sel prob = fmap toResult `fmap` CD.evaluate (CD.Proc p{selector=Just sel, greedy=Greedy}) prob
    where
      toResult pt = case CD.open pt of
        [nprob] -> CP.ComplexityPairProof
          { CP.result = pt
          , CP.removableDPs = Prob.strictDPs prob `Trs.difference` Prob.strictDPs nprob
          , CP.removableTrs = Prob.strictTrs prob `Trs.difference` Prob.strictTrs nprob }
        _ -> error "Tct.Trs.Method.Poly.NaturalPI.solveComplexityPair: the impossible happened"

matrixComplexityPair :: Int -> Int -> NaturalMIKind -> Arg.UsableArgs -> Arg.UsableRules -> CP.ComplexityPair
matrixComplexityPair dim deg nmiKind ua ur = CP.toComplexityPair $
  NaturalMI { miDimension = dim
            , miDegree = deg
            , miKind = nmiKind
            , uargs = ua
            , urules = ur
            , selector = Nothing
            , greedy = NoGreedy
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
-- other instances
----------------------------------------------------------------------


instance PP.Pretty (MatrixOrder Int) where
  pretty order = PP.vcat
    [ PP.text "We apply a matrix interpretation of kind " PP.<> PP.pretty (kind_ order) PP.<> PP.char ':'
    , PP.pretty $ I.prettyProof (mint_ order) ]

instance Xml.Xml (MatrixOrder Int) where
  toXml order = I.xmlProof (mint_ order) xtype where
    xtype = Xml.elt "type" [Xml.elt "matrixInterpretation" [xdom, xdim, xsdim]]
    xdom  = Xml.elt "domain" [Xml.elt "naturals" []]
    xdim  = Xml.elt "dimension" [ Xml.int (dim_ order)]
    xsdim = Xml.elt "strictDimension" [ Xml.int (1::Int) ]
  toCeTA order
    | True      = Xml.toXml order -- FIXME: MS: add sanity check; ceta supports definitely triangular; does it support algebraic ?
    | otherwise = Xml.unsupported

instance CD.SParsable i i NaturalMIKind where
  parseS = P.enum



--- * weightgap ------------------------------------------------------------------------------------------------------

data WgOn 
  = WgOnTrs -- ^ Orient at least all non-DP rules.
  | WgOnAny -- ^ Orient some rule.
  deriving (Eq, Show, DT.Typeable, Bounded, Enum)


data WeightGap = WeightGap 
  { wgDimension :: Int
  , wgDegree    :: Int
  , wgKind      :: NaturalMIKind
  , wgUArgs     :: UsableArgs
  , wgOn        :: WgOn
  , wgSel       :: Maybe (ExpressionSelector F V)
  } deriving (Show)

data WeightGapOrder =  WeightGapOrder 
  { wgProof       :: MatrixOrder Int
  , wgConstGrowth :: Bool }
  deriving (Show)

type WeightGapProof = PC.OrientationProof WeightGapOrder


instance CD.Processor WeightGap where
  type ProofObject WeightGap = PC.ApplicationProof WeightGapProof
  type I WeightGap           = Prob.TrsProblem
  type O WeightGap           = Prob.TrsProblem

  solve p prob
    | Prob.isTrivial prob = return . CD.resultToTree p prob $ CD.Fail PC.Closed
    | otherwise           = do
      res <- wgEntscheide p prob
      case res of
        SMT.Sat order -> undefined
        _             -> undefined

wgEntscheide :: WeightGap -> TrsProblem -> CD.TctM (SMT.Result WeightGapOrder)
wgEntscheide p prob = do
  mto <- CD.remainingTime `fmap` CD.askStatus prob
  res :: SMT.Result (I.Interpretation Prob.F (SomeLInter Int))
    <- liftIO $ SMT.solveStM (SMT.minismt mto) $ do

    SMT.setFormat "QF_NIA"

    amint <- DT.mapM toSMTLinearInterpretation absi
    strictVarEncoder <- Map.fromList `fmap` DT.mapM (\r -> SMT.bvarM' >>= \v -> return (r,v)) rules

      
    let
      strict = (strictVarEncoder Map.!)
      orientSelected (Trs.SelectDP r)  = strict r
      orientSelected (Trs.SelectTrs r) = strict r
      orientSelected (Trs.BigAnd es)   = SMT.bigAnd (orientSelected `fmap` es)
      orientSelected (Trs.BigOr es)    = SMT.bigOr (orientSelected `fmap` es)

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
          ruleConstraint r = wgConstraint SMT..&& (strict r SMT..==> orientConstraint) 
            where 
              li = interpret (RR.lhs r)
              ri = interpret (RR.rhs r)
              geqVec (EncM.Vector v1) (EncM.Vector v2) = SMT.bigAnd $ zipWith (SMT..>=) v1 v2
              gtVec (EncM.Vector (v1:vs1)) (EncM.Vector (v2:vs2)) = (v1 SMT..> v2) `SMT.band` geqVec (EncM.Vector vs1) (EncM.Vector vs2)
              wgConstraint = SMT.bigAnd 
                [ maybe SMT.bot (\lm -> geqVec (EncM.mRow 1 lm) (EncM.mRow 1 rm)) (Map.lookup v $ MI.coefficients li)
                | (v,rm) <- Map.toList $ MI.coefficients ri]
              orientConstraint = SMT.bigAnd 
                [ maybe SMT.bot  (\lm -> SMT.bigAnd [ geqVec (EncM.mRow j lm) (EncM.mRow j rm) | j <- [2..dim]])
                                              (Map.lookup v $ MI.coefficients li)
                                            | (v,rm) <- Map.toList $ MI.coefficients ri]
                                `SMT.band` gtVec (MI.constant li) (MI.constant ri)


      wgOnConstraints = case wgOn p of
        WgOnTrs -> SMT.bigAnd [ strict r  | r <- strs ]
        WgOnAny -> SMT.bigOr  [ strict r  | r <- srules ]

      wgSelConstraints = case wgSel p of
        Just sel -> orientSelected (RS.rsSelect sel prob)
        Nothing  -> SMT.top
     
    SMT.assert monotoneConstraints
    SMT.assert wOrderConstraints
    SMT.assert wgOrderConstraints
    SMT.assert wgOnConstraints
    SMT.assert wgSelConstraints
    SMT.assertM (kindConstraints kind slamint)
    

    return $ SMT.decode slamint
  return $ wgproof `fmap` res
  where

    usablePositions = UPEnc.usableArgsWhereApplicable prob False (wgUArgs p == Arg.UArgs)

    trs    = Prob.allComponents prob
    rules  = Trs.toList trs
    strs = Trs.toList (Prob.strictTrs prob)
    srules = Trs.toList (Prob.strictComponents prob)
    wrules = Trs.toList (Prob.weakComponents prob)


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
        , I.ufuns_     = Set.empty
        , I.shift_     = I.Shift $ RS.selAnyOf RS.selStricts `DM.fromMaybe` (wgSel p)
        , I.strictDPs_ = sDPs
        , I.strictTrs_ = sTrs
        , I.weakDPs_   = wDPs
        , I.weakTrs_   = wTrs }
      }
      where
      (sDPs,wDPs) = List.partition (\(r,i) -> r `Trs.member` Prob.strictComponents prob && uncurry isStrict i) (rs $ Prob.dpComponents prob)
      (sTrs,wTrs) = List.partition (\(r,i) -> r `Trs.member` Prob.strictComponents prob && uncurry isStrict i) (rs $ Prob.trsComponents prob)
      rs x = [ (r, (interpretf dim mint  lhs, interpretf dim mint rhs)) | r@(RR.Rule lhs rhs) <- Trs.toList x ]


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

