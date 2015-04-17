{- |
Module      :  Tct.Trs.Method.Matrix.NaturalMI
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>,
               Georg Moser <georg.moser@uibk.ac.at>,
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :
Stability   :  unstable
Portability :  unportable

This module defines the processor for matrix.
-}

{-# LANGUAGE ScopedTypeVariables #-}

module Tct.Trs.Method.Matrix.NaturalMI
where

  -- general imports
import Control.Monad (when)
import Control.Monad.Error                           (throwError, MonadError)
import Control.Monad.Trans                           (liftIO, MonadIO)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List                        as List
import qualified Data.Foldable                    as DF
import qualified Data.Maybe                       as DM
import qualified Data.Typeable                    as DT


-- imports term-rewriting
import qualified Tct.Trs.Data                        as TD
import qualified Data.Rewriting.Rule                 as RR (Rule (..))
import qualified Data.Rewriting.Term                 as RT

-- imports tct-common
import qualified Tct.Common.SMT                   as SMT
import qualified Tct.Common.ProofCombinators         as PC


-- imports tct-core
import qualified Tct.Core.Data                       as CD
import           Tct.Core.Data.Declaration.Parse     ()
import qualified Tct.Core.Common.Parser              as P
import qualified Tct.Core.Common.Pretty              as PP
import qualified Tct.Core.Common.Xml                 as Xml
import qualified Tct.Core.Common.SemiRing            as SR


-- imports tct-trs
import qualified Tct.Trs.Data.Arguments           as Args

import qualified Tct.Trs.Data.Problem             as Prob
import qualified Tct.Trs.Data.ProblemKind             as ProbK
import qualified Tct.Trs.Data.Signature           as Sig
import qualified Tct.Trs.Data.RuleSelector           as RS
import qualified Tct.Trs.Data.Trs as Trs
import qualified Tct.Trs.Encoding.UsablePositions    as UPEnc
import qualified Tct.Trs.Encoding.UsableRules        as UREnc
import qualified Tct.Trs.Encoding.Interpretation  as I


-- should be  Encoding.Matrix
import qualified Tct.Trs.Method.Matrix.MatrixInterpretation     as MI
import qualified Tct.Trs.Method.Matrix.Matrix     as EncM
-- import qualified Tct.Trs.Encoding.UsablePositions as EncUP



data NaturalMIKind
  = Algebraic    -- ^ Count number of ones in diagonal to compute induced complexity function.
  | Automaton    -- ^ Use automaton techniques to compute induced complexity function.
  | Triangular   -- ^ Use triangular matrices only.
  | Unrestricted -- ^ Put no further restrictions on the interpretations.
  deriving (DT.Typeable, Bounded, Enum, Eq)

instance Show NaturalMIKind where
  show Algebraic    = "algebraic"
  show Triangular   = "triangular"
  show Automaton    = "automaton"
  show Unrestricted = "nothing"

data MatrixOrder a
  = MatrixOrder { kind_      :: MI.MatrixKind Prob.F
                , dim_       :: Int
                , mint_      :: I.InterpretationProof (MI.LinearInterpretation MI.SomeIndeterminate a) (MI.LinearInterpretation Prob.V a)
                } deriving (Show)

instance PP.Pretty (MatrixOrder Int) where
  pretty order = PP.vcat
    [ PP.text "We apply a matrix interpretation of kind " PP.<> PP.pretty (kind_ order) PP.<> PP.char ':'
    , if I.uargs_ mint /= UPEnc.fullWithSignature (I.sig_ mint)
      then PP.vcat
           [ PP.text "The following argument positions are considered usable:"
           , PP.indent 2 $ PP.pretty (I.uargs_ mint)
           , PP.empty]
      else PP.empty
    , PP.text "Following symbols are considered usable:"
    , PP.indent 2 $ PP.set (map PP.pretty . Set.toList $ I.ufuns_ mint)
    , PP.text "TcT has computed the following interpretation:"
    , PP.indent 2 (PP.pretty (mint_ order))
    , PP.empty
    , PP.text "Following rules are strictly oriented:"
    , ppOrder (PP.text " > ") (I.strictDPs_ mint ++ I.strictTrs_ mint)
    , PP.text ""
    , PP.text "Following rules are (at-least) weakly oriented:"
    , ppOrder (PP.text " >= ") (I.weakDPs_ mint ++ I.weakTrs_ mint)
    ]
    where
      mint = mint_ order
      ppOrder ppOrd rs = PP.table [(PP.AlignRight, as), (PP.AlignLeft, bs), (PP.AlignLeft, cs)]
        where
          (as,bs,cs) = unzip3 $ concatMap ppRule rs
          ppRule (RR.Rule l r,(lhs, rhs)) =
            [ (PP.pretty l, PP.text " = ", PP.pretty lhs)
            , (PP.empty   , ppOrd        , PP.pretty rhs)
            , (PP.empty   , PP.text " = ", PP.pretty r)
            , (PP.empty   , PP.empty     , PP.empty)
              ]

instance Xml.Xml (MatrixOrder Int) where
  toXml order = I.xmlProof (mint_ order) xtype where
    xtype = Xml.elt "type" [Xml.elt "matrixInterpretation" [xdom, xdim, xsdim]]
    xdom  = Xml.elt "domain" [Xml.elt "naturals" []]
    xdim  = Xml.elt "dimension" [ Xml.int (dim_ order)]
    xsdim = Xml.elt "strictDimension" [ Xml.int (1::Int) ]
  toCeTA order
    | True      = Xml.toXml order -- FIXME: MS: add sanity check; ceta supports definitely triangular; does it support algebraic ?
    | otherwise = Xml.unsupported


data NaturalMI = NaturalMI
                 { miDimension :: Int
                 , miDegree :: Int
                 , miKind :: NaturalMIKind
                 , uargs :: Bool
                 , urules :: Bool
                 , selector :: Maybe (TD.ExpressionSelector Prob.F Prob.V)
                 } deriving (Show)

type NaturalMIProof = PC.OrientationProof (MatrixOrder Int)



instance CD.Processor NaturalMI where
  type ProofObject NaturalMI = PC.ApplicationProof NaturalMIProof
  type Problem NaturalMI     = Prob.TrsProblem
  type Forking NaturalMI     = CD.Optional CD.Id

  solve p prob
    | Prob.isTrivial prob = return . CD.resultToTree p prob $ CD.Fail PC.Closed
    | otherwise           = do
        res <- entscheide p prob
        case res of
         SMT.Sat order
           | progressing nprob -> toProof $ CD.Success nprob (PC.Applicable $ PC.Order order)
                                  (certification order p)
           | otherwise -> throwError $ userError "natrualmi: sat but no progress :?"
           where nprob = newProblem prob order
         _ -> toProof $ CD.Fail (PC.Applicable PC.Incompatible)
        where
         toProof = return . CD.resultToTree p prob
         progressing CD.Null = True
         progressing (CD.Opt (CD.Id nprob)) = Prob.progressUsingSize prob nprob


newProblem :: Prob.TrsProblem -> MatrixOrder Int -> CD.Optional CD.Id Prob.TrsProblem
newProblem prob order = case I.shift_ (mint_ order) of
  I.All     -> CD.Null
  I.Shift _ -> CD.Opt . CD.Id $ prob
    { Prob.strictDPs = Prob.strictDPs prob `Trs.difference` sDPs
    , Prob.strictTrs = Prob.strictTrs prob `Trs.difference` sTrs
    , Prob.weakDPs   = Prob.weakDPs prob `Trs.union` sDPs
    , Prob.weakTrs   = Prob.weakTrs prob `Trs.union` sTrs }
  where
    rules = Trs.fromList . fst . unzip
    sDPs = rules (I.strictDPs_ $ mint_ order)
    sTrs = rules (I.strictTrs_ $ mint_ order)

certification :: MatrixOrder Int -> NaturalMI  -> CD.Optional CD.Id CD.Certificate -> CD.Certificate
certification order mi cert = case cert of
  CD.Null         -> CD.timeUBCert bound
  CD.Opt (CD.Id c) -> CD.updateTimeUBCert c (`SR.add` bound)
  where
    bound = ub order mi (I.inter_ $ mint_ order)

instance I.AbstractInterpretation NaturalMI where
  type (A NaturalMI) = MI.LinearInterpretation MI.SomeIndeterminate (MI.MatrixInterpretationEntry Prob.F)
  type (B NaturalMI) = MI.LinearInterpretation MI.SomeIndeterminate SMT.IExpr
  type (C NaturalMI) = MI.LinearInterpretation Prob.V SMT.IExpr

  encode _ = toSMTLinearInterpretation

  --setMonotone :: NaturalMI -> B NaturalMI -> [Int] -> SMT.Expr
  setMonotone _ (MI.LInter vmmap _) poss =
    SMT.bigAnd $ map setMonotonePos poss
    where
      toSI = MI.SomeIndeterminate
      setMonotonePos pos =
        case Map.lookup (toSI pos) vmmap of
        Just m -> EncM.mEntry 1 1 m SMT..> SMT.zero
        Nothing -> error "Tct.Trs.Method.Matrix.NatrualMI.setMonotone: Argument Position not found"

  --setInFilter :: NaturalMI -> B NaturalMI -> (Int -> SMT.Expr) -> SMT.Expr
  setInFilter _ (MI.LInter vmmap _) inFilter =
    SMT.bigAnd (Map.mapWithKey func vmmap)
    where
      func (MI.SomeIndeterminate i) m = SMT.bigOr (fmap ( SMT..> SMT.zero) m) SMT..==> inFilter i


  interpret = interpretf . miDimension

  --addConstant :: NaturalMI -> C NaturalMI -> SMT.IExpr -> C NaturalMI
  addConstant _ (MI.LInter coeffs vec) smtexpr =
    MI.LInter coeffs vec'
    where
      vec' = EncM.adjustVector (SMT.add smtexpr) 1 vec

  -- gte :: NaturalMI -> C NaturalMI -> C NaturalMI -> SMT.Expr
  gte _ (MI.LInter lcoeffs lconst) (MI.LInter rcoeffs rconst) =
    SMT.bigAnd zipmaps SMT..&& gteVec lconst rconst
    where
      zipmaps = Map.intersectionWith gteMatrix lcoeffs rcoeffs
      gteVec (EncM.Vector v1) (EncM.Vector v2) =
        SMT.bigAnd $ zipWith (SMT..>=) v1 v2

      gteMatrix (EncM.Matrix m1) (EncM.Matrix m2) =
        SMT.bigAnd (zipWith gteVec m1 m2)

toSMTLinearInterpretation :: MI.LinearInterpretation MI.SomeIndeterminate (MI.MatrixInterpretationEntry fun) -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) (MI.LinearInterpretation MI.SomeIndeterminate SMT.IExpr)
toSMTLinearInterpretation li = do
  constant <- toSMTVector $ MI.constant li
  coefficients <- mapM toSMTMatrix $ Map.assocs $ MI.coefficients li
  return $ MI.LInter (Map.fromList coefficients) constant
  where
    toSMTVector :: EncM.Vector (MI.MatrixInterpretationEntry fun) -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) (EncM.Vector SMT.IExpr)
    toSMTVector (EncM.Vector vec) =
      fmap EncM.Vector (mapM entryToSMT vec)
    toSMTMatrix  :: (MI.SomeIndeterminate, EncM.Matrix (MI.MatrixInterpretationEntry fun)) -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) (MI.SomeIndeterminate, EncM.Matrix SMT.IExpr)
    toSMTMatrix (i , EncM.Matrix vecs) = mapM toSMTVector vecs >>= (\m -> return (i, EncM.Matrix m))

entryToSMT :: MI.MatrixInterpretationEntry fun -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) SMT.IExpr
entryToSMT ent@(MI.MIVar{}) =
  if MI.restrict ent
  then SMT.snvarM'
  else SMT.nvarM'
entryToSMT MI.MIConstZero = return SMT.zero --SMT.numM 0
entryToSMT MI.MIConstOne = return SMT.one  -- SMT.numM 1



interpretf :: (SR.SemiRing a)
              => Int
              -> I.Interpretation Prob.F (MI.LinearInterpretation MI.SomeIndeterminate a)
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




monotoneConstraints :: SR.SemiRing a => (a -> SMT.Formula SMT.IFormula) -> MI.MatrixInterpretation Prob.F Prob.V a -> SMT.Formula SMT.IFormula
monotoneConstraints geqOne = SMT.bigAnd .
  Map.map (SMT.bigAnd .
           Map.map (geqOne . EncM.mEntry 1 1) .
           MI.coefficients) .
  MI.interpretations



countDiagonal :: NaturalMIKind -> Int -> (EncM.Matrix Int -> Int)
countDiagonal Triangular dim = const dim
countDiagonal _ _ = EncM.diagonalNonZeros

ub :: MatrixOrder Int -> NaturalMI -> I.Interpretation Prob.F (MI.LinearInterpretation MI.SomeIndeterminate Int) -> CD.Complexity
ub order mi inter =
  case kind_ order of
    MI.UnrestrictedMatrix{} -> CD.Exp (Just 1)
    MI.TriangularMatrix{} -> CD.Poly $ Just $ countDiagonal (miKind mi) (miDimension mi) $ maxNonIdMatrix (miDimension mi) inter
    MI.ConstructorBased cs _ -> CD.Poly $ Just $ countDiagonal (miKind mi) (miDimension mi) $ maxNonIdMatrix (miDimension mi) inter'
      where inter' = inter{I.interpretations = filterCs $ I.interpretations inter}
            filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
    MI.EdaMatrix Nothing -> CD.Poly $ Just (miDimension mi)
    MI.EdaMatrix (Just n) -> CD.Poly $ Just n
    MI.ConstructorEda _ Nothing -> CD.Poly $ Just (miDimension mi)
    MI.ConstructorEda _ (Just n) -> CD.Poly $ Just n

maxNonIdMatrix :: Int -> I.Interpretation fun (MI.LinearInterpretation var Int) -> EncM.Matrix Int
maxNonIdMatrix dim mi = 
  if any (elem (EncM.unit d) . Map.elems . MI.coefficients) (Map.elems $ I.interpretations mi) && maxi == EncM.zeroMatrix d d 
    then EncM.unit 1 
    else maxi
  where maxi = EncM.maximumMatrix max (d, d) $ Map.map (EncM.maximumMatrix max (d, d) . Map.filter (/= (EncM.unit d)) . MI.coefficients) $ I.interpretations mi
        d    = dim



isStrict :: MI.LinearInterpretation a Int -> MI.LinearInterpretation a Int -> Bool
isStrict (MI.LInter _ lconst) (MI.LInter _ rconst) = allGEQ && EncM.vEntry 1 lconst  > EncM.vEntry 1 rconst
  where allGEQ = and $ zipWith (>=) (DF.toList lconst) (DF.toList rconst)

diag :: Int -> MI.LinearInterpretation a SMT.IExpr ->  SMT.Expr
diag deg (MI.LInter coeffs _)  = SMT.bigAnd $ Map.map diagEQdeg coeffs
  where
    deg' = SMT.num deg
    listOf (EncM.Vector v) = v
    diagEQdeg m =  SMT.bigAdd (listOf $ EncM.diagonalEntries m) SMT..=< deg'

diagOnesConstraint deg mi = SMT.bigAddM (map k diags) `SMT.lteM` SMT.numM deg
  where 
    k ds = do
      v <- SMT.snvarM'
      SMT.assert $ (SMT.bigAdd ds SMT..> SMT.zero) SMT..<=> (v SMT..== SMT.one)
      return v
    diags = List.transpose $ map diag $ Map.elems (I.interpretations mi)
    diag  = concatMap (DF.toList . EncM.diagonalEntries) . Map.elems . MI.coefficients
  


--kindConstraints :: Eq l => MatrixKind -> MI.LinearInterpretation (DioPoly DioVar Int) -> DioFormula l DioVar Int
kindConstraints MI.UnrestrictedMatrix _ = return SMT.top
kindConstraints (MI.TriangularMatrix Nothing) _ = return SMT.top
kindConstraints (MI.TriangularMatrix (Just deg)) absmi = diagOnesConstraint deg absmi -- SMT.bigAnd $ Map.map (diag deg) (I.interpretations absmi)
kindConstraints (MI.ConstructorBased _  Nothing) _ = return SMT.top
kindConstraints (MI.ConstructorBased cs (Just deg)) absmi = diagOnesConstraint deg absmi' -- SMT.bigAnd $ Map.map (diag deg) (I.interpretations absmi')
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



entscheide :: NaturalMI -> Prob.TrsProblem -> CD.TctM (SMT.Result (MatrixOrder Int))
entscheide p prob = do
  mto <- (maybe [] (\i -> ["-T:"++show i]) . CD.remainingTime) `fmap` CD.askStatus prob
  -- mto <- (maybe [] (\i -> ["-t", show i]) . CD.remainingTime) `fmap` CD.askStatus prob
  -- let as = if miDimension p > 3 then ["-ib", "1", "-ob", "2", "-twostep"] else []
  res :: SMT.Result (I.Interpretation Prob.F (MI.LinearInterpretation MI.SomeIndeterminate Int), UPEnc.UsablePositions Prob.F, Maybe (UREnc.UsableSymbols Prob.F))
    <- liftIO $ SMT.solveStM (SMT.z3' $ mto ++ ["-smt2", "-in"]) $ do
    -- <- liftIO $ SMT.solveStM (SMT.minismt' $ ["-m", "-v2", "-neg"] ++ mto ++ as) $ do
    -- <- liftIO $ SMT.solveStM SMT.minismt $ do
    (a,b,c) <-  I.orient p prob absi shift (uargs p) (urules p)
    SMT.assert =<< kindConstraints kind a
    return $ SMT.decode (a,b,c)

  return $ mkOrder `fmap` res
  where

    shift = DM.maybe I.All I.Shift (selector p)
    sig = Prob.signature prob
    absi =  I.Interpretation $ Map.mapWithKey (curry $ MI.abstractInterpretation kind (miDimension p)) (Sig.toMap sig)
    kind = toKind (miKind p)
    -- matrix interpretation kind to matrix kind
    toKind Unrestricted = MI.UnrestrictedMatrix
    toKind Algebraic =
      if Prob.isRCProblem prob
      then MI.ConstructorBased (ProbK.constructors (Prob.startTerms prob) `Set.union` Sig.symbols (Sig.filter Prob.isCompoundf sig)) (Just $ miDegree p)
      else MI.TriangularMatrix (Just $ miDegree p)
    toKind Triangular =
      if Prob.isRCProblem prob
      then MI.ConstructorBased (ProbK.constructors (Prob.startTerms prob) `Set.union` Sig.symbols (Sig.filter Prob.isCompoundf sig)) Nothing 
      else MI.TriangularMatrix (Just $ miDegree p)
    toKind Automaton =
      if Prob.isRCProblem prob
      then MI.ConstructorEda (ProbK.constructors (Prob.startTerms prob) `Set.union` Sig.symbols (Sig.filter Prob.isCompoundf sig)) (Just $ max 1 (miDegree p))
      else MI.EdaMatrix (Just $ max 1 (miDegree p))

    mkOrder (inter, uposs, ufuns) = MatrixOrder
      { kind_ = kind
      , dim_  = miDimension p
      , mint_ = minter}
      where
        minter = I.InterpretationProof
          { I.sig_ = sig
          , I.inter_ = inter
          , I.uargs_ = uposs
          , I.ufuns_ = maybe Set.empty UREnc.runUsableSymbols ufuns
          , I.shift_ = shift
          , I.strictDPs_ = sDPs
          , I.strictTrs_ = sTrs
          , I.weakDPs_ = wDPs
          , I.weakTrs_ = wTrs
          }
        (sDPs,wDPs) = List.partition (\(r,i) -> r `Trs.member` Prob.strictComponents prob && uncurry isStrict i) (rs $ Prob.dpComponents prob)
        (sTrs,wTrs) = List.partition (\(r,i) -> r `Trs.member` Prob.strictComponents prob && uncurry isStrict i) (rs $ Prob.trsComponents prob)
        rs trs =
          [ (r, (interpretf (miDimension p) inter  lhs, interpretf (miDimension p) inter  rhs))
          | r@(RR.Rule lhs rhs) <- Trs.toList trs
          , isUsable ufuns r]

        isUsable Nothing _ = True
        isUsable (Just fs) (RR.Rule lhs _) = either (const False) (`Set.member` UREnc.runUsableSymbols fs) (RT.root lhs)


matrixStrategy :: Int -> Int -> NaturalMIKind -> Bool -> Bool
               -> Maybe (TD.ExpressionSelector Prob.F Prob.V)
               -> CD.Strategy Prob.TrsProblem
matrixStrategy dim deg nmiKind ua ur sl = CD.Proc $
  NaturalMI { miDimension = dim
            , miDegree = deg
            , miKind = nmiKind
            , uargs = ua
            , urules = ur
            , selector = sl
            }
ms a b c d e f = CD.Proc $ NaturalMI a b c d e f

instance CD.SParsable prob NaturalMIKind where
  parseS = P.enum


description :: [String]
description =  [ "desctiption of the matrix interpretation processor: TODO"
               ]

nmiKindArg :: CD.Argument 'CD.Optional NaturalMIKind
nmiKindArg = CD.arg { CD.argName = "miKind" , CD.argDomain = "<miKind>" }
             `CD.withHelp` (help:kinds)
             `CD.optional` Triangular
  where
    help = "Specifies the kind of the matrix interpretation. <shape> is one of:"
    kinds = map ('*':)  [ show Unrestricted, show Triangular, show Algebraic, show Automaton]


dimArg :: CD.Argument 'CD.Required Int
dimArg = CD.nat { CD.argName = "dimension" , CD.argDomain = "<nat>" }
         `CD.withHelp` ["Specifies the dimension of the matrices used in the interpretation."]

degArg :: CD.Argument 'CD.Required Int
degArg = CD.nat { CD.argName = "degree" , CD.argDomain = "<nat>" }
         `CD.withHelp` ["Specifies the maximal degree of the matrices used in the interpretation."]


slArg :: (Ord f, Ord v) => CD.Argument 'CD.Optional (Maybe (TD.ExpressionSelector f v))
slArg = CD.some $ RS.selectorArg
  `CD.withName` "shift"
  `CD.withHelp`
    [ "This argument specifies which rules to orient strictly and shift to the weak components." ]
  `CD.optional` RS.selAnyOf RS.selStricts


matrixDeclaration = CD.declare "matrix" description
                    ( dimArg, degArg, nmiKindArg, Args.uaArg `CD.optional` True,
                    Args.urArg `CD.optional` True, slArg)
                    matrixStrategy


-- dead code


-- data MatrixInterpretationProcessor
--   = PloyInterProc
--     { kind :: MI.MatrixKind Prob.F
--     , uargs :: Bool
--     , urules :: Bool
--     , selector :: Maybe (TD.ExpressionSelector Prob.F Prob.V)
--     } deriving Show

-- newtype MatrixInterpretationProof = MatrixInterProof (PC.OrientationProof MatrixOrder) deriving Show



-- instance PP.Pretty MatrixInterpretationProof where
--   pretty (MatrixInterProof order) = PP.pretty order


-- instance Xml.Xml MatrixInterpretationProof where
--   toXml (MatrixInterProof order) = Xml.toXml order


--monotoneconstraint :: SR.SemiRing a => Prob.F -> MI.SomeIndeterminate -> MI.MatrixInterpretation

-- -- filteringConstraints :: SR.SemiRing a
-- --      => (a -> SMT.Formula SMT.IFormula)
-- --      -> Bool
-- --      -> Prob.Problem Prob.F Prob.V
-- --      -> MI.MatrixInterpretation Prob.F Prob.V a
-- --      -> SMT.Formula SMT.IFormula
-- -- filteringConstraints gtZero allowAF prob absmi = undefined
-- --   where
-- --     isNotZeroMatrix f i mi = fml
-- --       where
-- --         mxM = Map.lookup f (MI.interpretations mi) >>= \l -> Map.lookup (MI.SomeIndeterminate i) (MI.coefficients l)
-- --         notZero mx es = SMT.bigOr $ map (\(k,l) -> gtZero (EncM.mEntry  k l mx) ) es

-- --         fml = case mxM of
-- --           Nothing -> error "Tct.Trs.Method.Matrix.NaturalMi: Undefined function index"
-- --           Just mx -> let entries = (\(m,n) -> [(k,l) | k <- [1..n], l <- [1..m]]) $ EncM.mDim mx
-- --                      in notZero mx entries
