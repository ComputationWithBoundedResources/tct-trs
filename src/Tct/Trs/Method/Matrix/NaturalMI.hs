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

module Tct.Trs.Method.Matrix.NaturalMI
where

  -- general imports
import qualified Data.Map as Map
import qualified Data.Set as Set
-- import qualified Data.List                        as List
import qualified Data.Foldable                    as DF
import qualified Data.Maybe                       as DM

-- imports term-rewriting
import qualified Tct.Trs.Data                        as TD
import qualified Data.Rewriting.Rule                 as RR (Rule (..))
import qualified Data.Rewriting.Term                 as RT

-- imports tct-common
import qualified Tct.Common.SMT                   as SMT
import qualified Tct.Common.ProofCombinators         as PC


-- imports tct-core
import qualified Tct.Core.Data                       as CD
import qualified Tct.Core.Common.Pretty              as PP
import qualified Tct.Core.Common.Xml                 as Xml
import qualified Tct.Core.Common.SemiRing            as SR


-- imports tct-trs
import qualified Tct.Trs.Data.Problem             as Prob
import qualified Tct.Trs.Data.Signature           as Sig
import qualified Tct.Trs.Encoding.UsablePositions    as UPEnc
import qualified Tct.Trs.Encoding.UsableRules        as UREnc
import qualified Tct.Trs.Encoding.Interpretation  as I


-- should be  Encoding.Matrix
import qualified Tct.Trs.Method.Matrix.MatrixInterpretation     as MI
import qualified Tct.Trs.Method.Matrix.Matrix     as EncM
-- import qualified Tct.Trs.Encoding.UsablePositions as EncUP


-- data MatrixInterpretationProcessor
--   = PloyInterProc
--     { kind :: MI.MatrixKind Prob.F
--     , uargs :: Bool
--     , urules :: Bool
--     , selector :: Maybe (TD.ExpressionSelector Prob.F Prob.V)
--     } deriving Show

-- newtype MatrixInterpretationProof = MatrixInterProof (PC.OrientationProof MatrixOrder) deriving Show

-- data NaturalMIKind
--   = Algebraic    -- ^ Count number of ones in diagonal to compute induced complexity function.
--   | Automaton    -- ^ Use automaton techniques to compute induced complexity function.
--   | Triangular   -- ^ Use triangular matrices only.
--   | Unrestricted -- ^ Put no further restrictions on the interpretations.
--   deriving ({-Typeable,-} Bounded, Enum, Eq)

-- instance Show NaturalMIKind where
--   show Algebraic    = "algebraic"
--   show Triangular   = "triangular"
--   show Automaton    = "automaton"
--   show Unrestricted = "nothing"

-- instance CD.Processor MatrixInterpretationProcessor where
--   type ProofObject MatrixInterpretationProcessor = PC.ApplicationProof MatrixInterpretationProof
--   type Problem MatrixInterpretationProcessor = Prob.TrsProblem
--   solve p prob = undefined

data NaturalMI = NaturalMI
                 { dimension :: Int }

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


  interpret (NaturalMI dim) = interpretf dim

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
    toSMTVector (EncM.Vector vec) = mapM entryToSMT vec >>= return . EncM.Vector
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

-- data MatrixOrder
--   = MatrixOrder { kind_      :: MI.MatrixKind Prob.F
--                 , mint_      :: MI.MatrixInterpretation Prob.F Prob.V Int
--                 , sig_       :: Sig.Signature Prob.F
--                 , uargs_     :: UPEnc.UsablePositions Prob.F
--                 , ufuns_     :: Sig.Symbols Prob.F
--                 , strictDPs_ :: [(RR.Rule Prob.F Prob.V,
--                                   (MI.LinearInterpretation Prob.V Int,
--                                    MI.LinearInterpretation Prob.V Int))]
--                 , strictTrs_ :: [(RR.Rule Prob.F Prob.V,
--                                   (MI.LinearInterpretation Prob.V Int,
--                                    MI.LinearInterpretation Prob.V Int))]
--                 , weakDPs_   :: [(RR.Rule Prob.F Prob.V,
--                                   (MI.LinearInterpretation Prob.V Int,
--                                    MI.LinearInterpretation Prob.V Int))]
--                 , weakTrs_   :: [(RR.Rule Prob.F Prob.V,
--                                   (MI.LinearInterpretation Prob.V Int,
--                                    MI.LinearInterpretation Prob.V Int))]
--                 } deriving (Show)

-- instance PP.Pretty MatrixOrder where
--   pretty order = PP.vcat
--     [ PP.text "We apply a matrix interpretation of kind " PP.<> PP.pretty (kind_ order) PP.<> PP.char ':'
--     , if uargs_ order /= UPEnc.fullWithSignature (sig_ order)
--       then PP.vcat
--            [ PP.text "The following argument positions are considered usable:"
--            , PP.indent 2 $ PP.pretty (uargs_ order)
--            , PP.empty]
--       else PP.empty
--     , PP.text "Following symbols are considered usable:"
--     , PP.indent 2 $ PP.set (map PP.pretty . Set.toList $ ufuns_ order)
--     , PP.text "TcT has computed the following interpretation:"
--     , PP.indent 2 (PP.pretty (mint_ order))
--     , PP.empty
--     , PP.text "Following rules are strictly oriented:"
--     , ppOrder (PP.text " > ") (strictDPs_ order ++ strictTrs_ order)
--     , PP.text ""
--     , PP.text "Following rules are (at-least) weakly oriented:"
--     , ppOrder (PP.text " >= ") (weakDPs_ order ++ weakTrs_ order)
--     ]
--     where
--       ppOrder ppOrd rs = PP.table [(PP.AlignRight, as), (PP.AlignLeft, bs), (PP.AlignLeft, cs)]
--         where
--           (as,bs,cs) = unzip3 $ concatMap ppRule rs
--           ppRule (RR.Rule l r,(lhs, rhs)) =
--             [ (PP.pretty l, PP.text " = ", PP.pretty lhs)
--             , (PP.empty   , ppOrd        , PP.pretty rhs)
--             , (PP.empty   , PP.text " = ", PP.pretty r)
--             , (PP.empty   , PP.empty     , PP.empty)
--               ]

-- instance PP.Pretty MatrixInterpretationProof where
--   pretty (MatrixInterProof order) = PP.pretty order

-- instance Xml.Xml MatrixOrder where
--   toXml order = Xml.elt "instance Xml.Xml MatrixOrder not yet implemented" []

-- instance Xml.Xml MatrixInterpretationProof where
--   toXml (MatrixInterProof order) = Xml.toXml order

monotoneConstraints :: SR.SemiRing a => (a -> SMT.Formula SMT.IFormula) -> MI.MatrixInterpretation Prob.F Prob.V a -> SMT.Formula SMT.IFormula
monotoneConstraints geqOne = SMT.bigAnd .
  Map.map (SMT.bigAnd .
           Map.map (geqOne . EncM.mEntry 1 1) .
           MI.coefficients) .
  MI.interpretations

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
