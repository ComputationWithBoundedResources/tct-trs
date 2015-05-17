{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}

{-|
Module      : Tct.Trs.Method.Matrix.MatrixInterpretation
Description : Defines a general matrix interpretation of a function
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

module Tct.Trs.Method.Matrix.MatrixInterpretation (
  -- * data types
    LinearInterpretation(..)
  -- , MatrixInterpretation(..)
  , MatrixInterpretationEntry(..)
  , MatrixKind(..)
  , SomeIndeterminate(..)
  , SomeLinearInterpretation
  -- * functions
  , absStdMatrix
  , absTriMatrix
  , absEdaMatrix
  , abstractInterpretation
  , liProduct
  , liBigAdd
  -- , smtTriConstraints
  -- , maxNonIdMatrix
  -- , maxMatrix
  -- , toXml
  , pprintLInter
  )
where

-- general imports
import qualified Data.Map                         as Map
import qualified Data.Set                         as Set
--import qualified Data.List                        as List
import qualified Data.Foldable                    as DF
import qualified Data.Traversable                 as DT
import qualified Data.Maybe                       as DM

-- imports term-rewriting

-- imports tct-common
import qualified Tct.Common.SMT                   as SMT

-- imports tct-core
import qualified Tct.Core.Common.Pretty           as PP
import qualified Tct.Core.Common.Xml              as Xml
import qualified Tct.Core.Common.SemiRing         as SR


-- imports tct-trs
--import qualified Tct.Trs.Data.Problem             as Prob
--import qualified Tct.Trs.Data.Signature           as Sig


-- should be  Encoding.Matrix
import qualified Tct.Trs.Method.Matrix.Matrix     as EncM
--import qualified Tct.Trs.Encoding.UsablePositions as EncUP


----------------------------------------------------------------------
-- data types
----------------------------------------------------------------------



-- | linear interpretation of a function
data LinearInterpretation var a =
  LInter { coefficients :: Map.Map var (EncM.Matrix a)
         , constant     :: EncM.Vector a
         } deriving (Show, DT.Traversable, DF.Foldable)

-- | interpretation entry of a 'Matrix' / 'Vector' inside a 'LinearInterpretation'
data MatrixInterpretationEntry fun
  = MIVar { restrict :: Bool -- ^ is variable restricted to zero and one
          , varfun   :: fun  -- ^ function symbol
          , argpos   :: Int  -- ^ argument position
          , varrow   :: Int  -- ^ row
          , varcol   :: Int  -- ^ column
          }
  | MIConstZero -- ^ constant one. Introducing constants here circumvents the introduction of a RingConst class like in tct 2. Implicitly we have a Semiring for linear interpretations. So we need zero (and one).
  | MIConstOne  -- ^ constant zero
  deriving (Eq, Ord, Show)

-- type FunMatrixCreate fun a = fun -> Int -> Int -> EncM.Matrix a

-- | 'Matrix' restriction kinds
data MatrixKind fun
  = UnrestrictedMatrix -- ^ no restrictions on the matrix form
  | ConstructorBased (Set.Set fun) (Maybe Int) -- ^ TODO (set of constructor symbols)
  | TriangularMatrix (Maybe Int) -- ^ upper triangular form
  | ConstructorEda (Set.Set fun) (Maybe Int) -- ^ TODO
  | EdaMatrix (Maybe Int) -- ^ TODO
  deriving (Show)

-- | Canonical variable type for abstract linear matrix interpretations.
newtype SomeIndeterminate = SomeIndeterminate Int deriving (Eq, Ord, Enum)

type SomeLinearInterpretation f = LinearInterpretation SomeIndeterminate f

----------------------------------------------------------------------
-- functions
----------------------------------------------------------------------


-- | generate matrix with all abstract variable entries. All variables are not restricted.
absStdMatrix :: fun -> Int -> Int -> EncM.Matrix (MatrixInterpretationEntry fun)
absStdMatrix f dim k = EncM.Matrix $ map handlerow ds
  where
    handlerow i = EncM.Vector $ map (MIVar False f k i) ds
    ds = [1..dim]

-- | generate matrix with abstract variables in the upper triangular part zero constants at lower part.
--   Only variables entries in the main diagonal are restricted.
absTriMatrix :: fun -> Int -> Int -> EncM.Matrix (MatrixInterpretationEntry fun)
absTriMatrix f dim k =  EncM.Matrix $ map handlerow [1..dim]
  where
    handlerow i = EncM.Vector $ replicate (pred i) MIConstZero ++ midvar i : map (MIVar False f k i) [succ i..dim]
    midvar i = MIVar True f k i i

-- | generate matrix with abstract variables in the upper triangular part zero constants at lower part.
--   All variable intries are restricted.
absEdaMatrix :: fun -> Int -> Int -> EncM.Matrix (MatrixInterpretationEntry fun)
absEdaMatrix f dim k = EncM.Matrix $ map handlerow [1..dim]
  where
    handlerow i = EncM.Vector $ map (MIVar True f k i) [1..i] ++ map (MIVar True f k i) [succ i..dim]



-- | generate an abstract interpretation given a matrix kind restriction, a dimension, and a function symbol with arity.
abstractInterpretation ::  (Ord fun, Show fun) => MatrixKind fun -> Int -> (fun,Int) -> LinearInterpretation SomeIndeterminate (MatrixInterpretationEntry fun)
abstractInterpretation mkind dim (fun,arity) = interpretf fun
  where
    interpretf f = LInter (fcoeffs f) (fconst f)
    fcoeffs f = Map.fromList (map (\x -> (SomeIndeterminate x, (op f) f dim x)) [1..arity])
    fconst f = EncM.Vector $ map (\x -> MIVar False f 0 x 0) [1..dim]
    op f = case mkind of
      UnrestrictedMatrix    -> absStdMatrix
      TriangularMatrix _    -> absTriMatrix
      ConstructorBased cs _ -> if f `Set.member` cs
                              then absTriMatrix
                              else absStdMatrix
      EdaMatrix _           -> absEdaMatrix
      ConstructorEda cs _   -> if f `Set.member` cs
                              then absEdaMatrix
                              else absStdMatrix

-- | multiply a mtratix with the coeffitients and the constant of the linear interpretation.
liProduct :: SR.SemiRing a => EncM.Matrix a -> LinearInterpretation var a -> LinearInterpretation var a
liProduct m li = LInter (Map.map (EncM.mProduct m) (coefficients li)) (EncM.mvProduct m (constant li))


-- | add coefficients of same position, and add constant part of a list of linear interpretations
liBigAdd :: (SR.SemiRing a, Ord var) => EncM.Vector a -> [LinearInterpretation var a] -> LinearInterpretation var a
liBigAdd v lis =
  let
    coeffs = Map.unionsWith EncM.mAdd $ map coefficients lis
  in LInter coeffs (EncM.bigvAdd $ v : map constant lis)


-- | pretty print a linear interpretation
pprintLInter :: (Eq a, PP.Pretty a, SR.SemiRing a)
  => String -- ^ name of linear interpretation
  -> Int -- ^ indendtation
  -> (var -> PP.Doc) -- ^ pretty print function for variables
  -> LinearInterpretation var a -- ^ the linear interpretation
  -> PP.Doc
pprintLInter name indend ppVar (LInter ms vec) =
  PP.vcat [ PP.text (whenBaseLine i (alignRight indend name))
         PP.<> ppRow i | i <- [1..d] ]
  where
    d = EncM.vDim vec
    vs = [ (var, (show .  PP.pretty) `fmap` m) | (var, m) <- Map.toList ms, m /= zeroMatrix]

    alignRight pad str = replicate diff ' ' ++ str
      where diff = pad - length str
    whenBaseLine :: Int -> String -> String
    whenBaseLine i str
      | floor mid  == i = str
      | otherwise = [' ' | _ <- str]
      where mid = fromIntegral (d + 1) / (2 :: Rational)

    ppConstant i = PP.brackets $ PP.pretty (EncM.vEntry i vec)


    ppVariableCoefficient i m =
      PP.brackets (PP.fillSep [PP.text $ alignRight w cell | (cell, w) <- zip rs widths ])
      where
        rs = elts $ EncM.mRow i m
        widths = [collWidth j | j <- [1..d]]
        collWidth j = maximum $ 0 : [ length e | e <- elts $ EncM.mCol j m ]

    ppRow i = PP.hsep $
              PP.punctuate (PP.text $ whenBaseLine i " +") $
              [ ppVariableCoefficient i m
                PP.<+> PP.text (whenBaseLine i (show (ppVar var))) | (var,m) <- vs] ++ [ppConstant i]


    zeroMatrix = EncM.zeroMatrix d d
    elts (EncM.Vector es) = es



----------------------------------------------------------------------
-- instances
----------------------------------------------------------------------




instance Functor (LinearInterpretation var) where
  fmap f li = li { coefficients = Map.map (fmap f) (coefficients li)
                 , constant = fmap f (constant li)
                 }

instance (SMT.Decode m c a) => SMT.Decode m (LinearInterpretation var c) (LinearInterpretation var a) where
  decode = DT.traverse SMT.decode

instance (Eq a, PP.Pretty a, PP.Pretty var, SR.SemiRing a) => PP.Pretty (LinearInterpretation var a) where
  pretty = pprintLInter "" 0 PP.pretty

instance (Eq a, Ord var, PP.Pretty a, SR.SemiRing a) => PP.Pretty (LinearInterpretation var a, Map.Map var String) where
  pretty (li, vars) = pprintLInter "" 0 toString li
    where
      toString l = PP.text $ DM.fromJust (Map.lookup l vars)

instance PP.Pretty fun => PP.Pretty (MatrixInterpretationEntry fun) where
  pretty v@MIVar{} = res PP.<> usc PP.<> f PP.<> usc PP.<> row PP.<> usc PP.<> col PP.<> usc PP.<> ap
    where
      usc = PP.char '_'
      res = if restrict v then PP.char 'r' else PP.char 'a'
      ap = PP.int (argpos v)
      row = PP.int (varrow v)
      col = PP.int (varcol v)
      f = PP.pretty (varfun v)
  pretty MIConstZero = PP.text "zero"
  pretty MIConstOne = PP.text "one"



instance PP.Pretty (MatrixKind fun) where
  pretty UnrestrictedMatrix = PP.text "unrestricted matrix interpretation"
  pretty (TriangularMatrix Nothing) = PP.text "triangular matrix interpretation"
  pretty (TriangularMatrix (Just n)) = PP.text "triangular matrix interpretation (containing no more than "
                                       PP.<>  PP.int n
                                       PP.<> PP.text " non-zero interpretation-entries in the diagonal of the component-wise maxima)"
  pretty (ConstructorBased _ Nothing) = PP.text "constructor based matrix interpretation"
  pretty (ConstructorBased _ (Just n)) = PP.text "constructor based matrix interpretation (containing no more than "
                                         PP.<>  PP.int n
                                         PP.<> PP.text " non-zero interpretation-entries in the diagonal of the component-wise maxima)"
  pretty (EdaMatrix Nothing) = PP.text "matrix interpretation satisfying not(EDA)"
  pretty (EdaMatrix (Just n)) = PP.text "matrix interpretation satisfying not(EDA) and not(IDA("
                                PP.<> PP.int n
                                PP.<> PP.text "))"
  pretty (ConstructorEda _ Nothing) = PP.text "constructor-based matrix interpretation satisfying not(EDA)"
  pretty (ConstructorEda _ (Just n)) = PP.text "constructor-based matrix interpretation satisfying not(EDA) and not(IDA("
                                       PP.<> PP.int n
                                       PP.<> PP.text "))."


instance Show SomeIndeterminate where
  show (SomeIndeterminate i) = 'x' : show i

instance PP.Pretty SomeIndeterminate where
  pretty (SomeIndeterminate i) = PP.char 'x' PP.<> PP.int i

instance Xml.Xml (LinearInterpretation SomeIndeterminate Int) where
  toXml lint = xsum (xcons (constant lint) :map xcoeff (Map.toList $ coefficients lint) )
    where
      xpol p = Xml.elt "polynomial" [p]
      xsum   = xpol . Xml.elt "sum"
      xmul   = xpol . Xml.elt "product"
      xelm   = xpol . Xml.elt "coefficient"

      xcons c = xelm [ Xml.toXml c ]
      xcoeff (v,m) = xmul [ xelm [Xml.toXml m], xvar v]
      xvar (SomeIndeterminate i) = xpol $ Xml.elt "variable" [Xml.int i]








-- TODO: implement when other things are understood
-- toXml :: (Show fun, Ord fun, Xml.Xml fun) => MatrixInterpretation fun SomeIndeterminate Int -> MatrixKind fun -> EncUP.UsablePositions fun -> [Xml.XmlContent]
-- toXml mi knd uargs = tpe : [inter f li | (f,li) <- Map.toList $ interpretations mi]
--   where
--     dim = dimension mi
--     sig = signature mi
--     tpe = Xml.elt "type"
--           [ Xml.elt "matrixInterpretation"
--             [ Xml.elt "domain" [Xml.elt "naturals" []]
--             , Xml.elt "dimension" [Xml.int dim]
--             , Xml.elt "strictDimension" [Xml.int (1::Int)]
--             , Xml.elt "kind"
--               [ case knd of
--                  UnrestrictedMatrix -> Xml.elt "unrestricted" []
--                  ConstructorBased _ mn -> Xml.elt "constructorBased" [Xml.int $ DM.fromMaybe dim mn]
--                  TriangularMatrix mn -> Xml.elt "triangular" [Xml.int $ DM.fromMaybe dim mn]
--                  ConstructorEda _ mn -> Xml.elt "constructorEda" [Xml.int $ DM.fromMaybe dim mn]
--                  EdaMatrix mn -> Xml.elt "constructorEda" [Xml.int $ DM.fromMaybe dim mn]
--               ]
--             -- TODO add usable args xml here
--             ]
--           ]
--     inter f li =
--       Xml.elt "interpret"
--       [ Xml.elt "symbol" [Xml.toXml f]
--       , Xml.elt "arity" [Xml.int $ sig `Sig.arity` f]
--       , xsum $
--         (xpoly $ xcoeff $ xvec $ constant li) :
--         [xprod [xpoly $ xcoeff $ xmat m, xvar v] | (v,m) <- Map.toList $ coefficients li]
--       ]
--     xpoly p = Xml.elt "polynomial" [p]
--     xsum = xpoly . Xml.elt "sum"
--     xprod = xpoly . Xml.elt "product"
--     xvar (SomeIndeterminate i) = xpoly $ Xml.elt "variable" [Xml.int i]
--     xcoeff c = Xml.elt "coefficient" [c]
--     xelt e = xcoeff (Xml.elt "integer" [Xml.int e])
--     xvec (EncM.Vector vs) = Xml.elt "vector" [xelt e | e <- vs]
--     xmat mx = let
--       EncM.Matrix vvs = EncM.transpose mx
--       in Xml.elt "matrix" [xvec vs | vs <- vvs]

-- is there something equivalent to this instance?
-- instance PropAtom MIVar


-- instance Semiring a => Interpretation (MatrixInterpretation

-- smtTriConstraints :: MatrixInterpretation fun var SMT.IExpr -> SMT.Formula SMT.IFormula
-- smtTriConstraints = SMT.bigAnd . Map.map (SMT.bigAnd . Map.map triConstraint . coefficients) . interpretations
--                  where triConstraint m = SMT.bigAnd $ map (\i -> EncM.mEntry i i m SMT..=< SMT.one) [1..(dim m)]
--                        dim             = uncurry min . EncM.mDim

-- maxNonIdMatrix
--   :: (SR.SemiRing a)
--     => (a -> a -> a)
--     -> (EncM.Matrix a -> EncM.Matrix a -> Bool)
--     -> (EncM.Matrix a -> EncM.Matrix a -> Bool)
--     -> MatrixInterpretation fun var a -> EncM.Matrix a
-- maxNonIdMatrix amaxFun mxEqFun  mxNeqFun mi =
--   let
--     dim = dimension mi
--     --maxi :: EncM.Matrix a
--     maxi = EncM.maximumMatrix amaxFun (dim, dim)
--            $ Map.map (EncM.maximumMatrix amaxFun (dim, dim) . Map.filter (mxNeqFun (EncM.identityMatrix dim)) . coefficients)
--            $ interpretations mi

--   in if DF.any (DF.any (mxEqFun (EncM.identityMatrix dim)) . coefficients) (interpretations mi) &&
--         mxEqFun maxi (EncM.zeroMatrix dim dim)
--      then EncM.identityMatrix 1
--      else maxi


-- maxMatrix
--   :: SR.SemiRing a
--     => (a -> a -> a)
--     -> MatrixInterpretation fun var a
--     -> EncM.Matrix a
-- maxMatrix amaxFun mi = let
--   dim = dimension mi
--   in EncM.maximumMatrix amaxFun (dim, dim)
--      $ Map.map (EncM.maximumMatrix amaxFun (dim, dim) . coefficients)
--      $ interpretations mi

-- instance Functor (MatrixInterpretation fun var) where
--   fmap f mi = mi { interpretations = Map.map (fmap f) (interpretations mi) }

-- instance (Eq a, PP.Pretty a, PP.Pretty var, PP.Pretty fun, SR.SemiRing a) => PP.Pretty (MatrixInterpretation fun var a) where
--   pretty (MInter _ sig ints) = PP.table [ (PP.AlignLeft, List.intersperse nl [ p indend | (_, p) <- ps ]) ]
--     where
--       ps = [ printInter f li | (f,li) <- Map.assocs ints ]
--       printInter f li = (length name, \ ind -> pprintLInter name ind PP.pretty li)
--         where name = show $ PP.brackets (PP.pretty (f,sig)) PP.<> ppArgs PP.<+> PP.text "= "
--               ppArgs | null vs = PP.empty
--                      | otherwise = PP.parens $ PP.hsep $ PP.punctuate PP.comma [PP.pretty var | var <- vs]
--               vs = Map.keys $ coefficients li
--       nl = PP.text " "
--       indend = maximum (0: [len | (len, _) <- ps])
