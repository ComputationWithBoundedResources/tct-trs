module Tct.Trs.Poly.PolynomialInterpretation
  (
  Shape (..)
  , Kind (..)
  , SomeIndeterminate
  , SomePolynomial
  , VarPolynomial

  , CoefficientVar(..)
  , PolyInter (..)

  , mkInterpretation
  , interpret
  ) where

import qualified Data.Map               as M (Map, fromList, (!), elems)
import Data.Data (Typeable)

import qualified Data.Rewriting.Term    as R (Term)

import           Tct.Common.Ring

import           Tct.Common.Polynomial  (Monomial, Polynomial)
import qualified Tct.Common.Polynomial  as P
import qualified Tct.Common.Pretty  as PP
import           Tct.Trs.Interpretation (interpretTerm)
import           Tct.Trs            (Fun, Var)


-- | The shape of the polynomials.
data Shape
  = StronglyLinear
  | Linear
  | Quadratic
  | Mixed Int
  deriving (Eq, Show, Typeable)

-- | The kind of the interpretation.
data Kind
  = Unrestricted     { shape :: Shape }
  | ConstructorBased { shape :: Shape, constructors :: [Fun] }
  deriving Show

-- | Canonical variable type for abstract polynomials.
newtype SomeIndeterminate = SomeIndeterminate Int deriving (Eq, Ord, Enum)

indeterminates :: Int -> [SomeIndeterminate]
indeterminates n = take n [SomeIndeterminate 0 .. ]


type SomePolynomial c = P.Polynomial c SomeIndeterminate
type VarPolynomial c = P.Polynomial c Var

-- | Coefficients of the abstract polynomial.
data CoefficientVar = CoefficientVar
  { restrict :: Bool                        -- ^ Strictness Annotation.
  , varfun   :: Fun
  , argpos   :: Monomial SomeIndeterminate
  } deriving (Eq, Ord)

newtype PolyInter c = PolyInter 
  { interpretations :: M.Map Fun (SomePolynomial c) }
  deriving Show

interpret :: (SemiRing c, Eq c) => PolyInter c -> R.Term Var Fun -> Polynomial c Var
interpret ebsi = interpretTerm interpretFun interpretVar
  where
    interpretFun f = P.substituteVars interp . M.fromList . zip [SomeIndeterminate 0..]
      where interp = interpretations ebsi M.! f
    interpretVar      = P.variable

mkCoefficient :: Kind -> Fun -> P.Monomial SomeIndeterminate -> CoefficientVar
mkCoefficient (Unrestricted shp) f        = CoefficientVar (shp == StronglyLinear) f
mkCoefficient (ConstructorBased shp cs) f = CoefficientVar (shp == StronglyLinear || f `elem` cs) f

mkInterpretation :: Kind -> (Fun, Int) -> P.PolynomialView CoefficientVar SomeIndeterminate
mkInterpretation k (f,ar) = fromShape (shape k) (mkCoefficient k f) (indeterminates ar)
  where
    fromShape StronglyLinear = P.linear
    fromShape Linear         = P.linear
    fromShape Quadratic      = P.quadratic
    fromShape (Mixed i)      = P.mixed i


--- Proofdata --------------------------------------------------------------------------------------------------------

instance Show SomeIndeterminate where
  show (SomeIndeterminate i) = "x_" ++ show i

instance PP.Pretty SomeIndeterminate where
  pretty (SomeIndeterminate i) = PP.text "x_" PP.<> PP.int i

instance PP.Pretty Shape where
  pretty StronglyLinear = PP.text "stronglyLinear"
  pretty Linear         = PP.text "linear"
  pretty Quadratic      = PP.text "quadratic"
  pretty (Mixed i)      = PP.text "mixed" PP.<> PP.parens (PP.int i)

instance PP.Pretty Kind where
  pretty (Unrestricted shp)       = PP.text "unrestricted" PP.<> PP.parens (PP.pretty shp)
  pretty (ConstructorBased shp _) = PP.text "constructor-based" PP.<> PP.parens (PP.pretty shp)

instance PP.Pretty (PolyInter Int) where
  pretty pint = PP.vcat $ map PP.pretty (M.elems $ interpretations pint)


