{- | This module provides a tree-based implementation for multivariate polynomials.

All operations on 'Monomial' fulfill following invariants:

    * each variable (indeterminate) occurs at most once
    * exponents are >= 1

All operations on 'Polynomial' fulfill following invariants:

    * monomials are valid
    * monomials are unique
    * coefficients are non-zero wrt. 'zero'

Basic operations are defined via 'SemiRing' ('Ring') class.

For constructing polynomials a view 'PolynomialView' is provided.
A view is not as restrictive but does not support any arithmetical operations.
Use 'fromView' or 'fromViewWith' to construct a 'Polynomial'.

-}
module Tct.Common.Polynomial
  (
  -- * Polynomial
  Monomial
  , Polynomial
  , degree
  , isStronglyLinear
  , coefficients
  , constantValue
  , substituteVars
  -- * View
  , MonomialView (..)
  , PolynomialView (..)
  , mfromView
  , pfromView
  , pfromViewWith
  , pfromViewWithM
  , (^^^), monov, polyv
  , constant
  , variable
  , linear
  , quadratic
  , mixed
  -- * Pretty Printing
  , ppMonomial
  , ppPolynomial
  )
  where


import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Control.Monad
import qualified Data.Map.Strict   as M

import qualified Tct.Common.Pretty as PP
import           Tct.Common.Ring


-- | The abstract monomial type.
newtype Monomial v = Mono (M.Map v Int)
  deriving (Eq, Ord, Show)

mmult :: Ord v => Monomial v -> Monomial v -> Monomial v
mmult (Mono ps1) (Mono ps2) = Mono $ M.unionWith (+) ps1 ps2

mone :: Monomial v
mone = Mono M.empty

mdegree :: Monomial v -> Int
mdegree (Mono ps)
  | M.null ps = -1
  | otherwise = maximum $ M.elems ps

instance Ord v => Multiplicative (Monomial v) where
  one  = mone
  mult = mmult


-- | The abstract polynom type.
newtype Polynomial c v = Poly (M.Map (Monomial v) c) deriving Show

pnormalise :: (Additive c, Eq c) => Polynomial c v -> Polynomial c v
pnormalise (Poly ts) = Poly $ M.filter (/= zero) ts

asConstant :: (SemiRing c, Eq v) => Polynomial c v -> Maybe c
asConstant (Poly ts) = case M.toList ts of
  []                  -> Just zero
  [(m,c)] | m == mone -> Just c
  _                   -> Nothing

pzero :: Polynomial c v
pzero = Poly M.empty

padd :: (Additive c, Eq c, Ord v) => Polynomial c v -> Polynomial c v -> Polynomial c v
padd (Poly ts1) (Poly ts2) = pnormalise . Poly $ M.unionWith add ts1 ts2

instance (Additive c, Eq c, Ord v) => Additive (Polynomial c v) where
  zero = pzero
  add  = padd

pone :: Multiplicative c => Polynomial c v
pone = Poly $ M.singleton mone one

pscale :: SemiRing c => c -> Polynomial c v -> Polynomial c v
pscale c (Poly ts) = Poly $ M.map (`mult` c) ts

pmult :: (SemiRing c, Eq c, Ord v) => Polynomial c v -> Polynomial c v -> Polynomial c v
pmult p1@(Poly ts1) p2@(Poly ts2) = pnormalise $ case (asConstant p1, asConstant p2) of
  (Just c, _) -> pscale c p2
  (_, Just c) -> pscale c p1
  _           ->
    Poly $ M.fromListWith add
      [ (m1 `mmult` m2, c1 `mult` c2) | (m1,c1) <- M.toList ts1, (m2,c2) <- M.toList ts2 ]

instance (SemiRing c, Eq c, Ord v) => Multiplicative (Polynomial c v) where
  one  = pone
  mult = pmult

pnegate :: AdditiveGroup c => Polynomial c v -> Polynomial c v
pnegate (Poly ms) = Poly $ M.map neg ms

instance (AdditiveGroup c, Eq c, Ord v) => AdditiveGroup (Polynomial c v) where
  neg = pnegate


pbigMult :: (SemiRing c, Eq c, Ord v) => [Polynomial c v] -> Polynomial c v
pbigMult = foldl' pmult pone

pbigAdd :: (SemiRing c, Eq c, Ord v) => [Polynomial c v] -> Polynomial c v
pbigAdd = foldl' padd pzero

-- | @'substituteVars' p subs@ substitutes the variables in p according to @subs@.
-- Variables occuring not in @subs@ are mapped to the unit ('one') polynomial.
substituteVars :: (SemiRing c, Eq c, Ord v, Ord v') => Polynomial c v -> M.Map v (Polynomial c v') -> Polynomial c v'
substituteVars (Poly ts) subs = pbigAdd $ foldl' handleTerms [] (M.toList ts)
  where 
    handleTerms polys (m,c) = (c `pscale` handleMono m) : polys
    subs' = M.toList subs
    handleMono (Mono ps) = pbigMult $ foldl' k [] subs'
      where
        k polys (v,p) = case M.lookup v ps of
          Just i  -> polys ++ replicate i p
          Nothing -> polys

-- | Returns the degree of the polynomial.
--
-- prop> degree zero = -1
degree :: Ord v => Polynomial c v -> Int
degree (Poly ms) = maximum (map mdegree $ M.keys ms)

-- prop> all (==one) . coefficients.
isStronglyLinear :: (SemiRing c, Eq c, Ord v) =>  Polynomial c v -> Bool
isStronglyLinear = all (==one) . coefficients

-- | Returns the coefficients of the polynomial.
coefficients :: Ord v => Polynomial c v -> [c]
coefficients (Poly ts) = M.elems $ M.delete mone ts

-- | Returns the constant value of the polynomial.
constantValue :: (Ord v, SemiRing c) => Polynomial c v -> c
constantValue (Poly ts) = fromMaybe zero (M.lookup mone ts)


--- * View -----------------------------------------------------------------------------------------------------------


-- | Power type with variable @v@.
data PowerView v         = PowV v Int deriving (Eq, Ord)
-- | Monomial type with coefficient @c@ and variable @v@.
data MonomialView v      = MonoV [PowerView v]
-- | Polynomial type with coefficient @c@ and variable @v@.
newtype PolynomialView c v = PolyV [(c,Monomial v)]

-- | prop> v^^^1 = PowV v i
(^^^) :: v -> Int -> PowerView v
v^^^i = PowV v i

-- | prop> mono = MonoV
monov :: Ord v => [PowerView v] -> MonomialView v
monov = MonoV

-- | prop> poly = PolyV
polyv :: [(c,Monomial v)] -> PolynomialView c v
polyv = PolyV

mfromView :: Ord v => MonomialView v -> Monomial v
mfromView (MonoV ps) = Mono $ foldl' k M.empty ps
  where k m (PowV v i) = if i >0 then M.insertWith (+) v i m else m


-- | Like 'fromViewWith' with the identity function applied.
--
-- prop> fromView = fromViewWith id id
pfromView :: (Additive c, Eq c, Ord v) => PolynomialView c v -> Polynomial c v
pfromView = pfromViewWith id

pfromViewWith :: (Additive c', Eq c', Ord v) => (c -> c') -> PolynomialView c v -> Polynomial c' v
pfromViewWith f (PolyV ts) = Poly $ foldl' k M.empty ts where
  k p (c, m) = let c' = f c in
    if c' /= zero then M.insertWith add m c' p else p

pfromViewWithM :: (Monad m, Additive c', Eq c', Ord v) => (c -> m c') -> PolynomialView c v -> m (Polynomial c' v)
pfromViewWithM f (PolyV ts) = Poly `liftM` foldM k M.empty ts where
  k p (c,m) = do
    c' <- f c
    return $ if c' /= zero
      then M.insertWith add m c' p
      else p


-- | Lifts a constant to a polynom.
constantv :: c -> PolynomialView c v
constantv c = PolyV [(c,mone)]

-- | Lifts a variable to a polynom (with exponent 1).
variablev :: Multiplicative c => v -> PolynomialView c v
variablev v = PolyV [(one, Mono $ M.singleton v 1)]

constant :: (Additive c, Eq c, Ord v) => c -> Polynomial c v
constant = pfromView . constantv

variable :: (SemiRing c, Eq c, Ord v) => v -> Polynomial c v 
variable = pfromView . variablev


-- | @'linear' f [x,...,z] = cx*x + ... + cz*z + c@
-- constructs a linear polynomial; the coefficients are determinded by applying @f@ to each monomial.
linear :: Ord v => (Monomial v -> c) -> [v] -> PolynomialView c v
linear f = polyv . (mkTerm [] :) . map (\v -> mkTerm [v^^^1])
  where mkTerm ps = let m = mfromView (MonoV ps) in (f m,m)

-- | @'quadratic' f [x,...,z] = cx2*x^2 + cx*x + ... + cz2*z^2 + cz*z + c@
-- constructs a quadratic polynomial; the coefficients are determined by applying @f@ to each monomial.
quadratic :: Ord v => (Monomial v -> c) -> [v] -> PolynomialView c v
quadratic f = polyv . (mkTerm [] :) . map (\v -> mkTerm [v^^^2,v^^^1])
  where mkTerm ps = let m = mfromView (MonoV ps) in (f m, m)

-- | Creates a mixed polynom up to a specified degree; the coefficients are determined by applying @f@ to each monomial.
--
-- > mixed 2 (const 1) "xz" = x^2 + x*z + x + z^2 + z + 1
mixed :: Ord v => Int -> (Monomial v -> c) -> [v] -> PolynomialView c v
mixed d f vs =  polyv $ map mkTerm pows
  where
    mkTerm ps = let m = mfromView (MonoV ps) in (f m, m)
    pows =
      map (filter (\(PowV _ i) -> i>0) . zipWith PowV vs) -- [] isElem of pows
      . filter (\ps -> sum ps <= d)
      . sequence $ replicate (length vs) [0..d]


--- * Pretty ---------------------------------------------------------------------------------------------------------
instance PP.Pretty v => PP.Pretty (Monomial v) where
  pretty = ppMonomial PP.pretty

instance (PP.Pretty c, PP.Pretty v) => PP.Pretty (Polynomial c v) where
  pretty = ppPolynomial PP.pretty PP.pretty

-- | Pretty printing function for 'Monomial'.
-- Should be used for basic types that do not provide the 'Pretty' instance.
ppMonomial :: (v -> PP.Doc) -> Monomial v -> PP.Doc
ppMonomial pp (Mono ps)
  | M.null ps = PP.empty
  | otherwise = PP.hcat . PP.punctuate (PP.char '*') . map k $ M.toAscList ps
    where k (v,i) = pp v PP.<> PP.char '^' PP.<> PP.int i

-- | Pretty printing function for 'Polynomial'.
-- Should be used for basic types that do not provide the 'Pretty' instance.
ppPolynomial  :: (c -> PP.Doc) -> (v -> PP.Doc) -> Polynomial c v -> PP.Doc
ppPolynomial ppr ppv (Poly ts) = PP.hcat . PP.punctuate (PP.text " + ") $ map k $ M.toAscList ts
  where k (m@(Mono ps),c) = ppr c PP.<> if M.null ps then PP.empty else PP.char '*' PP.<> ppMonomial ppv m

