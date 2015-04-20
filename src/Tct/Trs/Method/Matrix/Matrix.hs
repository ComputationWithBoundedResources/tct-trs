{-|
Module      : Tct.Trs.Method.Matrix.Matrix
Description : Defines matrix and vector data types and their operations.
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

module Tct.Trs.Method.Matrix.Matrix
  (
  -- * data types
    Vector(..)
  , Matrix(..)
  -- *
  -- ** basic functions
  , liftVector
  , liftVector_
  , liftMatrix
  , liftMatrix_
  , adjustList
  , adjustVector
  , adjustMatrix
  , vDim
  , mDim
  , vEntry
  , mEntry
  , mCol
  , mRow
  , transpose
  , diagonalEntries
  -- ** SemiRing functions
  , zeroVector
  , zeroMatrix
  , identityMatrix
  , unit
  , vAdd
  , bigvAdd
  , mAdd
  , bigmAdd
  , scalarProduct
  , mvProduct
  , mProduct
  , bigmProduct
  , diagonalNonZeros
  , diagonalZeros
  , maxVector
  , maximumVector
  , maxMatrix
  , maximumMatrix
  ) where

import qualified Data.Foldable as F
import qualified Data.Traversable as F

import qualified Tct.Core.Common.Xml as Xml
import qualified Tct.Core.Common.SemiRing as SR

----------------------------------------------------------------------
-- data types
----------------------------------------------------------------------


-- | Vector data type
newtype Vector a = Vector [a] deriving (Show, Eq, Functor, F.Foldable, F.Traversable)

-- | Matrix data type
newtype Matrix a = Matrix [Vector a] deriving (Show, Eq, Functor, F.Foldable, F.Traversable)

----------------------------------------------------------------------
-- functions
----------------------------------------------------------------------


----------------------------------------------------------------------
-- 1. basic functions
----------------------------------------------------------------------


-- | lifts a list reducing function
liftVector :: ([a] -> b) -> Vector a -> b
liftVector f (Vector v) = f v

-- | lifts a list mapping function
liftVector_ :: ([a] -> [b]) -> Vector a -> Vector b
liftVector_ f (Vector v) = Vector $ f v

-- | lifts a 'Vector' reducing function
liftMatrix :: ([Vector a] -> b) -> Matrix a -> b
liftMatrix f (Matrix m) = f m

-- | lifts a 'Vector' mapping function
liftMatrix_ :: ([Vector a] -> [Vector b]) -> Matrix a -> Matrix b
liftMatrix_ f (Matrix v) = Matrix $ f v

-- | apply function @f@ on the @i@-th element in a list
adjustList :: (a -> a) -> Int -> [a] -> [a]
adjustList f i ls = let
  (p1,p2) = splitAt (pred i) ls
  in p1 ++ (f . head) p2 : tail p2

-- | apply function @f@ on the @i@-th entry of a 'Vector'
adjustVector :: (a -> a) -> Int -> Vector a -> Vector a
adjustVector f i = liftVector_ (adjustList f i)

-- | apply function @f@ on the @i-j@ entry of a 'Matrix'
adjustMatrix :: (a -> a) -> Int -> Int -> Matrix a -> Matrix a
adjustMatrix f i j = liftMatrix_ (adjustList (adjustVector f j) i)

-- | get the dimension of a 'Vector'
vDim :: Vector a -> Int
vDim = liftVector length

-- | get the dimensions @(rows,columns)@ of a 'Matrix'
mDim :: Matrix a -> (Int,Int)
mDim (Matrix m) = let
  x = length m
  in if x == 0
     then (0,0)
     else (x, vDim (head m))

-- | get entry @i@ of a 'Vector'
vEntry :: Int -> Vector a -> a
vEntry i = liftVector (!! pred i)

-- | get entry @i-j@ of a 'Matrix'
mEntry :: Int -> Int -> Matrix a -> a
mEntry i j = vEntry j . liftMatrix (!! pred i)

-- | get the @i@-th row of a 'Matrix'
mRow :: Int -> Matrix a -> Vector a
mRow i = liftMatrix (!! pred i)

-- | get the @j@-th column of a 'Matrix'
mCol :: Int -> Matrix a -> Vector a
mCol j m = Vector $ liftMatrix (map $ vEntry j) m

-- | transpose a 'Matrix'
transpose :: Matrix a -> Matrix a
transpose (Matrix []) = Matrix []
transpose (Matrix (Vector [] : vs)) = transpose $ Matrix vs
transpose m@(Matrix (Vector (_:_) : _)) = let
  headcol = Vector $ liftMatrix (map $ liftVector head) m
  Matrix tailcols = transpose $ liftMatrix_ (map $ liftVector_ tail) m
  in Matrix $ headcol : tailcols

-- | get the diagonal entries of a 'Matrix'
diagonalEntries :: Matrix a -> Vector a
diagonalEntries m = let
  (x,y) = mDim m
  l     = min x y
  in Vector $ map (\ i -> mEntry i i m) [1..l]

----------------------------------------------------------------------
-- 2. SemiRing functions
----------------------------------------------------------------------


-- | zero-'Vector' of dimension @dim@
zeroVector :: SR.SemiRing a => Int -> Vector a
zeroVector dim = Vector $ replicate dim SR.zero

-- | zero-'Matrix' with @m@ rows and @n@ columns
zeroMatrix :: SR.SemiRing a => Int -> Int -> Matrix a
zeroMatrix m n = Matrix $ replicate m (Vector $ replicate n SR.zero)

-- | identity-'Matrix' of dimension 'd x d'
identityMatrix :: SR.SemiRing a => Int -> Matrix a
identityMatrix d
  | d == 0     = Matrix []
  | otherwise = let
    r = liftVector_ (SR.one :) (zeroVector $ pred d)
    m = identityMatrix $ pred d
    in liftMatrix_ (r :) (addZeros m)
    where
      addZeros :: SR.SemiRing a => Matrix a -> Matrix a
      addZeros = liftMatrix_ (map (liftVector_ (SR.zero :)))

-- | same as "identityMatrix"
unit :: SR.SemiRing a => Int -> Matrix a
unit = identityMatrix

-- | add two 'Vector's of the same dimension
vAdd :: SR.SemiRing a => Vector a -> Vector a -> Vector a
vAdd (Vector v) (Vector w) = Vector $ zipWith SR.add v w

-- | sum of a list of 'Vector's
bigvAdd :: SR.SemiRing a => [Vector a] -> Vector a
bigvAdd vs = let
  dim = if null vs
        then 0
        else vDim (head vs)
  in foldr vAdd (zeroVector dim) vs

-- | add two matrices of same dimensions
mAdd :: SR.SemiRing a => Matrix a -> Matrix a -> Matrix a
mAdd (Matrix vs) (Matrix ws) = Matrix $ zipWith vAdd vs ws

-- | sum of a list of matrices
bigmAdd :: SR.SemiRing a => [Matrix a] -> Matrix a

bigmAdd ms =
  if null ms
  then Matrix []
  else foldr1 mAdd ms

-- | scalar product of two 'Vector's
scalarProduct :: SR.SemiRing a => Vector a -> Vector a -> a
scalarProduct (Vector v) (Vector w) = SR.bigAdd $ zipWith SR.mul v w

-- | multiply a 'Matrix' and a 'Vector'
mvProduct :: SR.SemiRing a => Matrix a -> Vector a -> Vector a
mvProduct m v = Vector $ liftMatrix (map (`scalarProduct` v)) m

-- | multiply a two matrices
mProduct :: SR.SemiRing a => Matrix a -> Matrix a -> Matrix a
mProduct m n = transpose $ liftMatrix_ (map $ mvProduct m) (transpose n)

-- | multiply a list of matrices
bigmProduct :: SR.SemiRing a => [Matrix a] -> Matrix a
bigmProduct ms =
  if null ms
  then Matrix []
  else foldr1 mProduct ms

-- | count the non-zeros in the diagonal of a "Matrix'
diagonalNonZeros :: (Eq a, SR.SemiRing a) => Matrix a -> Int
diagonalNonZeros m = let
  Vector diag = diagonalEntries m
  in length $ filter (/= SR.zero) diag

-- | count the zeros in the diagonal of a 'Matrix'
diagonalZeros :: (Eq a, SR.SemiRing a) => Matrix a -> Int
diagonalZeros m = let
  Vector diag = diagonalEntries m
  in length $ filter (== SR.zero) diag




-- | 'Vector' of the maximum entries of two 'Vector's. Needs a @max@ function
maxVector :: (SR.SemiRing a) => (a -> a -> a) -> Vector a -> Vector a -> Vector a
maxVector amax (Vector v) (Vector w) = Vector $ zipWith amax v w


-- | 'Vector' of the maximum entries of a list of 'Vector's. Needs a @max@ function
maximumVector :: (F.Foldable t, SR.SemiRing a)
                =>  (a -> a -> a)
                -> Int -> t (Vector a) -> Vector a
maximumVector amax dim = F.foldr (maxVector amax) (zeroVector dim)

-- | 'Matrix' of the maximum entries of two matrices. Needs a @max@ function
maxMatrix :: (SR.SemiRing a)
            =>  (a -> a -> a) -> Matrix a -> Matrix a -> Matrix a
maxMatrix amax (Matrix m) (Matrix n) = Matrix $ zipWith (maxVector amax) m n

-- | 'Matrix' of the maximum entries of a list of 'Vector's. Needs a @max@ function
maximumMatrix :: (F.Foldable t, SR.SemiRing a)
                => (a -> a -> a) -> (Int,Int) -> t (Matrix a) -> Matrix a
maximumMatrix amax dims = F.foldr (maxMatrix amax) (uncurry zeroMatrix dims)



----------------------------------------------------------------------
-- instances
----------------------------------------------------------------------

instance Xml.Xml (Vector Int) where
  toXml (Vector cs) = Xml.elt "vector" [ Xml.elt "coefficient" [ Xml.elt "integer" [Xml.int c] ] | c <- cs]
  toCeTA            = Xml.toXml

instance Xml.Xml (Matrix Int) where
  toXml mx = let Matrix vs = transpose mx in Xml.elt "matrix" (map Xml.toXml vs)
  toCeTA   = Xml.toXml
