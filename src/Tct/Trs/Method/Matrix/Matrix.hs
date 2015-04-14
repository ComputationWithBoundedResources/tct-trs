{- |
Module      :  Tct.Encoding.Matrix
Copyright   :  TODO
               (c) Martin Avanzini <martin.avanzini@uibk.ac.at>,
               Georg Moser <georg.moser@uibk.ac.at>,
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  TODO andreas
Stability   :  unstable
Portability :  unportable
-}

{-# LANGUAGE ConstraintKinds, DeriveTraversable #-}

module Tct.Trs.Method.Matrix.Matrix
  (
    Vector(..)
  , Matrix(..)
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
  , diagonalEntries
  , diagonalNonZeros
  , diagonalZeros
  , maxVector
  , maximumVector
  , maxMatrix
  , maximumMatrix
  ) where

import qualified Data.Foldable as F
import qualified Tct.Core.Common.SemiRing as SR

newtype Vector a = Vector [a] deriving (Show, Eq, Functor, Foldable, Traversable)
newtype Matrix a = Matrix [Vector a] deriving (Show, Eq, Functor, Foldable, Traversable)

--instance Functor Vector where
--  fmap f (Vector v) = Vector $ map f v

--instance Functor Matrix where
--  fmap f (Matrix m) = Matrix $ map (fmap f) m

-- lift list operations to vector operations

liftVector :: ([a] -> b) -> Vector a -> b
liftVector f (Vector v) = f v

liftVector_ :: ([a] -> [b]) -> Vector a -> Vector b
liftVector_ f (Vector v) = Vector $ f v

-- lift list operations to matrix operations
liftMatrix :: ([Vector a] -> b) -> Matrix a -> b
liftMatrix f (Matrix m) = f m

liftMatrix_ :: ([Vector a] -> [Vector b]) -> Matrix a -> Matrix b
liftMatrix_ f (Matrix v) = Matrix $ f v

-- apply function f on the i-th element in a list.
adjustList :: (a -> a) -> Int -> [a] -> [a]
adjustList f i ls = let
  (p1,p2) = splitAt (pred i) ls
  in p1 ++ (f . head) p2 : tail p2

adjustVector :: (a -> a) -> Int -> Vector a -> Vector a
adjustVector f i = liftVector_ (adjustList f i)

adjustMatrix :: (a -> a) -> Int -> Int -> Matrix a -> Matrix a
adjustMatrix f i j = liftMatrix_ (adjustList (adjustVector f j) i)


vDim :: Vector a -> Int
vDim = liftVector length

-- returns the matrix dimensions, based on the number of rows
-- and the length of the first row
mDim :: Matrix a -> (Int,Int)
mDim (Matrix m) = let
  x = length m
  in if x == 0
     then (0,0)
     else (x, vDim (head m))

vEntry :: Int -> Vector a -> a
vEntry i = liftVector (!! pred i)

mEntry :: Int -> Int -> Matrix a -> a
mEntry i j = vEntry j . liftMatrix (!! pred i)

mRow :: Int -> Matrix a -> Vector a
mRow i = liftMatrix (!! pred i)

mCol :: Int -> Matrix a -> Vector a
mCol j m = Vector $ liftMatrix (map $ vEntry j) m

transpose :: Matrix a -> Matrix a
transpose (Matrix []) = Matrix []
transpose (Matrix (Vector [] : vs)) = transpose $ Matrix vs
transpose m@(Matrix (Vector (_:_) : _)) = let
  headcol = Vector $ liftMatrix (map $ liftVector head) m
  Matrix tailcols = transpose $ liftMatrix_ (map $ liftVector_ tail) m
  in Matrix $ headcol : tailcols

zeroVector :: SR.SemiRing a => Int -> Vector a
zeroVector dim = Vector $ replicate dim SR.zero

zeroMatrix :: SR.SemiRing a => Int -> Int -> Matrix a
zeroMatrix m n = Matrix $ replicate m (Vector $ replicate n SR.zero)

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

unit :: SR.SemiRing a => Int -> Matrix a
unit = identityMatrix

vAdd :: SR.SemiRing a => Vector a -> Vector a -> Vector a
vAdd (Vector v) (Vector w) = Vector $ zipWith SR.add v w

bigvAdd :: SR.SemiRing a => [Vector a] -> Vector a
bigvAdd vs = let
  dim = if null vs
        then 0
        else vDim (head vs)
  in foldr vAdd (zeroVector dim) vs

mAdd :: SR.SemiRing a => Matrix a -> Matrix a -> Matrix a
mAdd (Matrix vs) (Matrix ws) = Matrix $ zipWith vAdd vs ws

bigmAdd :: SR.SemiRing a => [Matrix a] -> Matrix a

bigmAdd ms =
  if null ms
  then Matrix []
  else foldr1 mAdd ms

scalarProduct :: SR.SemiRing a => Vector a -> Vector a -> a
scalarProduct (Vector v) (Vector w) = SR.bigAdd $ zipWith SR.mul v w

mvProduct :: SR.SemiRing a => Matrix a -> Vector a -> Vector a
mvProduct m v = Vector $ liftMatrix (map (`scalarProduct` v)) m

mProduct :: SR.SemiRing a => Matrix a -> Matrix a -> Matrix a
mProduct m n = transpose $ liftMatrix_ (map $ mvProduct m) (transpose n)

-- must use
bigmProduct :: SR.SemiRing a => [Matrix a] -> Matrix a
bigmProduct ms =
  if null ms
  then Matrix []
  else foldr1 mProduct ms


diagonalEntries :: Matrix a -> Vector a
diagonalEntries m = let
  (x,y) = mDim m
  l     = min x y
  in Vector $ map (\ i -> mEntry i i m) [1..l]

diagonalNonZeros :: (Eq a, SR.SemiRing a) => Matrix a -> Int
diagonalNonZeros m = let
  Vector diag = diagonalEntries m
  in length $ filter (/= SR.zero) diag

diagonalZeros :: (Eq a, SR.SemiRing a) => Matrix a -> Int
diagonalZeros m = let
  Vector diag = diagonalEntries m
  in length $ filter (== SR.zero) diag



{-
  parameter amax is a function of type Semiring a => a -> a -> a
  returning the maxium of both values
-}

maxVector :: (SR.SemiRing a) => (a -> a -> a) -> Vector a -> Vector a -> Vector a
maxVector amax (Vector v) (Vector w) = Vector $ zipWith amax v w

maximumVector :: (F.Foldable t, SR.SemiRing a)
                =>  (a -> a -> a)
                -> Int -> t (Vector a) -> Vector a
maximumVector amax dim = F.foldr (maxVector amax) (zeroVector dim)


maxMatrix :: (SR.SemiRing a)
            =>  (a -> a -> a) -> Matrix a -> Matrix a -> Matrix a
maxMatrix amax (Matrix m) (Matrix n) = Matrix $ zipWith (maxVector amax) m n

maximumMatrix :: (F.Foldable t, SR.SemiRing a)
                => (a -> a -> a) -> (Int,Int) -> t (Matrix a) -> Matrix a
maximumMatrix amax dims = F.foldr (maxMatrix amax) (uncurry zeroMatrix dims)
