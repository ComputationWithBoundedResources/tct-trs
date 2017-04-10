-- Type.hs ---
--
-- Filename: Type.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Wed May  4 17:33:02 2016 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sat Apr  8 15:22:41 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 20
-- URL:
-- Doc URL:
-- Keywords:
-- Compatibility:
--
--

-- Commentary:
--
--
--
--

-- Change Log:
--
--
--
--
--
--
--

-- Code:

module Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Type where

data Vector = Vector1 Int
            | Vector2 Int Int
            | Vector3 Int Int Int
            | Vector4 Int Int Int Int
            | Vector5 Int Int Int Int Int
            | Vector6 Int Int Int Int Int Int
            | Vector7 Int Int Int Int Int Int Int
              deriving (Show)


maximumVectorLength :: Int
maximumVectorLength = 7

vectorLen :: Num a => Vector -> a
vectorLen Vector1{} = 1
vectorLen Vector2{} = 2
vectorLen Vector3{} = 3
vectorLen Vector4{} = 4
vectorLen Vector5{} = 5
vectorLen Vector6{} = 6
vectorLen Vector7{} = 7


vector0FromVectorInstance :: Vector -> Vector
vector0FromVectorInstance Vector1{} = Vector1 0
vector0FromVectorInstance Vector2{} = Vector2 0 0
vector0FromVectorInstance Vector3{} = Vector3 0 0 0
vector0FromVectorInstance Vector4{} = Vector4 0 0 0 0
vector0FromVectorInstance Vector5{} = Vector5 0 0 0 0 0
vector0FromVectorInstance Vector6{} = Vector6 0 0 0 0 0 0
vector0FromVectorInstance Vector7{} = Vector7 0 0 0 0 0 0 0


vectorMaxNr :: Int
vectorMaxNr = 10

-- instance OrderSolver Vector where
--   times nr (Vector1 y1)                   = Vector1 (fromIntegral nr*y1)
--   times nr (Vector2 y1 y2)                = Vector2 (fromIntegral nr*y1) (fromIntegral nr*y2)
--   times nr (Vector3 y1 y2 y3)             = Vector3 (fromIntegral nr*y1) (fromIntegral nr*y2)
--     (fromIntegral nr*y3)
--   times nr (Vector4 y1 y2 y3 y4)          = Vector4 (fromIntegral nr*y1) (fromIntegral nr*y2)
--     (fromIntegral nr*y3) (fromIntegral nr*y4)
--   times nr (Vector5 y1 y2 y3 y4 y5)       = Vector5 (fromIntegral nr*y1) (fromIntegral nr*y2)
--     (fromIntegral nr*y3) (fromIntegral nr*y4) (fromIntegral nr*y5)
--   times nr (Vector6 y1 y2 y3 y4 y5 y6)    = Vector6 (fromIntegral nr*y1) (fromIntegral nr*y2)
--     (fromIntegral nr*y3) (fromIntegral nr*y4) (fromIntegral nr*y5) (fromIntegral nr*y6)
--   times nr (Vector7 y1 y2 y3 y4 y5 y6 y7) = Vector7 (fromIntegral nr*y1) (fromIntegral nr*y2)
--     (fromIntegral nr*y3) (fromIntegral nr*y4) (fromIntegral nr*y5) (fromIntegral nr*y6)
--     (fromIntegral nr*y7)

instance Eq Vector where
  (Vector1 x1) == (Vector1 y1)                    = x1 == y1
  (Vector1 x1) == (Vector2 y1 y2)                 = x1 == y1 && 0 == y2
  (Vector1 x1) == (Vector3 y1 y2 y3)              = x1 == y1 && 0 == y2 && 0 == y3
  (Vector1 x1) == (Vector4 y1 y2 y3 y4)           = x1 == y1 && 0 == y2 && 0 == y3 && 0 == y4
  (Vector1 x1) == (Vector5 y1 y2 y3 y4 y5)        = x1 == y1 && 0 == y2 && 0 == y3 && 0 == y4 && 0 == y5
  (Vector1 x1) == (Vector6 y1 y2 y3 y4 y5 y6)     = x1 == y1 && 0 == y2 && 0 == y3 && 0 == y4 && 0 == y5 && 0 == y6
  (Vector1 x1) == (Vector7 y1 y2 y3 y4 y5 y6 y7)  = x1 == y1 && 0 == y2 && 0 == y3 && 0 == y4 && 0 == y5 && 0 == y6 && 0 == y7

  (Vector2 x1 x2) == (Vector2 y1 y2)                 = x1 == y1 && x2 == y2
  (Vector2 x1 x2) == (Vector3 y1 y2 y3 )             = x1 == y1 && x2 == y2 && 0 == y3
  (Vector2 x1 x2) == (Vector4 y1 y2 y3 y4 )          = x1 == y1 && x2 == y2 && 0 == y3 && 0 == y4
  (Vector2 x1 x2) == (Vector5 y1 y2 y3 y4 y5 )       = x1 == y1 && x2 == y2 && 0 == y3 && 0 == y4 && 0 == y5
  (Vector2 x1 x2) == (Vector6 y1 y2 y3 y4 y5 y6)     = x1 == y1 && x2 == y2 && 0 == y3 && 0 == y4 && 0 == y5 && 0 == y6
  (Vector2 x1 x2) == (Vector7 y1 y2 y3 y4 y5 y6 y7)  = x1 == y1 && x2 == y2 && 0 == y3 && 0 == y4 && 0 == y5 && 0 == y6 && 0 == y7

  (Vector3 x1 x2 x3) == (Vector3 y1 y2 y3)              = x1 == y1 && x2 == y2 && x3 == y3
  (Vector3 x1 x2 x3) == (Vector4 y1 y2 y3 y4 )          = x1 == y1 && x2 == y2 && x3 == y3 && 0 == y4
  (Vector3 x1 x2 x3) == (Vector5 y1 y2 y3 y4 y5 )       = x1 == y1 && x2 == y2 && x3 == y3 && 0 == y4 && 0 == y5
  (Vector3 x1 x2 x3) == (Vector6 y1 y2 y3 y4 y5 y6)     = x1 == y1 && x2 == y2 && x3 == y3 && 0 == y4 && 0 == y5 && 0 == y6
  (Vector3 x1 x2 x3) == (Vector7 y1 y2 y3 y4 y5 y6 y7)  = x1 == y1 && x2 == y2 && x3 == y3 && 0 == y4 && 0 == y5 && 0 == y6 && 0 == y7

  (Vector4 x1 x2 x3 x4) == (Vector4 y1 y2 y3 y4)           = x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4
  (Vector4 x1 x2 x3 x4) == (Vector5 y1 y2 y3 y4 y5 )       = x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && 0 == y5
  (Vector4 x1 x2 x3 x4) == (Vector6 y1 y2 y3 y4 y5 y6)     = x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && 0 == y5 && 0 == y6
  (Vector4 x1 x2 x3 x4) == (Vector7 y1 y2 y3 y4 y5 y6 y7)  = x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && 0 == y5 && 0 == y6 && 0 == y7

  (Vector5 x1 x2 x3 x4 x5) == (Vector5 y1 y2 y3 y4 y5)        = x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && x5 == y5
  (Vector5 x1 x2 x3 x4 x5) == (Vector6 y1 y2 y3 y4 y5 y6)     = x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && x5 == y5 && 0 == y6
  (Vector5 x1 x2 x3 x4 x5) == (Vector7 y1 y2 y3 y4 y5 y6 y7)  = x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && x5 == y5 && 0 == y6 && 0 == y7

  (Vector6 x1 x2 x3 x4 x5 x6) == (Vector6 y1 y2 y3 y4 y5 y6)     = x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && x5 == y5 && x6 == y6
  (Vector6 x1 x2 x3 x4 x5 x6) == (Vector7 y1 y2 y3 y4 y5 y6 y7)  = x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && x5 == y5 && x6 == y6 && 0 == y7

  (Vector7 x1 x2 x3 x4 x5 x6 x7) == (Vector7 y1 y2 y3 y4 y5 y6 y7) = x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && x5 == y5 && x6 == y6 && x7 == y7

  v1 == v2 = v2 == v1


-- normalizeVector :: Vector -> Vector
-- normalizeVector v@(Vector1 x1)
--   | x1 > vectorMaxNr = normalizeVector $ Vector2 (x1-vectorMaxNr) vectorMaxNr
--   | otherwise        = v
-- normalizeVector v@(Vector2 x1 x2)
--   | x2 > vectorMaxNr = normalizeVector $ Vector2 (x1 + x2 - vectorMaxNr) vectorMaxNr
--   | x1 > vectorMaxNr = normalizeVector $ Vector3 (x1-vectorMaxNr) vectorMaxNr x2
--   | otherwise        = v
-- normalizeVector v@(Vector3 x1 x2 x3)
--   | x3 > vectorMaxNr = normalizeVector $ Vector3 x1 (x2 + x3 - vectorMaxNr) vectorMaxNr
--   | x2 > vectorMaxNr = normalizeVector $ Vector3 (x1 + x2 - vectorMaxNr) vectorMaxNr x3
--   | x1 > vectorMaxNr = normalizeVector $ Vector4 (x1-vectorMaxNr) vectorMaxNr x2 x3
--   | otherwise        = v
-- normalizeVector v@(Vector4 x1 x2 x3 x4)
--   | x4 > vectorMaxNr = normalizeVector $ Vector4 x1 x2 (x3 + x4 - vectorMaxNr) vectorMaxNr
--   | x3 > vectorMaxNr = normalizeVector $ Vector4 x1 (x2 + x3 - vectorMaxNr) vectorMaxNr x4
--   | x2 > vectorMaxNr = normalizeVector $ Vector4 (x1 + x2 - vectorMaxNr) vectorMaxNr x3 x4
--   | x1 > vectorMaxNr = normalizeVector $ Vector5 (x1 - vectorMaxNr) vectorMaxNr x2 x3 x4
--   | otherwise        = v
-- normalizeVector v@(Vector5 x1 x2 x3 x4 x5)
--   | x5 > vectorMaxNr = normalizeVector $ Vector5 x1 x2 x3 (x4 + x5 - vectorMaxNr) vectorMaxNr
--   | x4 > vectorMaxNr = normalizeVector $ Vector5 x1 x2 (x3 + x4 - vectorMaxNr) vectorMaxNr x5
--   | x3 > vectorMaxNr = normalizeVector $ Vector5 x1 (x2 + x3 - vectorMaxNr) vectorMaxNr x4 x5
--   | x2 > vectorMaxNr = normalizeVector $ Vector5 (x1 + x2 - vectorMaxNr) vectorMaxNr x3 x4 x5
--   | x1 > vectorMaxNr = normalizeVector $ Vector6 (x1 - vectorMaxNr) vectorMaxNr x2 x3 x4 x5
--   | otherwise        = v
-- normalizeVector v@(Vector6 x1 x2 x3 x4 x5 x6)
--   | x6 > vectorMaxNr = normalizeVector $ Vector6 x1 x2 x3 x4 (x5 + x6 - vectorMaxNr) vectorMaxNr
--   | x5 > vectorMaxNr = normalizeVector $ Vector6 x1 x2 x3 (x4 + x5 - vectorMaxNr) vectorMaxNr x6
--   | x4 > vectorMaxNr = normalizeVector $ Vector6 x1 x2 (x3 + x4 - vectorMaxNr) vectorMaxNr x5 x6
--   | x3 > vectorMaxNr = normalizeVector $ Vector6 x1 (x2 + x3 - vectorMaxNr) vectorMaxNr x4 x5 x6
--   | x2 > vectorMaxNr = normalizeVector $ Vector6 (x1 + x2 - vectorMaxNr) vectorMaxNr x3 x4 x5 x6
--   | x1 > vectorMaxNr = normalizeVector $ Vector7 (x1 - vectorMaxNr) vectorMaxNr x2 x3 x4 x5 x6
--   | otherwise        = v
-- normalizeVector v@(Vector7 x1 x2 x3 x4 x5 x6 x7)
--   | x7 > vectorMaxNr = normalizeVector $ Vector7 x1 x2 x3 x4 x5 (x6 + x7 - vectorMaxNr) vectorMaxNr
--   | x6 > vectorMaxNr = normalizeVector $ Vector7 x1 x2 x3 x4 (x5 + x6 - vectorMaxNr) vectorMaxNr x7
--   | x5 > vectorMaxNr = normalizeVector $ Vector7 x1 x2 x3 (x4 + x5 - vectorMaxNr) vectorMaxNr x6 x7
--   | x4 > vectorMaxNr = normalizeVector $ Vector7 x1 x2 (x3 + x4 - vectorMaxNr) vectorMaxNr x5 x6 x7
--   | x3 > vectorMaxNr = normalizeVector $ Vector7 x1 (x2 + x3 - vectorMaxNr) vectorMaxNr x4 x5 x6 x7
--   | x2 > vectorMaxNr = normalizeVector $ Vector7 (x1 + x2 - vectorMaxNr) vectorMaxNr x3 x4 x5 x6 x7
--   | x1 > vectorMaxNr = error $ "Vector8 is not defined yet v " ++ show v
--   | otherwise        = v

-- vectorFromInt   :: Int -> Vector
-- vectorFromInt x
--   | x < 0       = Vector1 x -- may be used for calculation!!!
--   | x < maxNr 0 = Vector1 (nr x)
--   | x < maxNr 1 = let x' = x - maxNr 0
--                   in Vector2 (nr' x' (power 0)) (nr x')
--   | x < maxNr 2 = let x' = x - maxNr 1
--                   in Vector3 (nr' x' $ power 1) (nr' x' (power 0)) (nr x')
--   | x < maxNr 3 = let x' = x - maxNr 2
--                   in Vector4 (nr' x' $ power 2) (nr' x' $ power 1) (nr' x' (power 0)) (nr x')
--   | x < maxNr 4 = let x' = x - maxNr 3
--                   in Vector5 (nr' x' $ power 3) (nr' x' $ power 2) (nr' x' $ power 1) (nr' x' (power 0)) (nr x')
--   | x < maxNr 5 = let x' = x - maxNr 4
--                   in Vector6 (nr' x' $ power 4) (nr' x' $ power 3) (nr' x' $ power 2) (nr' x' $ power 1) (nr' x' (power 0)) (nr x')
--   | x < maxNr 6 = let x' = x - maxNr 5
--                   in Vector7 (nr' x' $ power 5) (nr' x' $ power 4) (nr' x' $ power 3) (nr' x' $ power 2) (nr' x' $ power 1) (nr' x' (power 0)) (nr x')
--   | x > maxNr 7 = error $ "Vector 8 is not defined yet"

--   where nr x = x `mod` (vectorMaxNr+1)
--         nr' x d = nr (x `div` d)
--         maxNr pow = sum (map (\p -> (vectorMaxNr+1)*(vectorMaxNr+1)^p) [0..pow])
        -- power pow = (vectorMaxNr+1)*(vectorMaxNr+1)^pow


-- denormalizeVector :: Vector -> Int
-- denormalizeVector (Vector1 x1)                   = x1
-- denormalizeVector (Vector2 x1 x2)                = denormalizeVector $ Vector1 ((x1+1)*(vectorMaxNr+1)+x2)
-- denormalizeVector (Vector3 x1 x2 x3)             = denormalizeVector $ Vector2 ((x1+1)*(vectorMaxNr+1)+x2) x3
-- denormalizeVector (Vector4 x1 x2 x3 x4)          = denormalizeVector $ Vector3 ((x1+1)*(vectorMaxNr+1)+x2) x3 x4
-- denormalizeVector (Vector5 x1 x2 x3 x4 x5)       = denormalizeVector $ Vector4 ((x1+1)*(vectorMaxNr+1)+x2) x3 x4 x5
-- denormalizeVector (Vector6 x1 x2 x3 x4 x5 x6)    = denormalizeVector $ Vector5 ((x1+1)*(vectorMaxNr+1)+x2) x3 x4 x5 x6
-- denormalizeVector (Vector7 x1 x2 x3 x4 x5 x6 x7) = denormalizeVector $ Vector6 ((x1+1)*(vectorMaxNr+1)+x2) x3 x4 x5 x6 x7


vectorFromInt   :: Int -> Vector
vectorFromInt x
  | x < 0       = Vector1 x -- may be used for calculation!!!
  | x < maxNr 0 = Vector1 (nr x)
  | x < maxNr 1 = let x' = x - maxNr 0
                  in Vector2 (nr x') (nr' x' (power 0))
  | x < maxNr 2 = let x' = x - maxNr 1
                  in Vector3 (nr x') (nr' x' $ power 0) (nr' x' (power 1))
  | x < maxNr 3 = let x' = x - maxNr 2
                  in Vector4 (nr x') (nr' x' $ power 0) (nr' x' $ power 1) (nr' x' (power 2))
  | x < maxNr 4 = let x' = x - maxNr 3
                  in Vector5 (nr x') (nr' x' $ power 0) (nr' x' $ power 1) (nr' x' $ power 2) (nr' x' (power 3))
  | x < maxNr 5 = let x' = x - maxNr 4
                  in Vector6 (nr x') (nr' x' $ power 0) (nr' x' $ power 1) (nr' x' $ power 2) (nr' x' $ power 3) (nr' x' (power 4))
  | x < maxNr 6 = let x' = x - maxNr 5
                  in Vector7 (nr x') (nr' x' $ power 0) (nr' x' $ power 1) (nr' x' $ power 2) (nr' x' $ power 3) (nr' x' $ power 4) (nr' x' (power 5))
  | x > maxNr 7 = error $ "Vector 8 is not defined yet"

  where nr x = x `mod` (vectorMaxNr+1)
        nr' x d = nr (x `div` d)
        maxNr pow = sum (map (\p -> (vectorMaxNr+1)*(vectorMaxNr+1)^p) [0..pow])

denormalizeVector :: Vector -> Int
denormalizeVector (Vector1 x1)                   = x1
denormalizeVector (Vector2 x1 x2)                = denormalizeVector $ Vector1 (x1+(x2+1)*(vectorMaxNr+1))
denormalizeVector (Vector3 x1 x2 x3)             = denormalizeVector $ Vector2 x1 (x2+(x3+1)*(vectorMaxNr+1))
denormalizeVector (Vector4 x1 x2 x3 x4)          = denormalizeVector $ Vector3 x1 x2 (x3+(x4+1)*(vectorMaxNr+1))
denormalizeVector (Vector5 x1 x2 x3 x4 x5)       = denormalizeVector $ Vector4 x1 x2 x3 (x4+(x5+1)*(vectorMaxNr+1))
denormalizeVector (Vector6 x1 x2 x3 x4 x5 x6)    = denormalizeVector $ Vector5 x1 x2 x3 x4 (x5+(x6+1)*(vectorMaxNr+1))
denormalizeVector (Vector7 x1 x2 x3 x4 x5 x6 x7) = denormalizeVector $ Vector6 x1 x2 x3 x4 x5 (x6+(x7+1)*(vectorMaxNr+1))

power :: Integral b => b -> Int
power pow = (vectorMaxNr+1)*(vectorMaxNr+1)^pow

instance Num Vector where
  (Vector1 x1) + (Vector1 y1)                   = -- normalizeVector $

    Vector1 (x1+y1)
  (Vector1 x1) + (Vector2 y1 y2)                = -- normalizeVector $
     Vector2 (x1+y1) y2
  (Vector1 x1) + (Vector3 y1 y2 y3)             = -- normalizeVector $
     Vector3 (x1+y1) y2 y3
  (Vector1 x1) + (Vector4 y1 y2 y3 y4)          = -- normalizeVector $
     Vector4 (x1+y1) y2 y3 y4
  (Vector1 x1) + (Vector5 y1 y2 y3 y4 y5)       = -- normalizeVector $
     Vector5 (x1+y1) y2 y3 y4 y5
  (Vector1 x1) + (Vector6 y1 y2 y3 y4 y5 y6)    = -- normalizeVector $
     Vector6 (x1+y1) y2 y3 y4 y5 y6
  (Vector1 x1) + (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1+y1) y2 y3 y4 y5 y6 y7

  (Vector2 x1 x2) + (Vector2 y1 y2)                = -- normalizeVector $
     Vector2 (x1+y1) (x2+y2)
  (Vector2 x1 x2) + (Vector3 y1 y2 y3 )            = -- normalizeVector $
     Vector3 (x1+y1) (x2+y2) y3
  (Vector2 x1 x2) + (Vector4 y1 y2 y3 y4 )         = -- normalizeVector $
     Vector4 (x1+y1) (x2+y2) y3 y4
  (Vector2 x1 x2) + (Vector5 y1 y2 y3 y4 y5 )      = -- normalizeVector $
     Vector5 (x1+y1) (x2+y2) y3 y4 y5
  (Vector2 x1 x2) + (Vector6 y1 y2 y3 y4 y5 y6 )   = -- normalizeVector $
     Vector6 (x1+y1) (x2+y2) y3 y4 y5 y6
  (Vector2 x1 x2) + (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1+y1) (x2+y2) y3 y4 y5 y6 y7
  v2@(Vector2 x1 x2) + v                           = v + v2


  (Vector3 x1 x2 x3) + (Vector3 y1 y2 y3)             = -- normalizeVector $
     Vector3 (x1+y1) (x2+y2) (x3+y3)
  (Vector3 x1 x2 x3) + (Vector4 y1 y2 y3 y4 )         = -- normalizeVector $
     Vector4 (x1+y1) (x2+y2) (x3+y3) y4
  (Vector3 x1 x2 x3) + (Vector5 y1 y2 y3 y4 y5 )      = -- normalizeVector $
     Vector5 (x1+y1) (x2+y2) (x3+y3) y4 y5
  (Vector3 x1 x2 x3) + (Vector6 y1 y2 y3 y4 y5 y6 )   = -- normalizeVector $
     Vector6 (x1+y1) (x2+y2) (x3+y3) y4 y5 y6
  (Vector3 x1 x2 x3) + (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1+y1) (x2+y2) (x3+y3) y4 y5 y6 y7
  v3@(Vector3 x1 x2 x3) + v                           = v + v3


  (Vector4 x1 x2 x3 x4) + (Vector4 y1 y2 y3 y4)          = -- normalizeVector $
     Vector4 (x1+y1) (x2+y2) (x3+y3) (x4+y4)
  (Vector4 x1 x2 x3 x4) + (Vector5 y1 y2 y3 y4 y5 )      = -- normalizeVector $
     Vector5 (x1+y1) (x2+y2) (x3+y3) (x4+y4) y5
  (Vector4 x1 x2 x3 x4) + (Vector6 y1 y2 y3 y4 y5 y6 )   = -- normalizeVector $
     Vector6 (x1+y1) (x2+y2) (x3+y3) (x4+y4) y5 y6
  (Vector4 x1 x2 x3 x4) + (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1+y1) (x2+y2) (x3+y3) (x4+y4) y5 y6 y7
  v4@(Vector4 x1 x2 x3 x4) + v                           = v + v4

  (Vector5 x1 x2 x3 x4 x5) + (Vector5 y1 y2 y3 y4 y5)        = -- normalizeVector $
     Vector5 (x1+y1) (x2+y2) (x3+y3) (x4+y4) (x5+y5)
  (Vector5 x1 x2 x3 x4 x5) + (Vector6 y1 y2 y3 y4 y5 y6    ) = -- normalizeVector $
     Vector6 (x1+y1) (x2+y2) (x3+y3) (x4+y4) (x5+y5) y6
  (Vector5 x1 x2 x3 x4 x5) + (Vector7 y1 y2 y3 y4 y5 y6 y7 ) = -- normalizeVector $
     Vector7 (x1+y1) (x2+y2) (x3+y3) (x4+y4) (x5+y5) y6 y7
  v5@(Vector5 x1 x2 x3 x4 x5) + v                            = v + v5

  (Vector6 x1 x2 x3 x4 x5 x6) + (Vector6 y1 y2 y3 y4 y5 y6)    = -- normalizeVector $
     Vector6 (x1+y1) (x2+y2) (x3+y3) (x4+y4) (x5+y5) (x6+y6)
  (Vector6 x1 x2 x3 x4 x5 x6) + (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1+y1) (x2+y2) (x3+y3) (x4+y4) (x5+y5) (x6+y6) y7
  v6@(Vector6 x1 x2 x3 x4 x5 x6) + v                           = v + v6


  (Vector7 x1 x2 x3 x4 x5 x6 x7) + (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1+y1) (x2+y2) (x3+y3) (x4+y4) (x5+y5) (x6+y6) (x7+y7)

  _ + _ = error "unkown error on + for Vector"

  (Vector1 x1) - (Vector1 y1)                   = -- normalizeVector $
     Vector1 (x1-y1)
  (Vector1 x1) - (Vector2 y1 y2)                = -- normalizeVector $
     Vector2 (x1-y1) y2
  (Vector1 x1) - (Vector3 y1 y2 y3)             = -- normalizeVector $
     Vector3 (x1-y1) y2 y3
  (Vector1 x1) - (Vector4 y1 y2 y3 y4)          = -- normalizeVector $
     Vector4 (x1-y1) y2 y3 y4
  (Vector1 x1) - (Vector5 y1 y2 y3 y4 y5)       = -- normalizeVector $
     Vector5 (x1-y1) y2 y3 y4 y5
  (Vector1 x1) - (Vector6 y1 y2 y3 y4 y5 y6)    = -- normalizeVector $
     Vector6 (x1-y1) y2 y3 y4 y5 y6
  (Vector1 x1) - (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1-y1) y2 y3 y4 y5 y6 y7

  (Vector2 x1 x2) - (Vector2 y1 y2)                = -- normalizeVector $
     Vector2 (x1-y1) (x2-y2)
  (Vector2 x1 x2) - (Vector3 y1 y2 y3 )            = -- normalizeVector $
     Vector3 (x1-y1) (x2-y2) y3
  (Vector2 x1 x2) - (Vector4 y1 y2 y3 y4 )         = -- normalizeVector $
     Vector4 (x1-y1) (x2-y2) y3 y4
  (Vector2 x1 x2) - (Vector5 y1 y2 y3 y4 y5 )      = -- normalizeVector $
     Vector5 (x1-y1) (x2-y2) y3 y4 y5
  (Vector2 x1 x2) - (Vector6 y1 y2 y3 y4 y5 y6 )   = -- normalizeVector $
     Vector6 (x1-y1) (x2-y2) y3 y4 y5 y6
  (Vector2 x1 x2) - (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1-y1) (x2-y2) y3 y4 y5 y6 y7
  v2@(Vector2 x1 x2) - v                           = v - v2


  (Vector3 x1 x2 x3) - (Vector3 y1 y2 y3)             = -- normalizeVector $
     Vector3 (x1-y1) (x2-y2) (x3-y3)
  (Vector3 x1 x2 x3) - (Vector4 y1 y2 y3 y4 )         = -- normalizeVector $
     Vector4 (x1-y1) (x2-y2) (x3-y3) y4
  (Vector3 x1 x2 x3) - (Vector5 y1 y2 y3 y4 y5 )      = -- normalizeVector $
     Vector5 (x1-y1) (x2-y2) (x3-y3) y4 y5
  (Vector3 x1 x2 x3) - (Vector6 y1 y2 y3 y4 y5 y6 )   = -- normalizeVector $
     Vector6 (x1-y1) (x2-y2) (x3-y3) y4 y5 y6
  (Vector3 x1 x2 x3) - (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1-y1) (x2-y2) (x3-y3) y4 y5 y6 y7
  v3@(Vector3 x1 x2 x3) - v                           = v - v3


  (Vector4 x1 x2 x3 x4) - (Vector4 y1 y2 y3 y4)          = -- normalizeVector $
     Vector4 (x1-y1) (x2-y2) (x3-y3) (x4-y4)
  (Vector4 x1 x2 x3 x4) - (Vector5 y1 y2 y3 y4 y5 )      = -- normalizeVector $
     Vector5 (x1-y1) (x2-y2) (x3-y3) (x4-y4) y5
  (Vector4 x1 x2 x3 x4) - (Vector6 y1 y2 y3 y4 y5 y6 )   = -- normalizeVector $
     Vector6 (x1-y1) (x2-y2) (x3-y3) (x4-y4) y5 y6
  (Vector4 x1 x2 x3 x4) - (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1-y1) (x2-y2) (x3-y3) (x4-y4) y5 y6 y7
  v4@(Vector4 x1 x2 x3 x4) - v                           = v - v4

  (Vector5 x1 x2 x3 x4 x5) - (Vector5 y1 y2 y3 y4 y5)        = -- normalizeVector $
     Vector5 (x1-y1) (x2-y2) (x3-y3) (x4-y4) (x5-y5)
  (Vector5 x1 x2 x3 x4 x5) - (Vector6 y1 y2 y3 y4 y5 y6    ) = -- normalizeVector $
     Vector6 (x1-y1) (x2-y2) (x3-y3) (x4-y4) (x5-y5) y6
  (Vector5 x1 x2 x3 x4 x5) - (Vector7 y1 y2 y3 y4 y5 y6 y7 ) = -- normalizeVector $
     Vector7 (x1-y1) (x2-y2) (x3-y3) (x4-y4) (x5-y5) y6 y7
  v5@(Vector5 x1 x2 x3 x4 x5) - v                            = v - v5

  (Vector6 x1 x2 x3 x4 x5 x6) - (Vector6 y1 y2 y3 y4 y5 y6)    = -- normalizeVector $
     Vector6 (x1-y1) (x2-y2) (x3-y3) (x4-y4) (x5-y5) (x6-y6)
  (Vector6 x1 x2 x3 x4 x5 x6) - (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1-y1) (x2-y2) (x3-y3) (x4-y4) (x5-y5) (x6-y6) y7
  v6@(Vector6 x1 x2 x3 x4 x5 x6) - v                           = v - v6


  (Vector7 x1 x2 x3 x4 x5 x6 x7) - (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1-y1) (x2-y2) (x3-y3) (x4-y4) (x5-y5) (x6-y6) (x7-y7)

  _ - _ = error "unkown error on - for Vector"

  fromInteger = vectorFromInt . fromIntegral

  abs _ = error "abs not defined for Vector type"
  signum _ = error "signum not defined for Vector type"

  (Vector1 x1) * (Vector1 y1)                   = -- normalizeVector $
     Vector1 (x1*y1)
  (Vector1 x1) * (Vector2 y1 y2)                = -- normalizeVector $
     Vector2 (x1*y1) y2
  (Vector1 x1) * (Vector3 y1 y2 y3)             = -- normalizeVector $
     Vector3 (x1*y1) y2 y3
  (Vector1 x1) * (Vector4 y1 y2 y3 y4)          = -- normalizeVector $
     Vector4 (x1*y1) y2 y3 y4
  (Vector1 x1) * (Vector5 y1 y2 y3 y4 y5)       = -- normalizeVector $
     Vector5 (x1*y1) y2 y3 y4 y5
  (Vector1 x1) * (Vector6 y1 y2 y3 y4 y5 y6)    = -- normalizeVector $
     Vector6 (x1*y1) y2 y3 y4 y5 y6
  (Vector1 x1) * (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1*y1) y2 y3 y4 y5 y6 y7

  (Vector2 x1 x2) * (Vector2 y1 y2)                = -- normalizeVector $
     Vector2 (x1*y1) (x2*y2)
  (Vector2 x1 x2) * (Vector3 y1 y2 y3 )            = -- normalizeVector $
     Vector3 (x1*y1) (x2*y2) y3
  (Vector2 x1 x2) * (Vector4 y1 y2 y3 y4 )         = -- normalizeVector $
     Vector4 (x1*y1) (x2*y2) y3 y4
  (Vector2 x1 x2) * (Vector5 y1 y2 y3 y4 y5 )      = -- normalizeVector $
     Vector5 (x1*y1) (x2*y2) y3 y4 y5
  (Vector2 x1 x2) * (Vector6 y1 y2 y3 y4 y5 y6 )   = -- normalizeVector $
     Vector6 (x1*y1) (x2*y2) y3 y4 y5 y6
  (Vector2 x1 x2) * (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1*y1) (x2*y2) y3 y4 y5 y6 y7
  v2@(Vector2 x1 x2) * v                           = v * v2


  (Vector3 x1 x2 x3) * (Vector3 y1 y2 y3)             = -- normalizeVector $
     Vector3 (x1*y1) (x2*y2) (x3*y3)
  (Vector3 x1 x2 x3) * (Vector4 y1 y2 y3 y4 )         = -- normalizeVector $
     Vector4 (x1*y1) (x2*y2) (x3*y3) y4
  (Vector3 x1 x2 x3) * (Vector5 y1 y2 y3 y4 y5 )      = -- normalizeVector $
     Vector5 (x1*y1) (x2*y2) (x3*y3) y4 y5
  (Vector3 x1 x2 x3) * (Vector6 y1 y2 y3 y4 y5 y6 )   = -- normalizeVector $
     Vector6 (x1*y1) (x2*y2) (x3*y3) y4 y5 y6
  (Vector3 x1 x2 x3) * (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1*y1) (x2*y2) (x3*y3) y4 y5 y6 y7
  v3@(Vector3 x1 x2 x3) * v                           = v * v3


  (Vector4 x1 x2 x3 x4) * (Vector4 y1 y2 y3 y4)          = -- normalizeVector $
     Vector4 (x1*y1) (x2*y2) (x3*y3) (x4*y4)
  (Vector4 x1 x2 x3 x4) * (Vector5 y1 y2 y3 y4 y5 )      = -- normalizeVector $
     Vector5 (x1*y1) (x2*y2) (x3*y3) (x4*y4) y5
  (Vector4 x1 x2 x3 x4) * (Vector6 y1 y2 y3 y4 y5 y6 )   = -- normalizeVector $
     Vector6 (x1*y1) (x2*y2) (x3*y3) (x4*y4) y5 y6
  (Vector4 x1 x2 x3 x4) * (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1*y1) (x2*y2) (x3*y3) (x4*y4) y5 y6 y7
  v4@(Vector4 x1 x2 x3 x4) * v                           = v * v4

  (Vector5 x1 x2 x3 x4 x5) * (Vector5 y1 y2 y3 y4 y5)        = -- normalizeVector $
     Vector5 (x1*y1) (x2*y2) (x3*y3) (x4*y4) (x5*y5)
  (Vector5 x1 x2 x3 x4 x5) * (Vector6 y1 y2 y3 y4 y5 y6    ) = -- normalizeVector $
     Vector6 (x1*y1) (x2*y2) (x3*y3) (x4*y4) (x5*y5) y6
  (Vector5 x1 x2 x3 x4 x5) * (Vector7 y1 y2 y3 y4 y5 y6 y7 ) = -- normalizeVector $
     Vector7 (x1*y1) (x2*y2) (x3*y3) (x4*y4) (x5*y5) y6 y7
  v5@(Vector5 x1 x2 x3 x4 x5) * v                            = v * v5

  (Vector6 x1 x2 x3 x4 x5 x6) * (Vector6 y1 y2 y3 y4 y5 y6)    = -- normalizeVector $
     Vector6 (x1*y1) (x2*y2) (x3*y3) (x4*y4) (x5*y5) (x6*y6)
  (Vector6 x1 x2 x3 x4 x5 x6) * (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1*y1) (x2*y2) (x3*y3) (x4*y4) (x5*y5) (x6*y6) y7
  v6@(Vector6 x1 x2 x3 x4 x5 x6) * v                           = v * v6


  (Vector7 x1 x2 x3 x4 x5 x6 x7) * (Vector7 y1 y2 y3 y4 y5 y6 y7) = -- normalizeVector $
     Vector7 (x1*y1) (x2*y2) (x3*y3) (x4*y4) (x5*y5) (x6*y6) (x7*y7)

  _ * _ = error "unkown error on * for Vector"


  -- _ * _ = error "* not defined for Vector type"


instance Ord Vector where
  (Vector1 x1) <= (Vector1 y1)                   = x1<=y1
  (Vector1 x1) <= (Vector2 y1 y2)                = x1<=y1 || 0<=y2
  (Vector1 x1) <= (Vector3 y1 y2 y3)             = x1<=y1 || 0<=y2 || 0<=y3
  (Vector1 x1) <= (Vector4 y1 y2 y3 y4)          = x1<=y1 || 0<=y2 || 0<=y3 || 0<=y4
  (Vector1 x1) <= (Vector5 y1 y2 y3 y4 y5)       = x1<=y1 || 0<=y2 || 0<=y3 || 0<=y4 || 0<=y5
  (Vector1 x1) <= (Vector6 y1 y2 y3 y4 y5 y6)    = x1<=y1 || 0<=y2 || 0<=y3 || 0<=y4 || 0<=y5 || 0<=y6
  (Vector1 x1) <= (Vector7 y1 y2 y3 y4 y5 y6 y7) = x1<=y1 || 0<=y2 || 0<=y3 || 0<=y4 || 0<=y5 || 0<=y6 || 0<=y7

  (Vector2 x1 x2) <= (Vector2 y1 y2)                = x1<=y1 || (x1==y1 && x2<=y2)
  (Vector2 x1 x2) <= (Vector3 y1 y2 y3 )            = x1<=y1 || (x1==y1 && x2<=y2) || 0<=y3
  (Vector2 x1 x2) <= (Vector4 y1 y2 y3 y4 )         = x1<=y1 || (x1==y1 && x2<=y2) || 0<=y3 || 0<=y4
  (Vector2 x1 x2) <= (Vector5 y1 y2 y3 y4 y5 )      = x1<=y1 || (x1==y1 && x2<=y2) || 0<=y3 || 0<=y4 || 0<=y5
  (Vector2 x1 x2) <= (Vector6 y1 y2 y3 y4 y5 y6 )   = x1<=y1 || (x1==y1 && x2<=y2) || 0<=y3 || 0<=y4 || 0<=y5 || 0<=y6
  (Vector2 x1 x2) <= (Vector7 y1 y2 y3 y4 y5 y6 y7) = x1<=y1 || (x1==y1 && x2<=y2) || 0<=y3 || 0<=y4 || 0<=y5 || 0<=y6 || 0<=y7


  (Vector3 x1 x2 x3) <= (Vector3 y1 y2 y3)             = x1<=y1 || x2<=y2 || x3<=y3
  (Vector3 x1 x2 x3) <= (Vector4 y1 y2 y3 y4 )         = x1<=y1 || x2<=y2 || x3<=y3 || 0<=y4
  (Vector3 x1 x2 x3) <= (Vector5 y1 y2 y3 y4 y5 )      = x1<=y1 || x2<=y2 || x3<=y3 || 0<=y4 || 0<=y5
  (Vector3 x1 x2 x3) <= (Vector6 y1 y2 y3 y4 y5 y6 )   = x1<=y1 || x2<=y2 || x3<=y3 || 0<=y4 || 0<=y5 || 0<=y6
  (Vector3 x1 x2 x3) <= (Vector7 y1 y2 y3 y4 y5 y6 y7) = x1<=y1 || x2<=y2 || x3<=y3 || 0<=y4 || 0<=y5 || 0<=y6 || 0<=y7


  (Vector4 x1 x2 x3 x4) <= (Vector4 y1 y2 y3 y4)          = x1<=y1 || x2<=y2 || x3<=y3 || x4<=y4
  (Vector4 x1 x2 x3 x4) <= (Vector5 y1 y2 y3 y4 y5 )      = x1<=y1 || x2<=y2 || x3<=y3 || x4<=y4 || 0<=y5
  (Vector4 x1 x2 x3 x4) <= (Vector6 y1 y2 y3 y4 y5 y6 )   = x1<=y1 || x2<=y2 || x3<=y3 || x4<=y4 || 0<=y5 || 0<=y6
  (Vector4 x1 x2 x3 x4) <= (Vector7 y1 y2 y3 y4 y5 y6 y7) = x1<=y1 || x2<=y2 || x3<=y3 || x4<=y4 || 0<=y5 || 0<=y6 || 0<=y7


  (Vector5 x1 x2 x3 x4 x5) <= (Vector5 y1 y2 y3 y4 y5)        = x1<=y1 || x2<=y2 || x3<=y3 || x4<=y4 || x5<=y5
  (Vector5 x1 x2 x3 x4 x5) <= (Vector6 y1 y2 y3 y4 y5 y6    ) = x1<=y1 || x2<=y2 || x3<=y3 || x4<=y4 || x5<=y5 || 0<=y6
  (Vector5 x1 x2 x3 x4 x5) <= (Vector7 y1 y2 y3 y4 y5 y6 y7 ) = x1<=y1 || x2<=y2 || x3<=y3 || x4<=y4 || x5<=y5 || 0<=y6 || 0<=y7


  (Vector6 x1 x2 x3 x4 x5 x6) <= (Vector6 y1 y2 y3 y4 y5 y6)    = x1<=y1 || x2<=y2 || x3<=y3 || x4<=y4 || x5<=y5 || x6<=x6
  (Vector6 x1 x2 x3 x4 x5 x6) <= (Vector7 y1 y2 y3 y4 y5 y6 y7) = x1<=y1 || x2<=y2 || x3<=y3 || x4<=y4 || x5<=y5 || x6<=y6 || 0<=y7


  (Vector7 x1 x2 x3 x4 x5 x6 x7) <= (Vector7 y1 y2 y3 y4 y5 y6 y7) = x1<=y1 || x2<=y2 || x3<=y3 || x4<=y4 || x5<=y5 || x6<=y6 || x7<=y7

  v1 <= v2                           = v2 <= v1

instance Enum Vector where
  toEnum   = vectorFromInt
  fromEnum = denormalizeVector


--
-- Type.hs ends here
