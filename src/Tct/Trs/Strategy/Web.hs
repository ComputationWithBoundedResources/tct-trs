{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
-- | This module provides strategies for the web interface.
module Tct.Trs.Strategy.Web
  ( webCustomDeclaration
  , webAutomaticDeclaration
  ) where


import Tct.Core
import Tct.Trs.Data.Problem         (isInnermostProblem)
import Tct.Trs.Processors           hiding (matrices, polys)
import Tct.Trs.Strategy.Competition (competition')


webAutomaticDeclaration = strategy "webAutomatic" () (competition' Fastest)

webCustomDeclaration = strategy "webCustom"
  ( degreeArg `optional` 2
  , ba "matchbounds"
  , ba "matrices"
  , ba "matricesusableargs"
  , ba "matricesusablerules"
  , ba "polys"
  , ba "polysusableargs"
  , ba "polysusablerules"
  , ba "toi"
  , ba "compose"
  , ba "dp"
  , ba "dptuples"
  , ba "dpsimps"
  , ba "dpdecompose"
  ) custom

-- ba :: String -> Argument 'Optional Bool
ba s = bool s ["Wether to use " ++ s ++ "."] `optional` True

custom
  -- deg
  deg
  -- base
  useMatchbounds
  useMatrices
  useMatricesURules
  useMatricesUArgs
  usePolys
  usePolysURules
  usePolysUArgs
  -- transform
  useToi
  useDecompose
  -- dp
  useDP
  useTuples
  useDPSimps
  useDPDecompose

  =

  when useToi (try toInnermost)
  .>>>
  if useDP
    then (basics 0 deg .>>> abort) .<||> (asDP .>>> onDP .>>> basics 0 deg .>>> abort)
    else basics 0 deg

  where

  asDP = withProblem $ \prob ->
    if useTuples && isInnermostProblem prob
       then dependencyTuples
       else dependencyPairs
  onDP =
     try (when useDPSimps dpsimps)
    .>>> te (when useDPDecompose (force decomposeDG') .>>> try (when useDPSimps dpsimps))

  basics l u = matchbounds .<||> interpretations
    where
    matchbounds     = force $ when useMatchbounds $ bounds Minimal Match .<||> bounds PerSymbol Match
    interpretations = force $
      if useDecompose
        then chain [ tew (int d) | d <- [(max 0 l) .. (max l u)] ]
        else int u
    int d               = matrices d .<||> polys d

    matrices d = force $ when useMatrices (mxs d)
    polys    d = force $ when usePolys    (px d)

    ua b = if b then UArgs else NoUArgs
    ur b = if b then URules else NoURules

    mx dm dg = matrix' dm dg    Algebraic  (ua useMatricesUArgs) (ur useMatricesURules) sel NoGreedy
    px dg    = poly' (Mixed dg) Restrict   (ua usePolysUArgs) (ur usePolysURules) sel NoGreedy
    sel      = if useDecompose then Just selAny else Nothing

    mxs 0 = mx 1 0
    mxs 1 = mx 1 1 .<||> mx 2 1 .<||> mx 3 1
    mxs 2 = mx 2 2 .<||> mx 3 2 .<||> mx 4 2
    mxs 3 = mx 3 3 .<||> mx 4 3
    mxs n = mx n n

