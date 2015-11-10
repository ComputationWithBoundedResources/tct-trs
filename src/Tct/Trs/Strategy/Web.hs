-- | This module provides the custom strategy for the web interface.
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module Tct.Trs.Strategy.Web where

import           Tct.Core
import           Tct.Trs.Processors

webDeclaration = strategy "web"
  ( --degreeArg
  ba "matchbounds"
  , ba "matrices"
  , ba "matricesusableargs"
  , ba "matricesusablerules"
  , ba "polys"
  , ba "polysusableargs"
  , ba "polysusablerules"
  , ba "toi"
  , ba "compose"
  , ba "dp"
  , ba "dpusetuples"
  , ba "dpsimps"
  ) web

ba s = bool s ["Wether to use " ++ s ++ "."]

web
  -- deg
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

  =
  let deg = 3 in 

  when useToi (try toInnermost)
  .>>>
  if useDP
    then basics 0 deg .<||> (tDP .>>> basics 0 deg)
    else basics 0 deg

  where

  tDP =
    if useTuples then dependencyTuples else dependencyPairs
    .>>> try (when useDPSimps dpsimps)

  basics l u = matchbounds .<||> interpretations
    where
    matchbounds         = when useMatchbounds $ bounds Minimal Match .<||> bounds PerSymbol Match
    interpretations =
      if useDecompose
        then force $ chain [ tew (int d) | d <- [(max 0 l) .. (max l u)] ]
        else int u
    int d               = when useMatrices (mxs d) .<||> when usePolys (px d)

    ua b = if b then UArgs else NoUArgs
    ur b = if b then URules else NoURules

    mx dm dg = matrix' dm dg    Algebraic  (ua useMatricesUArgs) (ur useMatricesURules) sel NoGreedy
    px dg    = poly' (Mixed dg) NoRestrict (ua usePolysUArgs) (ur usePolysURules) sel NoGreedy
    sel      = if useDecompose then Just selAny else Nothing

    mxs 0 = mx 1 0
    mxs 1 = mx 1 1 .<||> mx 2 1 .<||> mx 3 1
    mxs 2 = mx 2 2 .<||> mx 3 2 .<||> mx 4 2
    mxs 3 = mx 3 3 .<||> mx 4 3
    mxs n = mx n n

