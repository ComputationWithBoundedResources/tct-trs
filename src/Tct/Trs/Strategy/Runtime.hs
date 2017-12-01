{-# LANGUAGE ImplicitParams            #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module Tct.Trs.Strategy.Runtime
  ( runtime
  , runtime'
  , runtimeDeclaration
  ) where


import           Tct.Core
import qualified Tct.Core.Data                as T

import           Tct.Trs.Data
import qualified Tct.Trs.Data.DependencyGraph as DG
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.Rules as RS
import           Tct.Trs.Processors
import           Tct.Trs.Processor.Matrix.MI  as MI (mxeda, mxida)


-- | Declaration for "derivational" strategy.
runtimeDeclaration :: T.Declaration ('[T.Argument 'Optional CombineWith] T.:-> TrsStrategy)
runtimeDeclaration = strategy "runtime" (T.OneTuple $ combineWithArg `T.optional` Fastest) runtimeStrategy

-- | Default strategy for "runtime" complexity.
runtime :: TrsStrategy
runtime  = T.deflFun runtimeDeclaration

-- | A strategy for "runtime" complexity.
runtime' :: CombineWith -> TrsStrategy
runtime' = T.declFun runtimeDeclaration


--- * direct ---------------------------------------------------------------------------------------------------------

mx dim deg   = matrix' dim deg Algebraic ?ua ?ur ?sel
mxCP dim deg = matrixCP' dim deg Algebraic ?ua ?ur

mxseda dim       = MI.mxeda dim     ?ua ?ur ?sel
mxsida dim deg   = MI.mxida dim deg ?ua ?ur ?sel

px 1 = poly' Linear Restrict ?ua ?ur ?sel
px n = poly' (Mixed n) Restrict ?ua ?ur ?sel

pxCP 1 = polyCP' Linear Restrict ?ua ?ur
pxCP n = polyCP' (Mixed n) Restrict ?ua ?ur

wgOnUsable dim deg = weightgap' dim deg Algebraic ?ua WgOnTrs
wg dim deg         = weightgap' dim deg Algebraic ?ua WgOnAny

ax, axLeaf :: Int -> Int -> TrsStrategy
ax lo up = ara' NoHeuristics (Just 1) lo up 8
axLeaf lo up = ara' NoHeuristics Nothing lo up 5
axHeur lo up = ara' Heuristics Nothing lo up 3

--- * rc -------------------------------------------------------------------------------------------------------------

runtimeStrategy :: CombineWith -> TrsStrategy
runtimeStrategy combineWith = withState $ \st ->
  let mto = T.remainingTime st in mto `seq` runtimeStrategy' combineWith mto

runtimeStrategy' :: CombineWith -> Maybe Int -> TrsStrategy
runtimeStrategy' combineWith mto =
  let
    ?timeoutRel = timeoutRelative mto
    ?combine    = case combineWith of { Best -> best cmpTimeUB; Fastest -> fastest }
    ?ua         = UArgs
    ?ur         = URules
    ?sel        = Just selAny
  in

  withProblem $ \ prob ->
    if Prob.isInnermostProblem prob
      then best cmpTimeUB [ timeoutIn 7 direct
                          , ?combine
                            [ timeoutIn 18 interp
                            , timeoutIn 20 raml
                            , rci
                            ]
                          ]
      else ite toInnermost rci rc

direct = try trivial
  .>>> tew (fastest [axHeur 1 2, axLeaf 1 2]) -- up to quadratic bound
  .>>> empty


withDP =
  try (withProblem toDP')
  .>>> try removeInapplicable
  .>>> try cleanSuffix
  .>>> te removeHeads
  .>>> te (withProblem partIndep)
  .>>> try cleanSuffix
  .>>> try trivial
  .>>> try usableRules
  where
    toDP' prob
      | Prob.isInnermostProblem prob =
          timeoutIn 5 (dependencyPairs .>>> try usableRules .>>> wgOnTrs)
          .<|> dependencyTuples .>>> try usableRules
      | otherwise =
          dependencyPairs .>>> try usableRules .>>> try wgOnTrs

    partIndep prob
      | Prob.isInnermostProblem prob = decomposeIndependentSG
      | otherwise                    = linearPathAnalysis

    wgOnTrs = withProblem $ \ prob ->
      if RS.null (Prob.strictTrs prob)
        then identity
        else wgOnUsable 1 1 .<||> wgOnUsable 2 1

trivialDP =
  dependencyTuples
  .>>> try usableRules
  .>>> try trivial
  .>>> try dpsimps
  .>>> tew (wg 1 0 .<||> mx 1 0)

withCWDG s = withProblem $ \ prob -> s (Prob.congruenceGraph prob)


--- ** interpretations  ----------------------------------------------------------------------------------------------------------

interp = try trivial
  .>>> tew (try $ fastest [ax 1 1, mx 1 1, px 1])
  .>>> tew (try $ fastest [ax 2 2, px 2])
  .>>> tew (try $ fastest [mx 3 3, px 3])
  .>>> tew (try $ fastest [mxs1 .>>> tew mxs2 .>>> tew mxs3 .>>> tew mxs4])
  .>>> empty

  where
    mxs1 = mxsida 2 1 .<||> mxsida 3 1
    mxs2 = mxsida 2 2 .<||> mxsida 3 2 .<||> wg 2 2
    mxs3 = mxsida 3 3 .<||> mxsida 4 3
    mxs4 = mxsida 4 4


-- | Is now included in interp function

-- interpretations =
--   tew (?timeoutRel 15 $ mx 1 1 .<||> px 1)
--   .>>>
--   fastest
--     [ tew (px 3) .>>> empty
--     , tew (?timeoutRel 15 mxs1) .>>> tew (?timeoutRel 15 mxs2) .>>> tew mxs3 .>>> tew mxs4 .>>> empty
--     ]
--   where
--     mxs1 = mxsida 2 1 .<||> mxsida 3 1
--     mxs2 = mxsida 2 2 .<||> mxsida 3 2 .<||> wg 2 2
--     mxs3 = mxsida 3 3 .<||> mxsida 4 3
--     mxs4 = mxsida 4 4


--- ** raml ----------------------------------------------------------------------------------------------------------

toDP = dependencyTuples .<||> (dependencyPairs .>>> try usableRules .>>> try (wgOnUsable 2 1))
  .>>> try removeInapplicable
  .>>> try dpsimps

simpDP = try cleanSuffix
  .>>> te decomposeIndependentSG
  .>>> te removeHeads
  .>>> try trivial
  .>>> try usableRules

data Methods = PopStar | Matrices | Polys

-- semantic methods i = whenNonTrivial $
--   -- (when (PopStar `elem` methods) (peAny (spopstarPS `withDegree` Just i)))
--   -- <||>
--   (when (Matrices `elem` methods)
--    (peAny (mx i i)
--     .<||> peAny (mx (i + 1) i)
--     .<||> when (i == 1) (mx 3 1))
--     .<||> when (Polys `elem` methods && (i == 2 || i == 3))
--     (peAny (poly `withDegree` Just i)))

--   where peAny p = p `withPEOn`
--           (selLeafWDG `selInter` selStricts) >>> try cleanUpTail


raml =  dependencyTuples
  .>>>  try dpsimps
  .>>>  tew decomposeDG'
  .>||> try dpsimps
  .>>>  tew basics' .>>> empty


basics' =
       tew (try $ ?timeoutRel 15 $ fastest [mx 1 1, wg 1 1])
  .>>> tew (try $ ?timeoutRel 15 $ fastest [ax 2 2, eda2])
  .>>> tew (try $ ?timeoutRel 15 $ fastest [eda3])
  .>>> tew (try $                  fastest [ida4])
  .>>> tew (try $                  fastest [ida5])

 where
    -- eda1 = mxseda 1
    eda2 = mxseda 2
    eda3 = mxseda 3
    eda4 = mxseda 4
    ida4 = mxsida 4 1 .<||> mxsida 4 2 .<||> mxsida 4 3
    ida5 = mxsida 5 1 .<||> mxsida 5 2 .<||> mxsida 5 3 .<||> mxsida 5 4

--- ** rci ----------------------------------------------------------------------------------------------------------

rci =
  try innermostRuleRemoval
  .>>! ?combine
    [ timeoutIn 7 $ trivialDP .>>> empty
    , timeoutIn 7 $ matchbounds .>>> empty
    , withDP .>>!! dpi .>>> empty
    ]
  where

dpi =
  tew (withCWDG trans) .>>> basics
  where
    trans cwdg
      | cwdgDepth cwdg == (0::Int) = shiftLeafs
      | otherwise                  = ?timeoutRel 25 shiftLeafs .<|> removeFirstCongruence

    cwdgDepth cwdg = maximum $ 0 : [ dp r | r <- DG.roots cwdg]
      where dp n = maximum $ 0 : [ 1 + dp m | m <- DG.successors cwdg n]

    shiftLeafs = force $ removeLeafs 0 .<||> (removeLeafs 1 .<|> removeLeafs 2)

    removeLeafs 0 = force $ tew $ removeLeaf (mxCP 1 0)
    removeLeafs i =
      removeLeaf (mxCP i i)
      .<||> removeLeaf (mxCP (i+1) i)
      .<||> when' (i == 1) (removeLeaf (mxCP 3 1))
      .<||> when' (i == 2) (removeLeaf (pxCP 2))

    removeFirstCongruence = decomposeDG decomposeDGselect (Just proc) Nothing .>>! try simps
      where proc = try simps .>>> tew shiftLeafs .>>> basics .>>> empty

    basics = tew shift
      -- uncomment following line for script.sh
      where shift =
              fastest [ ax 1 1 .<||> mx 1 1 .<||> px 1 .<||>
                        ax 2 2 .<||> mx 2 2 .<||> px 2 .<||>
                        mx 3 3 .<||> px 3 .<||> -- ax 3 3 .<||>
                        mx 4 4
                      ]

    simps =
      try empty
      .>>> cleanSuffix
      .>>! try trivial
      .>>> try usableRules

when' b st = if b then st else abort

--- ** rc ------------------------------------------------------------------------------------------------------------

rc =
  ?combine
    [ timeoutIn 7 $ trivialDP .>>> empty
    , timeoutIn 7 $ matchbounds .>>> empty
    , ?combine
        [ interp .>>> empty
        , withDP .>>!! dp .>>> empty ]
    ]
  where

  dp = withProblem $ loopFrom 1
    where
      loopFrom i prob
        | RS.null (Prob.strictTrs prob) = dpi
        | otherwise                      = tew (is i) .>>! withProblem (loopFrom $ succ i)
      is i =
        let ?sel = Just selAnyRule in
        mx i i
        .<||> wg i i
        .<||> when' (i == 2 || i == 3) (px i)
        .<||> when' (i < 4) (mx (succ i) i .<||> wg (succ i) i)

