{-# LANGUAGE ImplicitParams            #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module provides a strategy for certification with \CeTA\.
-- All proofs produced should be certifiable.
--
-- Example calls (assumes the standard tct-trs executable).
--
-- > tct-trs s "withCertification certify" $file
-- > tct-trs -a s --ceta -s certify $file > $file.xml
module Tct.Trs.Strategy.Certify
  ( certify
  , certify'
  , certifyDeclaration
  ) where

import           Data.Foldable               (toList)

import           Tct.Core
import qualified Tct.Core.Data               as T

import           Tct.Trs.Data                (TrsStrategy)
import qualified Tct.Trs.Data.Problem        as Prob
import qualified Tct.Trs.Data.Rules          as RS
import qualified Tct.Trs.Data.Signature      as Sig
import           Tct.Trs.Processor.Matrix.MI
import           Tct.Trs.Processors          hiding (matchbounds)



-- | Declaration for strategy "certify".
certifyDeclaration :: T.Declaration ('[T.Argument 'Optional CombineWith, Argument 'Optional T.Nat] T.:-> TrsStrategy)
certifyDeclaration =
  strategy
    "certify"
    ( combineWithArg `optional` Fastest
    , degreeArg      `optional` 5)
    certifyStrategy

-- | Default "certify" strategy.
certify :: TrsStrategy
certify = T.deflFun certifyDeclaration

-- | > certify = certify' Fastest 5
certify' :: CombineWith -> Degree -> TrsStrategy
certify' = T.declFun certifyDeclaration

-- | Default strategy for certification with CeTA.
certifyStrategy :: CombineWith -> Degree -> TrsStrategy
certifyStrategy cmb deg = withProblem k where
  k prob
    | isRC && isIn = let ?ua = UArgs   in certifyRCI cmb deg
    | isRC         = let ?ua = NoUArgs in certifyRC  cmb deg
    | otherwise    = certifyDC cmb deg
    where
      isRC = Prob.isRCProblem prob
      isIn = Prob.isInnermostProblem prob

matchbounds :: TrsStrategy
matchbounds = withProblem $ \prob ->
  when (RS.isLeftLinear $ Prob.allComponents prob) (bounds PerSymbol Match .>>> empty)

shifts :: (?ua :: UsableArgs) => Degree -> Degree -> TrsStrategy
shifts l u = chain [ tew (intes d) | d <- [(max 0 l) .. u] ]

intes :: (?ua :: UsableArgs) => Degree -> TrsStrategy
intes 0 = px 0
intes 1 =            mx 1 1 .<||> mx 2 1 .<||> ma 2 1
intes 2 = px 2 .<||> mx 2 2 .<||> mx 3 2 .<||> ma 3 2
intes 3 = px 3 .<||> mx 3 3 .<||> ma 3 3
intes n =            mx n n

px :: (?ua :: UsableArgs) => Degree -> TrsStrategy
mx, ma :: (?ua :: UsableArgs) => Degree -> Degree -> TrsStrategy
px d = poly' (Mixed d) Restrict ?ua URules (Just selAny)
mx dim deg = matrix' dim deg (if deg < dim then Triangular else Algebraic) ?ua URules (Just selAny)
ma dim deg = T.processor MI
  { miKind      = MaximalMatrix (MaxAutomaton $ if deg < dim then Just deg else Nothing)
  , miDimension = dim
  , miUArgs     = ?ua
  , miURules    = URules
  , miSelector  = Just (selAny) }

combineWith :: CombineWith -> [TrsStrategy] -> TrsStrategy
combineWith Fastest sts = fastest        [ st .>>> empty | st <- sts ]
combineWith Best    sts = best cmpTimeUB [ st .>>> empty | st <- sts ]

certifyRC :: (?ua :: UsableArgs) => CombineWith -> Degree -> TrsStrategy
certifyRC cmb deg =
  combineWith cmb
    [ timeoutIn 8 trivialRC
    , timeoutIn 8 matchbounds .<||> interpretations ]
  where

  trivialRC = shifts 0 0 .>>> dependencyPairs' WDP .>>> try usableRules .>>> shifts 0 0 .>>> empty

  interpretations =
    shifts 1 1
    .>>! combineWith cmb
      [ dependencyPairs' WDP .>>> try usableRules .>>> shifts 1 deg
      ,                                           .>>> shifts 2 deg
      , force (shifts 2 2)
        .>>! combineWith cmb
          [ dependencyPairs' WDP .>>> try usableRules .>>> shifts 1 deg
          ,                                                shifts 3 deg ]
      ]

certifyRCI :: (?ua :: UsableArgs) => CombineWith -> Degree -> TrsStrategy
certifyRCI cmb deg =
  withProblem $ \p ->
  try innermostRuleRemoval
  .>>! combineWith cmb
    [ timeoutIn 8 trivialRCI
    , timeoutIn 8 matchbounds .<||> interpretations ]
  where

    trivialRCI = shifts 0 0 .>>> dependencyTuples .>>> try usableRules .>>> shifts 0 0

    interpretations p =
      shifts 1 1
      .>>!
        alternative
          [ combineWith cmb
            [ dt    .>>> try usableRules .>>> shifts 1 deg
            , wdp p .>>> try usableRules .>>> shifts 1 deg
            ,                                 shifts 2 deg ]
          , force (shifts 2 2)
            .>>! combineWith cmb
              [ dt    .>>> try usableRules .>>> shifts 1 deg
              , wdp p .>>> try usableRules .>>> shifts 1 deg
              ,                                 shifts 3 deg ] ]

    dt = dependencyTuples
    wdp p1 = withProblem $ \p2 ->
      if Sig.defineds (Prob.signature p1) == Sig.defineds (RS.signature (Prob.allComponents p2))
        then dependencyPairs' WDP
        else abort

certifyDC :: CombineWith -> Degree -> TrsStrategy
certifyDC cmb degree =
  try innermostRuleRemoval
  .>>! combineWith cmb
    [ matchbounds
    , srs
    , interpretations degree mxf
    , interpretations degree mxs ]
  where

    isSRS prob = all (\sym -> Sig.arity sig sym == 1) (toList $ Sig.symbols sig) where sig = Prob.signature prob
    whenSRS st = withProblem $ \prob -> when (isSRS prob) st

    withMini :: Int -> Int -> TrsStrategy -> TrsStrategy
    withMini ib ob = withKvPair ("solver", ["minismt", "-m", "-v2", "-neg", "-ib", show ib, "-ob", show ob])

    mi dim kind =
      T.processor MI
        { miKind      = kind
        , miDimension = dim
        , miUArgs     = NoUArgs
        , miURules    = NoURules
        , miSelector  = Just (selAny) }

    mxu dim deg = mi dim $ MaximalMatrix (UpperTriangular $ Multiplicity $ if deg < dim then Just deg else Nothing)
    mxl dim deg = mi dim $ MaximalMatrix (LowerTriangular $ Multiplicity $ if deg < dim then Just deg else Nothing)
    mxa dim deg = mi dim $ MaximalMatrix (MaxAutomaton                   $ if deg < dim then Just deg else Nothing)

    interpretations u st = chain [ tew (st n) | n <- [1 .. min u degree] ]

    -- SRS strategy
    -- try low  dimension with high bits
    -- try high dimension with low  bits
    srs = whenSRS $ fastest
      [ withMini 8 10  (tew (mxu 1 1))                                 .>>> empty
      , chain [ tew (withMini 1 2 $ mxf n) | n <- [1.. min 4 degree] ] .>>> empty ]

    -- fast strategy
    -- rule shifting using triangular and EDA with implicit bounds
    mxf :: Int -> TrsStrategy
    mxf 0 = mxu 1 1
    mxf 1 = mxu 1 1
    mxf 2 = mxu 2 2 .<||> mxl 2 2
    mxf 3 = mxu 3 3 .<||> mxa 3 3 .<||> withMini 1 2 (mxu 3 3 .<||> mxa 3 3 )
    mxf n = withMini 1 2 (mxu n n .<||> mxa n n )

    -- precise strategy
    -- strategy with increasing bound
    mxs :: Int -> TrsStrategy
    mxs 0 = mxu 1 1
    mxs 1 = mxu 1 1 .<||> mxu 2 1 .<||> mxl 2 1 .<||> mxu 3 1 .<||> mxa 3 1
    mxs 2 = mxu 2 2 .<||> mxl 2 2 .<||> mxu 3 2 .<||> mxa 3 2
    mxs 3 = mxu 3 3 .<||> mxl 3 3 .<||> mxu 4 3 .<||> mxa 4 3 .<||> withMini 1 2 (mxu 4 3 .<||> mxa 4 3)
    mxs n = withMini 1 2 $              mxu n n .<||> mxa n n

