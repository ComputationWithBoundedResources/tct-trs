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

import           Tct.Core
import qualified Tct.Core.Data          as T

import           Tct.Trs.Data           (TrsStrategy)
import qualified Tct.Trs.Data.Problem   as Prob
import qualified Tct.Trs.Data.Signature as Sig
import qualified Tct.Trs.Data.Trs       as Trs
import           Tct.Trs.Processors


-- | Declaration for strategy "certify".
certifyDeclaration :: T.Declaration ('[Argument 'Optional T.Nat] T.:-> TrsStrategy)
certifyDeclaration = strategy "certify" (OneTuple $ degreeArg `optional` 5) certifyStrategy

-- | Default "certify" strategy.
certify :: TrsStrategy
certify = T.deflFun certifyDeclaration

-- | > certify = certify' 5
certify' :: Degree -> TrsStrategy
certify' = T.declFun certifyDeclaration

-- | Default strategy for certification with CeTA.
certifyStrategy :: Degree -> TrsStrategy
certifyStrategy deg = withProblem k where
  k prob
    | isRC && isIn = let ?ua = UArgs in certifyRCI deg
    | isRC         = let ?ua = NoUArgs in certifyRC deg
    | otherwise    = certifyDC deg
    where
      isRC = Prob.isRCProblem prob
      isIn = Prob.isInnermostProblem prob

matchbounds :: TrsStrategy
matchbounds = withProblem $ \prob ->
  when (Trs.isLeftLinear $ Prob.allComponents prob) (bounds PerSymbol Match)

shifts :: (?ua :: UsableArgs) => Degree -> Degree -> TrsStrategy
shifts l u = chain [ tew (intes d) | d <- [(max 0 l) .. u] ]

intes :: (?ua :: UsableArgs) => Degree -> TrsStrategy
intes 0 = px 0
intes 2 = mx 2 .<||> px 2
intes 3 = mx 3 .<||> px 3
intes n = mx n

px,mx :: (?ua :: UsableArgs) => Degree -> TrsStrategy
px d = poly' (Mixed d) NoRestrict ?ua URules (Just selAny) NoGreedy
mx d = matrix' d d Triangular ?ua URules (Just selAny) NoGreedy

top :: [TrsStrategy] -> TrsStrategy
top = best cmpTimeUB

certifyRC :: (?ua :: UsableArgs) => Int -> TrsStrategy
certifyRC deg =
  top
    [ timeoutIn 8 trivialRC
    , timeoutIn 8 matchbounds .<||> interpretations ]
  where

  interpretations =
    shifts 1 1
    .>>! fastest
      [ dependencyPairs' WDP .>>> try usableRules .>>> shifts 1 deg .>>> empty
      , ( force (shifts 2 2)
        .>>! fastest
          [ dependencyPairs' WDP .>>> try usableRules .>>> shifts 1 deg .>>> empty
          ,                                              shifts 3 deg .>>> empty ])

        .<|>

        shifts 3 deg .>>> empty
      ]
  trivialRC = shifts 0 0 .>>> dependencyPairs' WDP .>>> try usableRules .>>> shifts 0 0 .>>> empty


certifyRCI :: (?ua :: UsableArgs) => Degree -> TrsStrategy
certifyRCI deg =
  withProblem $ \p ->
  try innermostRuleRemoval
  .>>! top
    [ timeoutIn 8 trivialRCI
    , timeoutIn 8 matchbounds .<||> interpretations p ]

  where
    interpretations p =
      shifts 1 1
      .>>! fastest
        [ dt    .>>> try usableRules .>>> shifts 1 deg .>>> empty
        , wdp p .>>> try usableRules .>>> shifts 1 deg .>>> empty
        ,                                 shifts 2 deg .>>> empty ]

      .<|>

      shifts 1 1 .>>! force (shifts 2 2)
      .>>! fastest
        [ dt    .>>> try usableRules .>>> shifts 1 deg .>>> empty
        , wdp p .>>> try usableRules .>>> shifts 1 deg .>>> empty
        ,                                 shifts 3 deg .>>> empty ]

    dt = dependencyTuples
    wdp p1 = withProblem $ \p2 -> if Sig.defineds (Prob.signature p1) == Sig.defineds (Trs.signature (Prob.allComponents p2)) then dependencyPairs' WDP else abort
    trivialRCI = shifts 0 0 .>>> dependencyTuples .>>> try usableRules .>>> shifts 0 0 .>>> empty

certifyDC :: Degree -> TrsStrategy
certifyDC deg =
  try innermostRuleRemoval
  .>>! (matchbounds .<||> interpretations 1 deg)
  where
    interpretations l u = chain [ tew (mxAny d) | d <- [(max 0 l) .. (min u deg)] ]
    mxAny d = matrix' d d Triangular NoUArgs NoURules (Just selAny) NoGreedy
    -- mxAll d = matrix' d d Triangular NoUArgs NoURules (Just sel) NoGreedy

