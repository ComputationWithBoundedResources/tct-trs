-- | This module provides the default "derivation" complexity strategy.
module Tct.Trs.Strategy.Derivational
  ( derivational
  , derivationalDeclaration
  ) where

import qualified Data.Set               as S (fold)

import           Tct.Core
import qualified Tct.Core.Data          as T

import           Tct.Trs.Data.Problem   (signature, trsComponents)
-- import           Tct.Trs.Data.RuleSelector (selAllOf, selStricts)
import           Tct.Trs.Data
import           Tct.Trs.Data.Signature (arity, symbols)
import qualified Tct.Trs.Data.Rules as RS
import           Tct.Trs.Processors
import           Tct.Trs.Processor.Matrix.MI (triangular')

-- MS:
-- decomposition after shifting does not work (as composition basically searches for an interpretation)
-- matchbounds sometimes/rarely applies after shifting rules to the weak component or after decomposition
-- SRS benefit from higher constants

-- | Declaration for "derivational" strategy.
derivationalDeclaration :: T.Declaration ('[] T.:-> TrsStrategy)
derivationalDeclaration = strategy "derivational" () dcfast

-- | Default strategy for derivational complexity.
derivational :: TrsStrategy
derivational = T.deflFun derivationalDeclaration


dcfast :: TrsStrategy
dcfast =
  fastest'
    [ timeoutIn 20 matchbounds
    , whenSRS $ timeoutIn 5 $ withMini (mx' 1 1)
    , alternative [ timeoutIn 5 (mx' i i) | i <- [1.. ideg] ]
    , interpretations .>>! basics
    , composition ]
  where
  withMini = withKvPair ("solver", ["minismt", "-m", "-v2", "-neg", "-ib", "8", "-ob", "10"])
  fastest' = fastest . fmap (.>>> close)
  -- best'    = best cmpTimeUB . fmap (.>>> close)

  ideg     = 4
  mdeg     = 6

  basics          = fastest $ timeoutIn 5 matchbounds : [ mx' d d | d <- [succ ideg .. mdeg] ]
  interpretations = matrices 1 ideg
  composition     = compose .>>! fastest' [ interpretations .>>! basics , wait 3 composition ]


iteNonSizeIncreasing :: TrsStrategy -> TrsStrategy -> TrsStrategy
iteNonSizeIncreasing st1 st2 = withProblem $ \prob ->
  if RS.isNonSizeIncreasing (trsComponents prob) then st1 else st2

isSRS :: Trs -> Bool
isSRS prob = S.fold (\sym -> (arity sig sym == 1 &&)) True (symbols sig)
  where sig = signature prob

whenSRS :: TrsStrategy -> TrsStrategy
whenSRS st = withProblem $ \prob -> when (isSRS prob) st

compose :: TrsStrategy
compose = force $
  iteNonSizeIncreasing
    (mul 1 .<|> mul 2 .<|> (mul 3 .<||> mul 4))
    (com 1 .<|> com 2 .<|> (com 3 .<||> com 4))


type Dimension = Int

mx' :: Dimension -> Degree -> TrsStrategy
-- mx dim deg  = triangular' dim deg NoUArgs NoURules (Just selAny)
mx' dim deg = triangular' dim deg NoUArgs NoURules Nothing

mxCP :: Dimension -> Degree -> ComplexityPair
mxCP dim deg = matrixCP' dim deg Algebraic NoUArgs NoURules

mul, com :: Degree -> TrsStrategy
mul n = decomposeCP' selAny RelativeMul  (mxCP n n)
com n = decomposeCP' selAny RelativeComp (mxCP n n)


-- dc :: TrsStrategy
-- dc =
--   best cmpTimeUB
--     [ timeoutIn 20 matchbounds
--     , interpretation1
--     , composition1 ]

--   where

--   ideg = 4
--   bdeg = max ideg 6

--   ints = chain [ tew (mxs d) | d <- [1..ideg] ]

--   -- basics1 = fastest $ timeoutIn 10 matchbounds : [mx' i i | i <- [1..bdeg]]
--   basics2 = fastest [mx' i i | i <- [succ ideg..bdeg]]

--   interpretation1 = force ints    .>>! composition2
--   composition1    = force compose .>>> (interpretation2 .<||> composition2)

--   interpretation2 = try ints .>>! composition2
--   composition2    = iteProgress compose (interpretation2 .<||> composition2) basics2

-- wg :: Dimension -> Degree -> TrsStrategy
-- wg dim deg  = weightgap' dim deg Algebraic NoUArgs WgOnAny

-- iteSRS :: TrsStrategy -> TrsStrategy -> TrsStrategy
-- iteSRS st1 st2 = withProblem $ \prob ->
--   if isSRS prob then st1 else st2

-- mxs :: Degree -> TrsStrategy
-- mxs 1 = mx 1 1 .<||> mx 2 1 .<||> mx 3 1 .<||> wg 2 1 .<||> wg 1 1
-- mxs 2 = mx 2 2 .<||> mx 3 2 .<||> mx 4 2 .<||> wg 2 2
-- mxs 3 = mx 3 3 .<||> mx 4 3 .<||> wg 3 3
-- mxs 4 = mx 4 4 .<||> wg 4 4
-- mxs n
--   | n > 0     = mx n n
--   | otherwise = mx 1 1

