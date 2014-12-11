{-# LANGUAGE GADTs #-}
-- | This module provides a dedicated processor for partialproofs.
module Tct.Trs.Data.PartialProcessor where

import qualified Tct.Core.Data        as T

import           Control.Monad.Error  (catchError)

import           Tct.Trs.Data.Problem
import           Tct.Trs.Data.Trs


data PartialProof = PartialProof
  { ppInputProblem :: Problem
  , ppProcName     :: String
  , ppResult       :: T.Return (T.ProofTree Problem)
  , ppRemovableDPs :: Trs
  , ppRemovableTrs :: Trs }
  deriving Show

-- | PartialProcessor extends 'Processor' with an addtional function resulting in a 'PartialProof'.
class (T.Processor p, T.Problem p ~ Problem)  => PartialProcessor p where
  solvePartial :: SelectorExpression -> p -> Problem -> T.TctM PartialProof

-- | A PartialStrategy is a non-composable 'Strategy' taking only a 'PartialProcessor'.
data PartialStrategy where
  PartialProc :: PartialProcessor p => p -> PartialStrategy

instance Show PartialStrategy where
  show (PartialProc p) = show p

instance PartialProcessor p => PartialProcessor (T.ErroneousProcessor p) where
  solvePartial _ e@(T.ErroneousProc err p) prob = do
    let ret = T.resultToTree e prob (T.Fail (T.ErroneousProof err p))
    return PartialProof
      { ppInputProblem = prob
      , ppProcName     = show e
      , ppResult       = ret
      , ppRemovableDPs = empty
      , ppRemovableTrs = empty }

evaluatePartial :: SelectorExpression -> PartialStrategy -> Problem -> T.TctM PartialProof
evaluatePartial rs (PartialProc p) prob = solvePartial rs p prob `catchError` errNode
  where errNode err = evaluatePartial rs (PartialProc (T.ErroneousProc err p)) prob

progressPartial :: PartialProof -> Bool
progressPartial pp = not (isEmpty $ ppRemovableDPs pp)  || not (isEmpty $ ppRemovableTrs pp)

