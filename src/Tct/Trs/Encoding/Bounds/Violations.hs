{-# LANGUAGE BangPatterns #-}

----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Processor.Bounds.Violations
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>,
--                Georg Moser <georg.moser@uibk.ac.at>,
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>,
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable
--
-- This module implements constructs automata compatible with enriched systems,
-- as employed in the bound processor.
----------------------------------------------------------------------------------

module Tct.Trs.Encoding.Bounds.Violations where

import qualified Data.Set                                as S

import qualified Data.Rewriting.Rule                     as R

import qualified Tct.Trs.Data.Rules                      as RS
import           Tct.Trs.Encoding.Bounds.Automata
import           Tct.Trs.Encoding.Bounds.Violations.Find
import           Tct.Trs.Encoding.Bounds.Violations.Fix


makeRuleCompatible :: Ord v => R.Rule Symbol v -> Enrichment -> Strictness -> WeakBoundedness -> Label -> Automaton -> Either Automaton Automaton
makeRuleCompatible r !e !str !wb !ml !a
  | null violations = Right a
  | otherwise       = Left $ foldl fixViolation a violations
  where violations = S.toList $ findViolations a e str wb ml r

compatibleAutomaton :: Ord v => RS.Rules Symbol v -> RS.Rules Symbol v -> Enrichment -> Automaton -> Automaton
compatibleAutomaton strict weak e a = eitherVal (iter a (1 :: Int))
  where
    iter a' !i = case r of
      Left  a'' -> iter a'' (i + 1)
      Right a'' -> Right a''
      where r = let r' = foldl (f WeakRule (maxlabel a')) (Right a') wrs in foldl (f StrictRule (maxlabel a')) r' srs

    f str ml a' rule = case a' of
      (Left a'')  -> Left . eitherVal $ makeRuleCompatible rule e str wb ml a''
      (Right a'') -> makeRuleCompatible rule e str wb ml a''

    eitherVal (Left v)  = v
    eitherVal (Right v) = v
    srs = RS.toList strict
    wrs = RS.toList weak
    wb = if RS.isCollapsing strict then WeakMayExceedBound else WeakMayNotExceedBound

