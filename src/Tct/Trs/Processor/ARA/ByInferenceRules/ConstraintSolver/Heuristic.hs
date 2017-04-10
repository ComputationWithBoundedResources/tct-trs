
module Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.Heuristic where

import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerDatatype.Type


data Heuristic dt = Shift dt   -- shift
  | Diamond dt                  -- first element
  | Interleaving dt dt          -- interleaving
  | Zero                        -- representing 0
  deriving (Show)


instance Functor Heuristic where
  fmap f (Shift dt)             = Shift (f dt)
  fmap f (Diamond dt)           = Diamond (f dt)
  fmap f (Interleaving dt1 dt2)=Interleaving (f dt1) (f dt2)
  fmap _ Zero                   = Zero

