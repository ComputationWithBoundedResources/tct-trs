-- | This module provides an interface to \complexity pair combinators\.
-- A complexity pair is a special subset of processors that return a complexity pair proof.
-- A complexity pair combinator is a processor that takes a complexity pair as argument.
module Tct.Trs.Data.ComplexityPair where

import           Data.Typeable

import qualified Tct.Core.Data             as T

import           Tct.Trs.Data.Problem
import           Tct.Trs.Data.RuleSelector (ExpressionSelector)
import           Tct.Trs.Data.Trs          (Trs)


data ComplexityPairProof = ComplexityPairProof
  { result       :: T.ProofTree TrsProblem
  , removableDPs :: Trs F V
  , removableTrs :: Trs F V }
  deriving Show

-- | A 'ComplexityPair' provides a special solve method returning a 'ComplexityProof'.
class IsComplexityPair p where
  solveComplexityPair :: p -> ExpressionSelector F V -> Problem F V -> T.TctM (T.Return ComplexityPairProof)

-- | A 'ComplexityPair' is a processor that can returns 'ComplexityPairProof'.
data ComplexityPair where
  ComplexityPair :: (T.Processor p, IsComplexityPair p) => p -> ComplexityPair
  deriving Typeable

instance Show ComplexityPair where
  show (ComplexityPair p) = show p

-- | Existential type for declarations specifying a Strategy.
data ComplexityPairDeclaration where
  CD :: (TrsProblem ~ prob, T.ParsableArgs prob args, T.ArgsInfo args) => 
    T.Declaration (args T.:-> ComplexityPair) -> ComplexityPairDeclaration

