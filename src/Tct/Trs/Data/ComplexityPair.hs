-- | This module provides an interface to \complexity pair combinators\.
-- A complexity pair is a special subset of processors that return a complexity pair proof.
-- A complexity pair combinator is a processor that takes a complexity pair as argument.
module Tct.Trs.Data.ComplexityPair
  (
    ComplexityPair (..)
  , ComplexityPairDeclaration (..)
  , IsComplexityPair (..)
  , ComplexityPairProof (..)

  , toComplexityPair
  , someComplexityPair
  ) where


import           Data.Typeable

import qualified Tct.Core.Data             as T

import           Tct.Trs.Data.Problem
import           Tct.Trs.Data.RuleSelector (ExpressionSelector)
import           Tct.Trs.Data.Trs          (Trs)
import           Tct.Trs.Data.Symbol       (F, V)


data ComplexityPairProof = ComplexityPairProof
  { result       :: T.ProofTree TrsProblem
  , removableDPs :: Trs F V
  , removableTrs :: Trs F V }
  deriving Show

-- MS: TODO: a complexity pair should just return a proof tree
-- then lift it here

-- | A 'ComplexityPair' provides a special solve method returning a 'ComplexityProof'.
class IsComplexityPair p where
  solveComplexityPair :: p -> ExpressionSelector F V -> Problem F V -> T.TctM (Either String ComplexityPairProof)

-- | A 'ComplexityPair' is a processor that can returns 'ComplexityPairProof'.
data ComplexityPair where
  ComplexityPair :: (T.Processor p, IsComplexityPair p) => p -> ComplexityPair
  deriving Typeable

instance Show ComplexityPair where
  show (ComplexityPair p) = show p

-- | Existential type for declarations specifying a Strategy.
data ComplexityPairDeclaration where
  CD :: (TrsProblem ~ prob, T.ParsableArgs args, T.ArgsInfo args) =>
    T.Declaration (args T.:-> ComplexityPair) -> ComplexityPairDeclaration

someComplexityPair :: (TrsProblem ~ prob, T.ParsableArgs args, T.ArgsInfo args) =>
  T.Declaration (args T.:-> ComplexityPair) -> ComplexityPairDeclaration
someComplexityPair = CD

toComplexityPair :: (T.Processor p, IsComplexityPair p) => p -> ComplexityPair
toComplexityPair = ComplexityPair

