module Tct.Trs.Interpretation 
  ( interpretTerm )
  where

  
import Tct.Trs (Var, Fun)
import Data.Rewriting.Term (Term (..))


-- | @interpret fun var term@ interprets @term@.
interpretTerm :: (Fun -> [a] -> a) -> (Var -> a) -> Term Fun Var -> a
interpretTerm ifun ivar (Fun f ts) = ifun f (interpretTerm ifun ivar `fmap` ts)
interpretTerm _    ivar (Var a)    = ivar a

