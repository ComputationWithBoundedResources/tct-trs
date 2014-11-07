module Tct.Trs.Interpretation 
  ( interpretTerm )
  where

  
import Data.Rewriting.Term (Term (..))


-- | @interpret fun var term@ interprets @term@.
interpretTerm :: (fun -> [a] -> a) -> (var -> a) -> Term fun var -> a
interpretTerm ifun ivar (Fun f ts) = ifun f (interpretTerm ifun ivar `fmap` ts)
interpretTerm _    ivar (Var a)    = ivar a

