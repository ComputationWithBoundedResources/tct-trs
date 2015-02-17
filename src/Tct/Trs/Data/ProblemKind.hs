module Tct.Trs.Data.ProblemKind where

import Tct.Trs.Data.Signature (Symbols)

data StartTerms f
  = AllTerms 
    { alls         :: Symbols f }
  | BasicTerms 
    { defineds     :: Symbols f
    , constructors :: Symbols f }
  deriving (Show, Eq)

data Strategy
  = Innermost
  | Outermost
  | Full
  deriving (Show, Eq)
