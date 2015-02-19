module Tct.Trs.Data.RuleSet where

import Tct.Trs.Data.Trs (Trs, empty)

-- * ruleset
data RuleSet f v = RuleSet
  { sdps :: Trs f v -- ^ strict dependency pairs                          
  , wdps :: Trs f v -- ^ weak dependency pairs
  , strs :: Trs f v -- ^ strict rules
  , wtrs :: Trs f v -- ^ weak rules
  }

emptyRuleSet :: RuleSet f v
emptyRuleSet = RuleSet empty empty empty empty

