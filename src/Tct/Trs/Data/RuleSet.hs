module Tct.Trs.Data.RuleSet where

import Tct.Trs.Data.Rules (Rules, empty)

-- * ruleset
data RuleSet f v = RuleSet
  { sdps :: Rules f v -- ^ strict dependency pairs
  , wdps :: Rules f v -- ^ weak dependency pairs
  , strs :: Rules f v -- ^ strict rules
  , wtrs :: Rules f v -- ^ weak rules
  }

emptyRuleSet :: RuleSet f v
emptyRuleSet = RuleSet empty empty empty empty

