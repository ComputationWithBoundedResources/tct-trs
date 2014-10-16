module Tct.Common.Ring 
  (
    module Tct.Common.SemiRing
  , AdditiveGroup (..)
  , Ring 
  ) where

import Tct.Common.SemiRing

-- | Extends 'Additive' to a additive group with inverse elements.
class Additive a => AdditiveGroup a where
  neg :: a -> a

-- | 'Ring' instances should satisfy the 'SemiRing' laws:
-- Additionally:
--
-- * @'neg' a@ defines the inversible element of a
--
--    prop> a `add` neg a = zero
type Ring a = (AdditiveGroup a, Multiplicative a)

instance AdditiveGroup Int where
  neg = negate

