-- | This module provides addtional functionalities to the 'Data.Rewriting.Term' library.
module Tct.Trs.TermRewriting where


import Data.Maybe (fromMaybe)

import qualified Data.Rewriting.Term    as R (Term (..))


-- Rewrite / Transform -----------------------------------------------------------------------------------------------
-- inspired from uniplate library

-- | Bottom-up transformation.
transform :: (R.Term f v -> R.Term f v) -> R.Term f v -> R.Term f v
transform g (R.Fun f ts) = g (R.Fun f $ map (transform g) ts)
transform g v            = g v

-- | Composable bottom-up transformation using (f `mplus` g).
rewrite :: (R.Term f v -> Maybe (R.Term f v)) -> R.Term f v -> R.Term f v
rewrite f = transform g
  where g t = maybe t (rewrite f) (f t)

-- prop> rewrite r x = transform (always r) only if there are no overlaps
always :: (a -> Maybe a) -> a -> a
always r x = x `fromMaybe` r x

