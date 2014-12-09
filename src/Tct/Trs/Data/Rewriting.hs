-- This module contains some useful functions (yet) not available in rewriting library
module Tct.Trs.Data.Rewriting where

import           Control.Arrow               ((&&&))
import qualified Data.Set                    as S

import           Data.Rewriting.CriticalPair (CP (..))
import qualified Data.Rewriting.CriticalPair as R
import           Data.Rewriting.Rule         (Rule (..))
import qualified Data.Rewriting.Rule         as R
import qualified Data.Rewriting.Rules        as R (fullRewrite, result)
import           Data.Rewriting.Term         (Term (..))
import qualified Data.Rewriting.Term         as T

-- | Returns the size of the term.
size :: Term f v -> Int
size = T.fold (const 1) (\_ xs -> 1 + sum xs)

-- | Checks wether the given rule is non-erasing, ie. all variables occuring in the left hand side also occur in the
-- right hand side.
isNonErasing :: Ord v => Rule f v -> Bool
isNonErasing (Rule l r) = varsS l == varsS r
  where varsS = S.fromList . T.vars

--isSizeIncreasing :: Ord v => Rule f v -> Bool
--isSizeIncreasing rule@(Rule l r) = size r > size l && isNonErasing rule

-- | prop> isNonDuplicating = not . R.isDuplicating
isNonDuplicating :: Ord v => Rule f v -> Bool
isNonDuplicating = not . R.isDuplicating

-- | Checks wether the given rule non-size increasing, ie. the size of the lhs is at least the size of the rhs and the
-- rule is not duplicating.
isNonSizeIncreasing :: Ord v => Rule f v -> Bool
isNonSizeIncreasing rule@(Rule l r) = size l >= size r && isNonDuplicating rule

invertRule :: Rule f v -> Rule f v
invertRule (Rule l r) = Rule r l

-- TODO: check
mutualCriticalPairs :: (Eq f, Ord v) => [Rule f v] -> [Rule f v] -> [R.CP f v v]
mutualCriticalPairs r s = R.cps r s ++ R.cps s r

forwardPairs :: (Eq f, Ord v) => [Rule f v] -> [Rule f v] -> [CP f v v]
forwardPairs r = mutualCriticalPairs (map invertRule r)

toPairs :: [CP f v v] -> [(Term f (Either v v), Term f (Either v v))]
toPairs = map (left &&& right)

rewrite :: (Ord v', Eq v, Eq f) => [Rule f v'] -> Term f v -> [Term f v]
rewrite trs = map R.result . R.fullRewrite trs

rewrites :: (Ord v', Eq v, Eq f) => [Rule f v'] -> [Term f v] -> [Term f v]
rewrites trs = concatMap (rewrite trs)


