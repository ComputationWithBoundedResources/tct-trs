-- This module contains some useful functions (yet) not available in rewriting library
module Tct.Trs.Data.Rewriting where


import           Control.Applicative
import           Control.Arrow               ((&&&))
import           Control.Monad.State.Strict
import           Data.Maybe
import qualified Data.Set                    as S
import           Data.Traversable            as F

import           Data.Rewriting.CriticalPair (CP (..))
import qualified Data.Rewriting.CriticalPair as R
import           Data.Rewriting.Rule         (Rule)
import qualified Data.Rewriting.Rule         as R
import qualified Data.Rewriting.Rules        as RS
import qualified Data.Rewriting.Substitution as S
import           Data.Rewriting.Term         (Term (..))
import qualified Data.Rewriting.Term         as T


tvars :: Ord v => Term f v -> S.Set v
tvars = S.fromList . T.vars

rvars :: Ord v => Rule f v -> S.Set v
rvars = S.fromList . R.vars

tmapM :: Applicative m => (f -> m f') -> (v -> m v') -> Term f v -> m (Term f' v')
tmapM _ g (T.Var v)    = T.Var <$> g v
tmapM f g (T.Fun t ts) = T.Fun <$> f t <*> F.traverse (tmapM f g) ts

rmap :: (Term f v -> Term f' v') -> Rule f v -> Rule f' v'
rmap f (R.Rule lhs rhs) = R.Rule (f lhs) (f rhs)

rmapM :: Applicative m => (Term f v  -> m (Term f' v')) -> Rule f v -> m (Rule f' v')
rmapM f (R.Rule lhs rhs) = R.Rule <$> f lhs <*> f rhs

-- | Returns the size of the term.
size :: Term f v -> Int
size = T.fold (const 1) (\_ xs -> 1 + sum xs)

-- | Variant of unify that renames terms using Either.
unifyE :: (Ord v1, Ord v2, Eq f) => T.Term f v1 -> T.Term f v2 -> Maybe (S.Subst f (Either v1 v2))
unifyE t1 t2 = S.unify (T.rename Left t1) (T.rename Right t2)

-- | Checks wether the given terms are unifable.
isUnifiable :: (Ord v1, Ord v2, Eq f) => T.Term f v1 -> T.Term f v2 -> Bool
isUnifiable t = isJust . unifyE t

-- | Checks wether the given rule is non-erasing, ie. all variables occuring in the left hand side also occur in the
-- right hand side.
isNonErasing :: Ord v => Rule f v -> Bool
isNonErasing (R.Rule l r) = varsS l == varsS r
  where varsS = S.fromList . T.vars

directSubterms :: Term f v -> [Term f v]
directSubterms (R.Var _)    = []
directSubterms (R.Fun _ ts) = ts

--isSizeIncreasing :: Ord v => Rule f v -> Bool
--isSizeIncreasing rule@(Rule l r) = size r > size l && isNonErasing rule

-- | prop> isNonDuplicating = not . R.isDuplicating
isNonDuplicating :: Ord v => Rule f v -> Bool
isNonDuplicating = not . R.isDuplicating

-- | Checks wether the given rule non-size increasing, ie. the size of the lhs is at least the size of the rhs and the
-- rule is not duplicating.
isNonSizeIncreasing :: Ord v => Rule f v -> Bool
isNonSizeIncreasing rule@(R.Rule l r) = size l >= size r && isNonDuplicating rule

invertRule :: Rule f v -> Rule f v
invertRule (R.Rule l r) = R.Rule r l

-- TODO: check
mutualCriticalPairs :: (Eq f, Ord v) => [Rule f v] -> [Rule f v] -> [R.CP f v v]
mutualCriticalPairs r s = R.cps r s ++ R.cps s r

forwardPairs :: (Eq f, Ord v) => [Rule f v] -> [Rule f v] -> [CP f v v]
forwardPairs r = mutualCriticalPairs (map invertRule r)

toPairs :: [CP f v v] -> [(Term f (Either v v), Term f (Either v v))]
toPairs = map (left &&& right)

rewrite :: (Ord v', Eq v, Eq f) => [Rule f v'] -> Term f v -> [Term f v]
rewrite trs = map RS.result . RS.fullRewrite trs

rewrites :: (Ord v', Eq v, Eq f) => [Rule f v'] -> [Term f v] -> [Term f v]
rewrites trs = concatMap (rewrite trs)


data Fresh v = Old v | Fresh Int deriving (Eq, Ord, Show)

freshVar :: State Int (T.Term f (Fresh v))
freshVar = T.Var . Fresh <$> (modify succ >> get)

-- tcap/icap
-- J. Giesl, R. Thieman, P.Schneiderkamp, Proving and Disproving Termination of Higher-Order Functions (Definition 11)
tcap :: (Ord v2, Ord v1, Eq f) => [Rule f v1] -> Term f (Fresh v2) -> Term f (Fresh v2)
tcap rs t = evalState (tcapM (RS.lhss rs) t) 0

icap :: (Ord v2, Ord v1, Eq f) => [Rule f v1] -> Term f (Fresh v2) -> Term f (Fresh v2)
icap rs t = evalState (icapM (RS.lhss rs) t) 0

tcapM :: (Eq f, Ord v1, Ord v2) => [T.Term f v1] -> T.Term f (Fresh v2) -> State Int (T.Term f (Fresh v2))
tcapM _    (T.Var _)  = freshVar
tcapM lhss (T.Fun f ts) = do
  t <- T.Fun f <$> F.mapM (tcapM lhss) ts
  if any (isUnifiable t) lhss then freshVar else return t

icapM :: (Eq f, Ord v1, Ord v2) => [T.Term f v1] -> T.Term f (Fresh v2) -> State Int (T.Term f (Fresh v2))
icapM _    t@(T.Var _)  = return t
icapM lhss (T.Fun f ts) = do
  t <- T.Fun f <$> F.mapM (icapM lhss) ts
  if any (isUnifiable t) lhss then freshVar else return t

-- generalisation of tcap/icap to generalised q restricted rewriting
-- R.Thiemann, Dissertation (Definition 3.11, ICap)
-- FIXME
-- qcapM :: (Ord f, Ord v1, Ord v2)
--   => [R.Term f v1] -> [R.Term f v1]
--   -> [R.Term f (Fresh v2)] -> R.Term f (Fresh v2) -> State Int (R.Term f (Fresh v2))
-- qcapM rsLhss qsLhss ss = qcapM'
--   where
--     allqnf = S.fromList rsLhss `S.isSubsetOf` S.fromList qsLhss
--
--     rsLhss' = map (T.rename Right) rsLhss
--     ss'     = map (T.rename Left) ss
--
--     qcapM' t@(R.Var v)
--       | allqnf && any ((v `elem`) . T.vars) ss = return t
--       | otherwise                              = freshVar
--     qcapM' (R.Fun f ts) = do
--       t' <- R.Fun f <$> mapM qcapM' ts
--       let mgus = catMaybes [ (,) l `liftM` S.unify (T.rename Left t') l | l <- rsLhss' ]
--       if and [ any (not . isQNF) [ S.apply delta s | s <- ss' ++ directSubterms l ] | (l,delta) <- mgus ]
--         then return t'
--         else freshVar
--
--     isQNF t = all isNothing [ t `S.match` q | q <- qsLhss ]
--
