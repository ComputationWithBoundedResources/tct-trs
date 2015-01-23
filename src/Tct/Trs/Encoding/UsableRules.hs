{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Trs.Encoding.UsableRules
  ( validUsableRulesEncoding
    -- | Add this constraint for a valid SAT encoding.
  , usable
    -- | Propositional formula that holds if the given rule is usable.
  , usableEncoder
    -- | Initial left-hand side roots symbols of usable rules.
  ) where


import           Control.Monad.Identity
import qualified Data.Map.Strict        as M
import           Data.Maybe             (fromMaybe)
import qualified Data.Set               as S
import           Data.Traversable       as F

import qualified Data.Rewriting.Rule    as R
import qualified Data.Rewriting.Term    as R

import qualified Tct.Common.SMT         as SMT

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem   as Prob
import qualified Tct.Trs.Data.Trs       as Trs


data UsableEncoder f = UsableEncoder 
  (Symbols f)         -- ^ containts initial symbols
  (M.Map f SMT.Expr)  -- ^ maps functions symbol to variables
  deriving (Eq, Ord, Show)

encode :: Ord f => UsableEncoder f -> f -> SMT.Expr
encode (UsableEncoder _ e) f = SMT.top `fromMaybe` M.lookup f e

instance Ord f => SMT.Decode SMT.Environment (UsableEncoder f) (Symbols f) where
  decode (UsableEncoder fs m) = do
    m1 :: S.Set f <- SMT.decode m
    return $ fs `S.union` m1


usable :: Ord f => UsableEncoder f -> Problem f v -> R.Rule f v -> SMT.Expr
usable encoder prob
  | not (Prob.isDPProblem prob) = const SMT.top
  | otherwise                   = usable' . R.root . R.lhs
  where
    usable' (Right f) = encode encoder f
    usable' _         = SMT.top

usableEncoder :: Ord f => Problem f v -> SMT.SolverStM SMT.Expr (UsableEncoder f)
usableEncoder prob = UsableEncoder initialfs `liftM` mapping
  where
    mapping = M.fromList `liftM` F.mapM atom (S.toList $ allfs `S.difference` initialfs)
    atom f = SMT.bvarM' >>= \v -> return (f,v)
    allfs     = Trs.symbols (Prob.signature prob)
    initialfs =
      case Prob.startTerms prob of
        Prob.AllTerms fs -> fs
        st               -> Prob.defineds st

validUsableRulesEncoding :: (Ord f, Ord v) => UsableEncoder f -> Problem f v -> (f -> Int -> SMT.Expr) -> SMT.Expr
validUsableRulesEncoding encodeUsable prob encodeUnfiltered
  | Prob.isDPProblem prob = memo $ SMT.bigAndM [ usableM r `SMT.impliesM` omega (R.rhs r) | r <- Trs.toList allRules ]
  | otherwise             = SMT.top
  where
    allRules = Prob.allComponents prob

    memo            = fst . runIdentity . SMT.memo
    usableM         = return . usable encodeUsable prob
    unfilteredM f i = return $ encodeUnfiltered f i
    omega           = SMT.memoized $ \ t ->
      case t of
        R.Var _    -> return SMT.top
        R.Fun f ts ->
          SMT.bigAndM [ usableM rl | rl <- Trs.toList $ Trs.filter (\r -> R.root (R.lhs r) == Right f) allRules ]
          `SMT.bandM` SMT.bigAndM [ unfilteredM f i `SMT.impliesM` omega ti | (i,ti) <- zip [1..] ts]

