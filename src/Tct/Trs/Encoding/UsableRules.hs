{- | This module provides the encoding for \usable rules modulo argument filtering\. -}
{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Trs.Encoding.UsableRules
  ( usableRulesEncoding
  , validUsableRulesEncoding
  ) where


import           Control.Monad.Identity
import qualified Data.Foldable                  as F
import qualified Data.IntSet                    as IS
import qualified Data.Map.Strict                as M
import           Data.Maybe                     (fromMaybe)
import qualified Data.Set                       as S
import qualified Data.Traversable               as F

import qualified Data.Rewriting.Rule            as R
import qualified Data.Rewriting.Term            as R

import qualified Tct.Common.SMT                 as SMT

import           Tct.Trs.Data
import           Tct.Trs.Data.ArgumentFiltering
import qualified Tct.Trs.Data.Problem           as Prob
import qualified Tct.Trs.Data.Trs               as Trs
import qualified Tct.Trs.Data.Signature         as Sig


-- | @usableRulesEncoding prob allowUR allowAF@ returns @ m (usable, inFilter, usableEncoding, inFilterEncoding, validEncoding)@, where
--
-- * @usable rule@ and @inFilter fun pos@ denote predicates,
-- * @decode usableEncoding@ returns @Nothing@ if @allowUR == False@, otherwise @Just (Symbol f)@, ie the usable
-- symbols, and
-- * @decode inFilterEncoding @ returns @Nothing if @allowAR == False@, otherwise @Just (ArgumentFiltering f)@.
-- * add @validEncoding@ to the list of asserts
usableRulesEncoding :: (Ord v, Ord f) => Problem f v -> Bool -> Bool ->
  SMT.SolverStM SMT.Expr (R.Rule f v -> SMT.Expr, f -> Int -> SMT.Expr, Maybe (UsableEncoder f), Maybe (InFilterEncoder f), SMT.Expr)
usableRulesEncoding _    False   _       = return (const SMT.top, \_ _ -> SMT.top, Nothing, Nothing, SMT.top)
usableRulesEncoding prob allowUR allowAF = do
  usenc <- usableEncoder prob
  afenc <- argfilEncoder prob
  let
    usable'
      | allowUR && allowAF = usable prob usenc
      | otherwise          = const SMT.top
    inFilter' f i
      | allowAF   = inFilter afenc f i
      | otherwise = SMT.top
    validEncoding
      | allowUR   = validUsableRulesEncoding prob usable' inFilter'
      | otherwise = SMT.top
  return (usable', inFilter', if allowUR then Just usenc else Nothing  , if allowAF then Just afenc else Nothing, validEncoding)


-- | The actual encoding.
validUsableRulesEncoding :: (Ord f, Ord v) => Problem f v -> (R.Rule f v -> SMT.Expr) -> (f -> Int -> SMT.Expr) -> SMT.Expr
validUsableRulesEncoding prob usable' inFilter'
  | Prob.isDPProblem prob = memo $ SMT.bigAndM [ usableM r `SMT.impliesM` omega (R.rhs r) | r <- Trs.toList allRules ]
  | otherwise             = SMT.top
  where
    allRules = Prob.allComponents prob

    memo            = fst . runIdentity . SMT.memo
    usableM         = return . usable'
    unfilteredM f i = return $ inFilter' f i
    omega           = SMT.memoized $ \ t ->
      case t of
        R.Var _    -> return SMT.top
        R.Fun f ts ->
          SMT.bigAndM [ usableM rl | rl <- Trs.toList $ Trs.filter (\r -> R.root (R.lhs r) == Right f) allRules ]
          `SMT.bandM` SMT.bigAndM [ unfilteredM f i `SMT.impliesM` omega ti | (i,ti) <- zip [1..] ts]

--- * argument filtering ---------------------------------------------------------------------------------------------

data InFilterEncoder f = InFilterEncoder
  (ArgumentFiltering f)     -- ^ initial argument filtering
  (M.Map (f,Int) SMT.Expr)  -- ^ variable mapping

instance Ord f => SMT.Decode SMT.Environment (InFilterEncoder f) (ArgumentFiltering f) where
  decode (InFilterEncoder af m) = do
    fis :: S.Set (f,Int) <- SMT.decode (SMT.Property (fromMaybe False) m)
    return $ S.foldr insert af fis
    where
      insert (f,i) = alter (k i) f
      k i (Just (Filtering s)) = Just $ Filtering (IS.insert i s)
      k _ _ = error "Tct.Trs.Encoding.UsabalRules.ArgumentFilter.insert: the impossible happened."

-- | Sets the initial argumentfiltering. Provides a mapping for each @(symbol, position)@.
argfilEncoder :: Ord f => Problem f v -> SMT.SolverStM SMT.Expr (InFilterEncoder f)
argfilEncoder prob = InFilterEncoder initial `liftM` mapping
  where
    sig = Prob.signature prob
    initial = S.foldr (alter mkF) empty $ Sig.symbols sig
    mkF _   = Just (Filtering IS.empty)
    mapping = M.fromList `liftM` F.mapM mkM (concatMap mkV $ Sig.elems sig)
    mkV (f, i) = zip (repeat f) [1 .. i]
    mkM k = SMT.bvarM' >>= \v -> return (k,v)

-- | In filter mapping.
inFilter :: Ord f => InFilterEncoder f -> f -> Int -> SMT.Expr
inFilter (InFilterEncoder _ m) f i = SMT.top `fromMaybe` M.lookup (f,i) m



--- * usable rules ---------------------------------------------------------------------------------------------------

data UsableEncoder f = UsableEncoder
  (Symbols f)         -- ^ containts initial symbols
  (M.Map f SMT.Expr)  -- ^ maps functions symbol to variables

-- | Returns set of usable symbols.
instance Ord f => SMT.Decode SMT.Environment (UsableEncoder f) (Symbols f) where
  decode (UsableEncoder fs m) = do
    m1 :: S.Set f <- SMT.decode (SMT.Property (fromMaybe False) m)
    return $ fs `S.union` m1


-- | Lifts usable symbols to usable rules.
usable :: Ord f => Problem f v -> UsableEncoder f -> R.Rule f v -> SMT.Expr
usable prob (UsableEncoder _ m)
  | not (Prob.isDPProblem prob) = const SMT.top
  | otherwise                   = usable' . R.root . R.lhs
  where
    usable' (Right f) = SMT.top `fromMaybe` M.lookup f m
    usable' _         = SMT.top

-- | Sets the initial usable symbols. Provides a mapping from defined symbols to variables.
usableEncoder :: (Ord f, Ord v) => Problem f v -> SMT.SolverStM SMT.Expr (UsableEncoder f)
usableEncoder prob = UsableEncoder initialfs `liftM` mapping
  where
    mapping    = M.fromList `liftM` F.foldrM atom [] (defs `S.difference` initialfs)
    atom f acc = SMT.bvarM' >>= \v -> return ((f,v) :acc)
    defs       = Trs.definedSymbols (Prob.allComponents prob)
    initialfs =
      case Prob.startTerms prob of
        Prob.AllTerms fs -> fs
        st               -> Prob.defineds st

