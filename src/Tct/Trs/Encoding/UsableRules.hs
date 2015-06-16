{-# LANGUAGE ScopedTypeVariables #-}
{- | This module provides the encoding for \usable rules modulo argument filtering\. -}
module Tct.Trs.Encoding.UsableRules
  ( UsableEncoder
  , UsableSymbols (..)
  , usableEncoder
  , usable
  , validUsableRules
  ) where


import Data.Traversable as F
import           Control.Monad.Identity
import qualified Data.Map.Strict                as M
import           Data.Maybe                     (fromMaybe)
import qualified Data.Set                       as S

import qualified Data.Rewriting.Rule            as R
import qualified Data.Rewriting.Term            as R

import qualified Tct.Core.Common.Pretty         as PP

import qualified Tct.Common.SMT                 as SMT

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem           as Prob
import qualified Tct.Trs.Data.ProblemKind       as Prob
import qualified Tct.Trs.Data.Trs               as Trs
import qualified Tct.Trs.Data.Signature         as Sig


--- * usable rules ---------------------------------------------------------------------------------------------------

data UsableEncoder f w = UsableEncoder
  (Symbols f)         -- ^ containts initial symbols
  (M.Map f (SMT.Formula w))  -- ^ maps functions symbol to variables

newtype UsableSymbols f = UsableSymbols { runUsableSymbols :: Symbols f }

-- | Returns set of usable symbols.
instance (Ord f, SMT.Storing w) => SMT.Decode (SMT.Environment w) (UsableEncoder f w) (UsableSymbols f) where
  decode (UsableEncoder fs m) = do
    m1 :: S.Set f <- SMT.decode (SMT.Property (fromMaybe False) m)
    return . UsableSymbols $ fs `S.union` m1

instance PP.Pretty f => PP.Pretty (UsableSymbols f) where
  pretty = PP.set . map PP.pretty . S.toList . runUsableSymbols

-- | Provides a mapping from defined symbols to variables.
usableEncoder :: (SMT.Fresh w, Ord f) => Problem f v -> SMT.SmtSolverSt w (UsableEncoder f w)
usableEncoder prob = UsableEncoder initialfs `liftM` mapping
  where
    mapping = M.fromAscList `liftM` F.mapM atom (S.toAscList $ defs `S.difference` initialfs)
    atom f  = SMT.bvarM' >>= \v -> return (f,v)
    defs    = Sig.defineds (Prob.signature prob)
    initialfs =
      case Prob.startTerms prob of
        Prob.AllTerms fs -> fs
        st               -> Prob.defineds st

-- | Lifts usable symbols to usable rules.
usable :: Ord f => UsableEncoder f w -> R.Rule f v -> (SMT.Formula w)
usable (UsableEncoder _ m) = usable' . R.root . R.lhs
  where
    usable' (Right f) = SMT.top `fromMaybe` M.lookup f m
    usable' _         = SMT.top

-- | The actual encoding.
validUsableRules :: (Ord f, Ord v) => Trs f v -> (R.Rule f v -> SMT.Formula w) -> (f -> Int -> SMT.Formula w) -> SMT.Formula w
validUsableRules trs usable' inFilter' =
  memo $ SMT.bigAndM [ usableM r `SMT.impliesM` omega (R.rhs r) | r <- Trs.toList trs ]
  where
    memo          = fst . runIdentity . SMT.memo
    usableM       = return . usable'
    inFilterM f i = return $ inFilter' f i
    omega         = SMT.memoized $ \ t ->
      case t of
        R.Var _    -> return SMT.top
        R.Fun f ts ->
          SMT.bigAndM [ usableM rl | rl <- Trs.toList $ Trs.filter (\r -> R.root (R.lhs r) == Right f) trs ]
          `SMT.bandM` SMT.bigAndM [ inFilterM f i `SMT.impliesM` omega ti | (i,ti) <- zip [1..] ts]

