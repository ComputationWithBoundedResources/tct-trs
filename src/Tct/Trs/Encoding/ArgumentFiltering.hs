{-# LANGUAGE ScopedTypeVariables #-}
-- | This module provides \Argument Filtering\.
module Tct.Trs.Encoding.ArgumentFiltering
  (
  -- * Argument Filtering
  Filtering (..)
  , ArgumentFiltering
  , empty
  , alter
  , apply

  -- * In Filter Encoding
  , InFilterEncoder
  , inFilterEncoder
  , inFilter
  ) where

import           Control.Monad          (liftM)
import qualified Data.IntSet            as IS
import qualified Data.Map.Strict        as M
import           Data.Maybe             (fromMaybe)
import           Data.Monoid
import qualified Data.Set               as S
import qualified Data.Traversable       as F

import qualified Data.Rewriting.Rule    as R

import qualified Tct.Core.Common.Pretty as PP

import qualified Tct.Common.SMT         as SMT

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem   as Prob
import qualified Tct.Trs.Data.Signature as Sig
import qualified Tct.Trs.Data.Trs       as Trs


data Filtering
  = Projection Int
  | Filtering IS.IntSet
  deriving (Eq, Show)

newtype ArgumentFiltering f = AF (M.Map f Filtering)
  deriving (Eq, Show)

empty :: ArgumentFiltering f
empty = AF M.empty

filtering :: Ord f => (f, Int) -> ArgumentFiltering f -> Filtering
filtering (f,ar) (AF m) = Filtering (IS.fromList $ take ar [1..]) `fromMaybe` M.lookup f m

alter :: Ord f => (Maybe Filtering -> Maybe Filtering) -> f -> ArgumentFiltering f -> ArgumentFiltering f
alter f s (AF m) = AF (M.alter f s m)

apply :: (Ord f, Ord v) => Trs f v -> ArgumentFiltering f -> Trs f v
apply trs af = filterRule `Trs.map` trs
  where
    filterRule (R.Rule l r) = R.Rule (filterTerm l) (filterTerm r)
    filterTerm (R.Fun f ts) = case filtering (f,length ts) af of
      Projection i -> filterTerm $ ts!!(i-1)
      Filtering is -> R.Fun f (map filterTerm . snd $ foldl k (1,[]) ts)
        where k (i,nts) ti = if i `IS.member` is then (i+1,ti:nts) else (i+1,nts)
    filterTerm v = v

{-fold :: (Symbol -> Filtering -> b -> b) -> ArgumentFiltering -> b -> b-}
{-fold f af@(AF (sig, _)) m = foldr f' m (Set.toList $ symbols sig)-}
  {-where f' sym = f sym (filtering sym af)-}

instance PP.Pretty f => PP.Pretty (ArgumentFiltering f) where
  pretty (AF m)
    | M.null m  = PP.text "empty"
    | otherwise = PP.hsep $ PP.punctuate (PP.text ",")  [ppp s f | (s,f) <- M.toList m]
    where
      ppp s f = PP.text "pi" <> PP.parens (PP.pretty s) <> PP.text " = " <> ppf f
      ppf (Projection i) = PP.int i
      ppf (Filtering is) = PP.list [ PP.int i | i <- IS.toList is]


--- * infilter -------------------------------------------------------------------------------------------------------
--- a restricted version that ignores projection

data InFilterEncoder f w = InFilterEncoder
  (ArgumentFiltering f)     -- ^ initial argument filtering
  (M.Map (f,Int) (SMT.Formula w))  -- ^ variable mapping

instance (Ord f, SMT.Storing w) => SMT.Decode (SMT.Environment w) (InFilterEncoder f w) (ArgumentFiltering f) where
  decode (InFilterEncoder af m) = do
    fis :: S.Set (f,Int) <- SMT.decode (SMT.Property (fromMaybe False) m)
    return $ S.foldr insert af fis
    where
      insert (f,i) = alter (k i) f
      k i (Just (Filtering s)) = Just $ Filtering (IS.insert i s)
      k _ _                    = error "Tct.Trs.Encoding.ArgumentFiltering.decode.insert: filtering not defined."

-- | Sets the initial argumentfiltering. Provides a mapping for each @(symbol, position)@.
inFilterEncoder :: (SMT.Fresh w, Ord f) => Problem f v -> SMT.SmtSolverSt w (InFilterEncoder f w)
inFilterEncoder prob = InFilterEncoder initial `liftM` mapping
  where
    sig = Prob.signature prob
    initial = S.foldr (alter mkF) empty $ Sig.symbols sig
    mkF _   = Just (Filtering IS.empty)
    mapping = M.fromList `liftM` F.mapM mkM (concatMap mkV $ Sig.elems sig)
    mkV (f, i) = zip (repeat f) [1 .. i]
    mkM k = SMT.bvarM' >>= \v -> return (k,v)

-- | In filter mapping.
inFilter :: Ord f => InFilterEncoder f w -> f -> Int -> (SMT.Formula w)
inFilter (InFilterEncoder _ m) f i = error err `fromMaybe` M.lookup (f,i) m
  where err = "Tct.Trs.Encoding.ArgumentFiltering: entry not defined."

