{- This module provides \Argument Filtering\. -}
module Tct.Trs.Data.ArgumentFiltering 
  ( ArgumentFiltering
  , empty
  , alter
  , apply 
  ) where


import Data.Monoid
import Data.Maybe (fromMaybe)
import qualified Data.IntSet as IS
import qualified Data.Map as M

import qualified Data.Rewriting.Term as R
import qualified Data.Rewriting.Rule as R

import qualified Tct.Core.Common.Pretty as PP

import Tct.Trs.Data.Trs (Trs)
import qualified Tct.Trs.Data.Trs as Trs


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

