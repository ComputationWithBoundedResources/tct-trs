{-# LANGUAGE DeriveFoldable #-}
module Tct.Trs.Data.Trs
  (
  Trs
  , Fun, Var, Rule
  , ruleList, fromRuleList
  , empty, singleton, union, unions, difference, intersect
  , SelectorExpression (..)
    
  , isEmpty
  , isDuplicating, isLinear
  , isNonErasing, isNonSizeIncreasing, isNonDuplicating

  , isLinear', isNonErasing', isNonSizeIncreasing', isNonDuplicating'
  
  -- , module Data.Rewriting.Rules
  ) where


import Data.Typeable
import qualified Data.Set as S
import qualified Data.Foldable as F

import qualified Tct.Core.Common.Pretty as PP

import qualified Data.Rewriting.Rule        as R 

import qualified Tct.Trs.Data.Rewriting     as R 


type Fun  = String
type Var  = String
type Rule = R.Rule Fun Var

type RuleSet = S.Set Rule

newtype TrsT a = TrsT (S.Set a)
  deriving (Eq, Ord, Show, F.Foldable)

type Trs = TrsT Rule

data SelectorExpression
  = SelectDP Rule
  | SelectTrs Rule
  | BigAnd [SelectorExpression]
  | BigOr [SelectorExpression]
  deriving (Show, Typeable)

ruleList :: Trs -> [Rule]
ruleList (TrsT rs) = S.elems rs

fromRuleList :: [Rule] -> Trs
fromRuleList = TrsT . S.fromList 

lift1 :: (RuleSet -> a) -> Trs -> a
lift1 f (TrsT rs) = f rs 

lift2 :: (RuleSet -> RuleSet -> a) -> Trs -> Trs -> a
lift2 f (TrsT rs1)  (TrsT rs2) = f rs1 rs2

empty :: Trs
empty = TrsT S.empty

singleton :: Rule -> Trs
singleton = TrsT . S.singleton

union :: Trs -> Trs -> Trs
union trs1 trs2 = TrsT $ lift2 S.union trs1 trs2

unions :: [Trs] -> Trs
unions = undefined

intersect :: Trs -> Trs -> Trs
intersect trs1 trs2 = TrsT $ lift2 S.intersection trs1 trs2

difference :: Trs -> Trs -> Trs
difference trs1 trs2 = TrsT $ lift2 S.difference trs1 trs2


-- * properties
any' :: (Rule -> Bool) -> Trs -> Bool
any' f (TrsT rs) = S.foldr ((||) . f) False rs

all' :: (Rule -> Bool) -> Trs -> Bool
all' f (TrsT rs) = S.foldr ((&&) . f) True rs

isEmpty :: Trs -> Bool
isEmpty = lift1 S.null

isLinear, isDuplicating :: Trs -> Bool
isLinear         = all' R.isLinear
isDuplicating    = any' R.isDuplicating

isNonErasing, isNonSizeIncreasing, isNonDuplicating :: Trs -> Bool
isNonErasing        = all' R.isNonErasing
isNonSizeIncreasing = all' R.isNonSizeIncreasing
isNonDuplicating    = not . isDuplicating


-- * property-tests; return Just msg if property is not fulfilled.

note :: Bool -> String -> Maybe String
note b st = if b then Just st else Nothing

isLinear'  :: Trs -> Maybe String
isLinear' trs = note (not $ isLinear trs) " some rule is non-linear"

isNonErasing', isNonSizeIncreasing', isNonDuplicating' :: Trs -> Maybe String
isNonErasing' trs        = note (not $ isNonErasing trs) " some rule is erasing"
isNonSizeIncreasing' trs = note (not $ isNonSizeIncreasing trs) " some rule is size-increasing"
isNonDuplicating' trs    = note (not $ isNonDuplicating trs) " some rule is duplicating"




-- * pretty printing --

ppTrs :: Trs -> PP.Doc
ppTrs = F.foldl k PP.empty
  where k doc rs = doc PP.<$$> PP.pretty rs

instance PP.Pretty Trs where
  pretty = ppTrs

