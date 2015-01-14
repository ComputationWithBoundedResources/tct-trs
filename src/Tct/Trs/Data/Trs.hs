{-# LANGUAGE DeriveFoldable #-}
module Tct.Trs.Data.Trs
  (
  Trs
  , AFun (..), Fun, Var, Rule
  , ruleList, fromRuleList
  , Signature
  , Symbols
  , funs
  , mkSignature
  , restrictSignature
  , mkDefinedSymbols
  , mkConstructorSymbols
  , empty, singleton, union, unions, difference, intersect
  , SelectorExpression (..)
    
  , isEmpty
  , isDuplicating, isLinear
  , isNonErasing, isNonSizeIncreasing, isNonDuplicating

  , isLinear', isNonErasing', isNonSizeIncreasing', isNonDuplicating'
  
  -- , module Data.Rewriting.Rules
  ) where


import qualified Data.Map.Strict as M
import Data.Typeable
import qualified Data.Set as S
import qualified Data.Foldable as F

import qualified Tct.Core.Common.Pretty as PP

import qualified Data.Rewriting.Rule        as R 
import qualified Data.Rewriting.Term        as T

import qualified Tct.Trs.Data.Rewriting     as R 


-- | Annotated function symbol.
data AFun f
  = TrsFun f
  | DpFun f
  | ComFun Int
  deriving (Eq, Ord, Show)

-- TODO: MS are there some rules; how they should look like
-- eg what happens if the initial Trs has a symbol ending with #
instance PP.Pretty f => PP.Pretty (AFun f) where
  pretty (TrsFun s) = PP.pretty s
  pretty (DpFun s) = PP.pretty s PP.<> PP.char '#'
  pretty (ComFun i) = PP.pretty "c_" PP.<> PP.int i

type Var  = String
type Fun  = AFun String
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

type Signature      = M.Map Fun Int
type Symbols        = S.Set Fun

-- FIXME: is not safe
mkSignature :: Trs -> Signature
mkSignature rules = foldl k M.empty (ruleList rules)
  where 
    k m (R.Rule l r) = M.unions [m, fa l, fa r]
    fa t = M.fromList (T.funs $ T.withArity t)

funs :: Trs -> Symbols
funs (TrsT rs) = S.foldl k S.empty rs
  where k acc = S.union acc . S.fromList . R.funs 

restrictSignature :: Signature -> Symbols -> Signature
restrictSignature sig fs = M.filterWithKey k sig
  where k f _ = f `S.member` fs

mkDefinedSymbols :: Trs -> Symbols
mkDefinedSymbols (TrsT rs) = S.foldl ofRule S.empty rs
  where 
   ofRule acc (R.Rule l r) = ofTerm (ofTerm acc l) r
   ofTerm acc (T.Fun f _) = f `S.insert` acc
   ofTerm acc _           = acc

mkConstructorSymbols :: Signature -> Symbols -> Symbols
mkConstructorSymbols sig defineds = alls `S.difference` defineds
  where alls = S.fromList (M.keys sig)

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

