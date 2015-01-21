{- | 
Set like interface TRSs.

Should be imported qualified.
 -}
-- TODO: MS
-- at some point check if lists actually would be better
-- * often we use toList + map
-- * often we use Prob.dpComponents ..., and we have to perform a union; for lists we could just concat the
-- components assuming that problem itself is valid

{-# LANGUAGE DeriveFoldable #-}
module Tct.Trs.Data.Trs
  (
  Trs
  , Signature
  , Symbols
  , SelectorExpression (..)

  , toList, fromList
  , funs

  , signature
  , restrictSignature
  , definedSymbols
  , constructorSymbols

  , empty, singleton, union, unions, difference, intersect
    
  , null
  , isDuplicating, isLinear
  , isNonErasing, isNonSizeIncreasing, isNonDuplicating

  , isLinear', isNonErasing', isNonSizeIncreasing', isNonDuplicating'
  ) where


import Prelude hiding (null)
import qualified Data.Map.Strict as M
import Data.Typeable
import qualified Data.Set as S
import qualified Data.Foldable as F

import qualified Tct.Core.Common.Pretty as PP

import Data.Rewriting.Rule (Rule)
import qualified Data.Rewriting.Rule        as R 
import qualified Data.Rewriting.Term        as T

import qualified Tct.Trs.Data.Rewriting     as R 




type RuleSet f v = S.Set (Rule f v)

newtype TrsT a = TrsT (S.Set a)
  deriving (Eq, Ord, Show, F.Foldable)

type Trs f v = TrsT (R.Rule f v)

data SelectorExpression f v
  = SelectDP (Rule f v)
  | SelectTrs (Rule f v)
  | BigAnd [SelectorExpression f v]
  | BigOr [SelectorExpression f v]
  deriving (Show, Typeable)

toList :: Trs f v -> [Rule f v]
toList (TrsT rs) = S.toList rs

fromList :: (Ord f, Ord v) => [Rule f v] -> Trs f v
fromList = TrsT . S.fromList

type Signature f    = M.Map f Int
type Symbols f      = S.Set f

funs :: (Ord f, Ord v) => Trs f v -> Symbols f
funs (TrsT rs) = S.foldl k S.empty rs
  where k acc = S.union acc . S.fromList . R.funs 

-- FIXME: is not safe
signature :: Ord f => Trs f v -> Signature f
signature rules = foldl k M.empty (toList rules)
  where 
    k m (R.Rule l r) = M.unions [m, fa l, fa r]
    fa t = M.fromList (T.funs $ T.withArity t)

restrictSignature :: (Ord f) => Signature f -> Symbols f -> Signature f
restrictSignature sig fs = M.filterWithKey k sig
  where k f _ = f `S.member` fs

definedSymbols :: (Ord f, Ord v) => Trs f v -> Symbols f
definedSymbols (TrsT rs) = S.foldl ofRule S.empty rs
  where 
   ofRule acc (R.Rule l r) = ofTerm (ofTerm acc l) r
   ofTerm acc (T.Fun f _) = f `S.insert` acc
   ofTerm acc _           = acc

constructorSymbols :: Ord f => Signature f -> Symbols f -> Symbols f
constructorSymbols sig defineds = alls `S.difference` defineds
  where alls = S.fromList (M.keys sig)


lift1 :: (RuleSet f v -> a) -> Trs f v -> a
lift1 f (TrsT rs) = f rs 

lift2 :: (RuleSet f v -> RuleSet f v -> a) -> Trs f v -> Trs f v -> a
lift2 f (TrsT rs1)  (TrsT rs2) = f rs1 rs2

empty :: Trs f v
empty = TrsT S.empty

singleton :: Rule f v -> Trs f v
singleton = TrsT . S.singleton

union :: (Ord f, Ord v) => Trs f v -> Trs f v -> Trs f v
union trs1 trs2 = TrsT $ lift2 S.union trs1 trs2

unions :: (Ord f, Ord v) => [Trs f v] -> Trs f v
unions []   = empty
unions trss = foldl1 union trss

intersect :: (Ord f, Ord v) => Trs f v -> Trs f v -> Trs f v
intersect trs1 trs2 = TrsT $ lift2 S.intersection trs1 trs2

difference :: (Ord f, Ord v) => Trs f v -> Trs f v -> Trs f v
difference trs1 trs2 = TrsT $ lift2 S.difference trs1 trs2


-- * properties
any' :: (Rule f v -> Bool) -> Trs f v -> Bool
any' f (TrsT rs) = S.foldr ((||) . f) False rs

all' :: (Rule f v -> Bool) -> Trs f v -> Bool
all' f (TrsT rs) = S.foldr ((&&) . f) True rs

null :: Trs f v -> Bool
null = lift1 S.null

isLinear, isDuplicating :: (Ord f, Ord v) => Trs f v -> Bool
isLinear         = all' R.isLinear
isDuplicating    = any' R.isDuplicating

isNonErasing, isNonSizeIncreasing, isNonDuplicating :: (Ord f, Ord v) => Trs f v -> Bool
isNonErasing        = all' R.isNonErasing
isNonSizeIncreasing = all' R.isNonSizeIncreasing
isNonDuplicating    = not . isDuplicating


-- * property-tests; return Just msg if property is not fulfilled.

note :: Bool -> String -> Maybe String
note b st = if b then Just st else Nothing

isLinear'  :: (Ord f, Ord v) => Trs f v -> Maybe String
isLinear' trs = note (not $ isLinear trs) " some rule is non-linear"

isNonErasing', isNonSizeIncreasing', isNonDuplicating' :: (Ord f, Ord v) => Trs f v -> Maybe String
isNonErasing' trs        = note (not $ isNonErasing trs) " some rule is erasing"
isNonSizeIncreasing' trs = note (not $ isNonSizeIncreasing trs) " some rule is size-increasing"
isNonDuplicating' trs    = note (not $ isNonDuplicating trs) " some rule is duplicating"




-- * pretty printing --

ppTrs :: (PP.Pretty f, PP.Pretty v) => Trs f v -> PP.Doc
ppTrs = F.foldl k PP.empty
  where k doc rs = doc PP.<$$> PP.pretty rs

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Trs f v) where
  pretty = ppTrs

