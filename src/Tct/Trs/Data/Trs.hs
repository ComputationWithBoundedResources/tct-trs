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
  , Signature (..)
  , arity
  , symbols
  , elems
  , onSignature
  , Symbols
  , SelectorExpression (..)

  , map
  , toList, fromList
  , funs

  , signature
  , restrictSignature
  , definedSymbols
  , constructorSymbols

  , empty, singleton, concat, union, unions, difference, intersect, filter

  , null
  , isDuplicating, isLinear
  , isNonErasing, isNonSizeIncreasing, isNonDuplicating

  , isLinear', isNonErasing', isNonSizeIncreasing', isNonDuplicating'
  ) where


import qualified Data.Foldable          as F
import qualified Data.Map.Strict        as M
import           Data.Maybe             (fromMaybe)
import qualified Data.Set               as S
import           Data.Typeable
import           Prelude                hiding (filter, concat, map, null)

import qualified Tct.Core.Common.Pretty as PP

import           Data.Rewriting.Rule    (Rule)
import qualified Data.Rewriting.Rule    as R
import qualified Data.Rewriting.Term    as T

import qualified Tct.Trs.Data.Rewriting as R




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

map :: (Ord f2, Ord v2) => (Rule f1 v1 -> Rule f2 v2) -> Trs f1 v1 -> Trs f2 v2
map k = fromList . fmap k . toList

toList :: Trs f v -> [Rule f v]
toList (TrsT rs) = S.toList rs

fromList :: (Ord f, Ord v) => [Rule f v] -> Trs f v
fromList = TrsT . S.fromList

newtype Signature f = Signature {runSignature :: M.Map f Int}
  deriving (Eq, Ord, Show)

type Symbols f = S.Set f

arity :: (Ord f, Show f) => Signature f ->  f -> Int
arity sig f = err `fromMaybe` M.lookup f (runSignature sig)
  where err = error $ "Signature: not found " ++ show f

symbols :: Signature f -> Symbols f
symbols = M.keysSet . runSignature

elems :: Signature f -> [(f, Int)]
elems = M.assocs . runSignature

onSignature :: (M.Map f Int -> M.Map f2 Int) -> Signature f -> Signature f2
onSignature f = Signature . f . runSignature

funs :: (Ord f, Ord v) => Trs f v -> Symbols f
funs (TrsT rs) = S.foldl k S.empty rs
  where k acc = S.union acc . S.fromList . R.funs


-- FIXME: is not safe
signature :: Ord f => Trs f v -> Signature f
signature rules = Signature $ foldl k M.empty (toList rules)
  where
    k m (R.Rule l r) = M.unions [m, fa l, fa r]
    fa t = M.fromList (T.funs $ T.withArity t)

restrictSignature :: Ord f => Signature f -> Symbols f -> Signature f
restrictSignature sig fs = Signature $ M.filterWithKey k (runSignature sig)
  where k f _ = f `S.member` fs

definedSymbols :: (Ord f, Ord v) => Trs f v -> Symbols f
definedSymbols (TrsT rs) = S.foldr ofRule S.empty rs
  where
    ofRule (R.Rule l r) acc = ofTerm r (ofTerm l acc)
    ofTerm (T.Fun f _)  acc = f `S.insert` acc
    ofTerm _ acc           = acc

constructorSymbols :: Ord f => Signature f -> Symbols f -> Symbols f
constructorSymbols sig defineds = alls `S.difference` defineds
  where alls = S.fromList (M.keys $ runSignature sig)


lift1 :: (RuleSet f v -> a) -> Trs f v -> a
lift1 f (TrsT rs) = f rs

lift2 :: (RuleSet f v -> RuleSet f v -> a) -> Trs f v -> Trs f v -> a
lift2 f (TrsT rs1)  (TrsT rs2) = f rs1 rs2

empty :: Trs f v
empty = TrsT S.empty

singleton :: Rule f v -> Trs f v
singleton = TrsT . S.singleton

concat :: (Ord f, Ord v) => Trs f v -> Trs f v -> Trs f v
concat trs1 trs2 = TrsT $ lift2 S.union trs1 trs2

union :: (Ord f, Ord v) => Trs f v -> Trs f v -> Trs f v
union trs1 trs2 = TrsT $ lift2 S.union trs1 trs2

unions :: (Ord f, Ord v) => [Trs f v] -> Trs f v
unions []   = empty
unions trss = foldl1 union trss

intersect :: (Ord f, Ord v) => Trs f v -> Trs f v -> Trs f v
intersect trs1 trs2 = TrsT $ lift2 S.intersection trs1 trs2

difference :: (Ord f, Ord v) => Trs f v -> Trs f v -> Trs f v
difference trs1 trs2 = TrsT $ lift2 S.difference trs1 trs2

filter :: (Rule f v -> Bool) -> Trs f v -> Trs f v
filter k (TrsT rs) = TrsT (S.filter k rs)


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
instance PP.Pretty f => PP.Pretty (f, Int) where
  pretty (f,i) = PP.tupled [PP.pretty f, PP.int i]

ppTrs :: (PP.Pretty f, PP.Pretty v) => Trs f v -> PP.Doc
ppTrs = F.foldl k PP.empty
  where k doc rs = doc PP.<$$> PP.pretty rs

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Trs f v) where
  pretty = ppTrs

