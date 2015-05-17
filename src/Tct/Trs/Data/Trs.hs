-- | This module provides a set like interface to TRSs.
-- 
-- Should be imported qualified.
module Tct.Trs.Data.Trs
  (
  Trs
  , SelectorExpression (..)

  , map
  , toList, toAscList, fromList
  , funs

  -- , definedSymbols
  -- , constructorSymbols
  , symbols
  , signature

  , member
  , isSubset
  , empty, singleton, concat, union, unions, difference, intersect, filter

  , size
  , null
  , isWellformed
  , isDuplicating, isLinear, isLeftLinear, isRightLinear, isCollapsing
  , isNonErasing, isNonSizeIncreasing, isNonDuplicating
  , isOverlay

  , isLinear', isRightLinear', isNonErasing', isNonSizeIncreasing', isNonDuplicating'
  , isOverlay'
  ) where


import qualified Data.Foldable          as F
import qualified Data.Set               as S
import qualified Data.Map               as M
import qualified Data.List              as L

import           Data.Typeable
import           Prelude                hiding (concat, filter, map, null)

import qualified Tct.Core.Common.Pretty as PP
import qualified Tct.Core.Common.Xml    as Xml

import           Data.Rewriting.Rule    (Rule)
import qualified Data.Rewriting.Rule    as R
import qualified Data.Rewriting.Rules   as R (lhss)
import qualified Data.Rewriting.Term    as T
import qualified Data.Rewriting.CriticalPair as CP

import qualified Tct.Trs.Data.Rewriting as R
import qualified Tct.Trs.Data.Signature as Sig



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


funs :: Ord f => Trs f v -> S.Set f
funs (TrsT rs) = S.foldl k S.empty rs
  where k acc = S.union acc . S.fromList . R.funs

map :: (Ord f2, Ord v2) => (Rule f1 v1 -> Rule f2 v2) -> Trs f1 v1 -> Trs f2 v2
map k = fromList . fmap k . toList

toList :: Trs f v -> [Rule f v]
toList (TrsT rs) = S.toList rs

toAscList :: Trs f v -> [Rule f v]
toAscList (TrsT rs) = S.toAscList rs

fromList :: (Ord f, Ord v) => [Rule f v] -> Trs f v
fromList = TrsT . S.fromList

definedSymbols :: Ord f => Trs f v -> S.Set f
definedSymbols (TrsT rs) = S.foldr ofRule S.empty rs
  where
    ofRule (R.Rule l _) = ofTerm l
    ofTerm (T.Fun f _)  = (f `S.insert`)
    ofTerm _            = id

-- constructorSymbols :: Ord f => Trs f v -> S.Set f 
-- constructorSymbols trs = funs trs `S.difference` definedSymbols trs

symbols :: (Ord f, Ord v) => Trs f v -> (M.Map f Int, M.Map f Int)
symbols trs = (toMap ds, toMap $ funs trs' `S.difference` ds)
  where 
    trs' = map (\(R.Rule l r) -> R.Rule (T.withArity l) (T.withArity r)) trs
    ds           = definedSymbols trs'

    toMap        = foldr insert M.empty . S.toAscList
    insert (k,a) = M.insertWith err k a
    err          = error "Tct.Trs.Data.Trs: Symbol already defined with different arity."

signature :: (Ord f, Ord v) => Trs f v -> Sig.Signature f
signature = Sig.mkSignature . symbols


lift1 :: (RuleSet f v -> a) -> Trs f v -> a
lift1 f (TrsT rs) = f rs

lift2 :: (RuleSet f v -> RuleSet f v -> a) -> Trs f v -> Trs f v -> a
lift2 f (TrsT rs1)  (TrsT rs2) = f rs1 rs2

member :: (Ord f, Ord v) => Rule f v -> Trs f v -> Bool
member = lift1 . S.member

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

size :: Trs f v -> Int
size = lift1 S.size

null :: Trs f v -> Bool
null = lift1 S.null

isSubset :: (Ord f, Ord v) => Trs f v -> Trs f v -> Bool
isSubset = lift2 S.isSubsetOf

isWellformed :: Ord v => Trs f v -> Bool
isWellformed trs = all T.isFun (R.lhss rules) && all (\r -> vars (R.rhs r) `S.isSubsetOf` vars (R.lhs r)) rules
  where 
    rules = toList trs
    vars = S.fromList . T.vars

isLinear, isLeftLinear, isRightLinear, isDuplicating, isCollapsing :: (Ord f, Ord v) => Trs f v -> Bool
isLinear      = all' R.isLinear
isLeftLinear  = all' R.isLeftLinear
isRightLinear = all' R.isRightLinear
isDuplicating = any' R.isDuplicating
isCollapsing  = any' R.isCollapsing

isNonErasing, isNonSizeIncreasing, isNonDuplicating :: (Ord f, Ord v) => Trs f v -> Bool
isNonErasing        = all' R.isNonErasing
isNonSizeIncreasing = all' R.isNonSizeIncreasing
isNonDuplicating    = not . isDuplicating

isOverlay :: (Ord f, Ord v) => Trs f v -> Bool
isOverlay = L.null . CP.cpsIn' . toList 

-- * property-tests; return Just msg if property is not fulfilled.
-- TODO: MS: this is confusing as we comine with <|> eg. isLinear' <|> isNonDuplicating'
-- use Either, rename, fixed type?

note :: Bool -> String -> Maybe String
note b st = if b then Just st else Nothing

isLinear', isRightLinear'  :: (Ord f, Ord v) => Trs f v -> Maybe String
isLinear' trs      = note (not $ isLinear trs) " some rule is non-linear"
isRightLinear' trs = note (not $ isRightLinear trs) " some rule is not right linear"

isNonErasing', isNonSizeIncreasing', isNonDuplicating' :: (Ord f, Ord v) => Trs f v -> Maybe String
isNonErasing' trs        = note (not $ isNonErasing trs) " some rule is erasing"
isNonSizeIncreasing' trs = note (not $ isNonSizeIncreasing trs) " some rule is size-increasing"
isNonDuplicating' trs    = note (not $ isNonDuplicating trs) " some rule is duplicating"

isOverlay' :: (Ord f, Ord v) => Trs f v -> Maybe String
isOverlay' trs = note (not $ isOverlay trs) " system is not overlay"

--- * proof data -----------------------------------------------------------------------------------------------------

ppTrs :: (PP.Pretty f, PP.Pretty v) => Trs f v -> PP.Doc
ppTrs = PP.vcat . fmap PP.pretty . toList

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Trs f v) where
  pretty = ppTrs

instance (Xml.Xml f, Xml.Xml v) => Xml.Xml (R.Term f v) where
  toXml (R.Fun f ts) = Xml.elt "funapp" $ Xml.toXml f :  [ Xml.elt "arg" [Xml.toXml t] | t <- ts ]
  toXml (R.Var v)    = Xml.toXml v
  toCeTA = Xml.toXml

instance (Xml.Xml f, Xml.Xml v) => Xml.Xml (R.Rule f v) where
  toXml r = Xml.elt "rule"
    [ Xml.elt "lhs" [Xml.toXml $ R.lhs r]
    , Xml.elt "rhs" [Xml.toXml $ R.rhs r] ]
  toCeTA = Xml.toXml

instance (Xml.Xml f, Xml.Xml v) => Xml.Xml (Int, R.Rule f v) where
  toXml (i,r) = Xml.toXml r `Xml.setAtts` [Xml.att "rid" (show i)]

instance (Xml.Xml f, Xml.Xml v) => Xml.Xml (Trs f v) where
  toXml rs = Xml.elt "rules" [ Xml.toXml r | r <- toList rs ]
  toCeTA   = Xml.toXml

