module Tct.Trs.Data.Problem
  where

import qualified Data.Map.Strict            as M
import qualified Data.Set as S

import qualified Data.Rewriting.Problem as R
import qualified Data.Rewriting.Rule as R (Rule (..))
import qualified Data.Rewriting.Term as R

import qualified Tct.Core.Common.Pretty     as PP

import Tct.Trs.Data.Trs (Trs, Fun(..))
import qualified Tct.Trs.Data.Trs as Trs

data SymbolKind
  = Defined
  | Constructor
  deriving (Eq, Show)

type Signature = M.Map Fun Int
type Constructors = S.Set Fun
type DefinedSymbols = S.Set Fun

data Problem = Problem
  { startTerms :: R.StartTerms
  , strategy   :: R.Strategy
  , symbols    :: (Signature, DefinedSymbols, Constructors)

  , strictDPs  :: Trs
  , strictTrs  :: Trs
  , weakDPs    :: Trs
  , weakTrs    :: Trs
  
  } deriving (Show)

signature :: Problem -> Signature
signature = (\(sig, _,_) -> sig) . symbols

constructors :: Problem -> Constructors
constructors = (\(_, _,cs) -> cs) . symbols

-- TODO: tpdb format - funs with different arities?
sanitise :: Problem -> Problem
sanitise prob = prob { symbols = (sig, ds, cs) }
  where
    rules = Trs.ruleList $ allComponents prob
    sig = foldl k M.empty rules
      where 
        k m (R.Rule l r) = funs l `M.union` funs r `M.union` m
        funs t = M.fromList (R.funs $ R.withArity t)
    ds = foldl k S.empty rules
      where
        k s (R.Rule (R.Fun f _) _) = f `S.insert` s
        k s _ = s
    cs = S.fromList (M.keys sig) `S.difference` ds

fromRewriting :: R.Problem String String -> Problem
fromRewriting prob = sanitise Problem
  { startTerms = R.startTerms prob
  , strategy   = R.strategy prob
  , symbols    = undefined

  , strictDPs  = Trs.empty
  , strictTrs  = Trs.fromRuleList $ map ruleMap $ R.strictRules (R.rules prob)
  , weakDPs    = Trs.empty
  , weakTrs    = Trs.fromRuleList $ map ruleMap $ R.weakRules (R.rules prob) }
  where ruleMap (R.Rule l r) = let k = R.map TrsFun id in R.Rule (k l) (k r)



strictComponents, weakComponents, allComponents :: Problem -> Trs
strictComponents prob = strictDPs prob `Trs.union` strictTrs prob
weakComponents prob   = weakDPs prob `Trs.union` weakTrs prob
allComponents prob    = strictComponents prob `Trs.union` weakComponents prob

dpComponents, trsComponents :: Problem -> Trs
dpComponents prob  = strictDPs prob `Trs.union` weakDPs prob
trsComponents prob = strictTrs prob `Trs.union` weakTrs prob

isRCProblem, isDCProblem :: Problem -> Bool
isRCProblem prob = startTerms prob == R.BasicTerms
isDCProblem prob = startTerms prob == R.AllTerms

note :: Bool -> String -> Maybe String
note b st = if b then Just st else Nothing

isRCProblem', isDCProblem' :: Problem -> Maybe String
isRCProblem' prob = note (not $ isRCProblem  prob) " not a RC problem"
isDCProblem' prob = note (not $ isDCProblem  prob) " not a DC problem"

isTrivial :: Problem -> Bool
isTrivial = Trs.isEmpty . strictComponents

-- * ruleset
data Ruleset = Ruleset 
  { sdp  :: Trs -- ^ strict dependency pairs                          
  , wdp  :: Trs -- ^ weak dependency pairs
  , strs :: Trs -- ^ strict rules
  , wtrs :: Trs -- ^ weak rules
  }

ruleset :: Problem -> Ruleset
ruleset prob = Ruleset 
  { sdp  = strictDPs prob
  , wdp  = weakDPs prob
  , strs = strictTrs prob
  , wtrs = weakTrs prob }

emptyRuleset :: Ruleset
emptyRuleset = Ruleset Trs.empty Trs.empty Trs.empty Trs.empty


-- * pretty printing

ppProblem :: Problem -> PP.Doc
ppProblem prob =  PP.vcat
  [ PP.text "Strict Rules:"
  , PP.indent 2 $ PP.pretty (strictComponents prob)
  , PP.text "Weak Rules:"
  , PP.indent 2 $ PP.pretty (weakComponents prob) ]

instance PP.Pretty Problem where
  pretty = ppProblem

