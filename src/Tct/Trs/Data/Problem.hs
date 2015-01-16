module Tct.Trs.Data.Problem
  where

import qualified Data.Set as S
import qualified Data.Map.Strict as M

import qualified Data.Rewriting.Problem as R
import qualified Data.Rewriting.Rule as R (Rule (..))
import qualified Data.Rewriting.Term as R

import qualified Tct.Core.Common.Pretty     as PP

import Tct.Trs.Data.Trs (Trs, Fun)
import qualified Tct.Trs.Data.Trs as Trs


data StartTerms
  = AllTerms 
    { allSymbols :: S.Set Fun }
  | BasicTerms 
    { definedSymbols     :: S.Set Fun
    , constructorSymbols :: S.Set Fun }
  deriving (Show, Eq)

data Strategy
  = Innermost
  | Outermost
  | Full
  deriving (Show, Eq)

data Problem = Problem
  { startTerms :: StartTerms
  , strategy   :: Strategy
  , signature  :: Trs.Signature

  , strictDPs  :: Trs
  , strictTrs  :: Trs
  , weakDPs    :: Trs
  , weakTrs    :: Trs
  
  } deriving (Show, Eq)

sanitise :: Problem -> Problem
sanitise prob = prob 
  { startTerms = restrictST (startTerms prob)
  , signature  = sig }
  where 
    sig   = Trs.restrictSignature sig (Trs.funs $ allComponents prob)
    allfs = S.fromList (M.keys sig)
    restrictST (AllTerms fs)      = AllTerms (fs `S.intersection` allfs)
    restrictST (BasicTerms ds cs) = BasicTerms (ds `S.intersection` allfs) (cs `S.intersection` allfs)

fromRewriting :: R.Problem String String -> Problem
fromRewriting prob = Problem
  { startTerms   = case R.startTerms prob of
      R.AllTerms   -> AllTerms (defs `S.union` cons)
      R.BasicTerms -> BasicTerms defs cons
  , strategy = case R.strategy prob of
      R.Innermost -> Innermost
      R.Full      -> Full
      R.Outermost -> Outermost
  , signature  = sig

  , strictDPs  = Trs.empty
  , strictTrs  = sTrs
  , weakDPs    = Trs.empty
  , weakTrs    = wTrs }
  where 
    toFun (R.Rule l r) = let k = R.map Trs.TrsFun id in R.Rule (k l) (k r)
    sTrs = Trs.fromRuleList . map toFun $ R.strictRules (R.rules prob)
    wTrs = Trs.fromRuleList . map toFun $ R.weakRules (R.rules prob)
    trs  = sTrs `Trs.union` wTrs
    sig  = Trs.mkSignature trs
    defs = Trs.mkDefinedSymbols trs
    cons = Trs.mkConstructorSymbols sig defs



strictComponents, weakComponents, allComponents :: Problem -> Trs
strictComponents prob = strictDPs prob `Trs.union` strictTrs prob
weakComponents prob   = weakDPs prob `Trs.union` weakTrs prob
allComponents prob    = strictComponents prob `Trs.union` weakComponents prob

dpComponents, trsComponents :: Problem -> Trs
dpComponents prob  = strictDPs prob `Trs.union` weakDPs prob
trsComponents prob = strictTrs prob `Trs.union` weakTrs prob

isRCProblem, isDCProblem :: Problem -> Bool
isRCProblem prob = case startTerms prob of
  BasicTerms{} -> True
  _            -> False
isDCProblem prob = case startTerms prob of
  AllTerms{} -> True
  _          -> False

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

