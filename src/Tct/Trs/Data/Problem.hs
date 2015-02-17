module Tct.Trs.Data.Problem
  where

import Data.Typeable
import Control.Applicative ((<|>))
import qualified Data.Set as S
import qualified Data.ByteString.Char8 as BS

import qualified Data.Rewriting.Problem as R
import qualified Data.Rewriting.Rule as R (Rule (..))
import qualified Data.Rewriting.Term as R

import qualified Tct.Core.Common.Pretty  as PP
import qualified Tct.Core.Common.Xml     as Xml

import Tct.Trs.Data.DependencyGraph (DependencyGraph, DG, CDG)
import qualified Tct.Trs.Data.DependencyGraph as DPG
import Tct.Trs.Data.ProblemKind
import Tct.Trs.Data.RuleSet
import Tct.Trs.Data.Trs (Trs)
import qualified Tct.Trs.Data.Trs as Trs

import Tct.Trs.Data.Signature (Signature)
import qualified Tct.Trs.Data.Signature as Sig


-- | The problem type.
data Problem f v = Problem
  { startTerms :: StartTerms f
  , strategy   :: Strategy
  , signature  :: Signature f

  , strictDPs  :: Trs f v
  , strictTrs  :: Trs f v
  , weakDPs    :: Trs f v
  , weakTrs    :: Trs f v

  , dpGraph    :: DependencyGraph f v 
  } deriving (Show, Eq)

dependencyGraph :: Problem f v -> DG f v
dependencyGraph = DPG.dependencyGraph . dpGraph

congruenceGraph :: Problem f v -> CDG f v
congruenceGraph = DPG.congruenceGraph . dpGraph

-- | Annotated function symbol.
data AFun f
  = TrsFun f
  | DpFun f
  | ComFun Int
  deriving (Eq, Ord, Show, Typeable)

newtype F = F (AFun BS.ByteString)
  deriving (Eq, Ord, Show, Typeable)

markFun :: F -> F 
markFun (F (TrsFun f)) = F (DpFun f)
markFun _              = error "Tct.Trs.Data.Problem.markFun: not a trs symbol"

compoundf :: Int -> F
compoundf = F . ComFun

isCompoundf :: F -> Bool
isCompoundf (F (ComFun _)) = True
isCompoundf _              = False

instance PP.Pretty F where
  pretty (F (TrsFun f)) = PP.text (BS.unpack f)
  pretty (F (DpFun f))  = PP.text (BS.unpack f) PP.<> PP.char '#'
  pretty (F (ComFun i)) = PP.pretty "c_" PP.<> PP.int i

instance Xml.Xml F where
  toXml (F (TrsFun f)) = Xml.elt "name" [Xml.text $ BS.unpack  f]
  toXml (F (DpFun f))  = Xml.elt "sharp" [Xml.elt "name" [Xml.text $ BS.unpack f]]
  toXml (F (ComFun f)) = Xml.elt "name" [Xml.text $ 'c':show f]
  toCeTA = Xml.toXml

newtype V = V BS.ByteString
  deriving (Eq, Ord, Show, Typeable)

instance PP.Pretty V where
  pretty (V v) = PP.text (BS.unpack v)

instance Xml.Xml V where
  toXml (V v) = Xml.elt "var" [Xml.text (BS.unpack v)]
  toCeTA      = Xml.toXml

type TrsProblem = Problem F V

sanitise :: (Ord f, Ord v) => Problem f v -> Problem f v
sanitise = sanitiseDPGraph . sanitiseDPGraph

sanitiseDPGraph :: (Ord f, Ord v) => Problem f v -> Problem f v
sanitiseDPGraph prob = prob
  { dpGraph = DPG.estimatedDependencyGraph (ruleSet prob) (strategy prob) }

sanitiseSignature :: (Ord f, Ord v) => Problem f v -> Problem f v
sanitiseSignature prob = prob 
  { startTerms = restrictST (startTerms prob)
  , signature  = sig }
  where 
    sig   = Sig.restrictSignature (signature prob) (Trs.funs $ allComponents prob)
    allfs = Sig.symbols sig
    restrictST (AllTerms fs)      = AllTerms (fs `S.intersection` allfs)
    restrictST (BasicTerms ds cs) = BasicTerms (ds `S.intersection` allfs) (cs `S.intersection` allfs)

fromRewriting :: R.Problem String String -> TrsProblem
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
  , weakTrs    = wTrs 
  
  , dpGraph = DPG.empty }
  where 
    toFun (R.Rule l r) = let k = R.map (F . TrsFun . BS.pack) (V . BS.pack) in R.Rule (k l) (k r)
    sTrs = Trs.fromList . map toFun $ R.strictRules (R.rules prob)
    wTrs = Trs.fromList . map toFun $ R.weakRules (R.rules prob)
    trs  = sTrs `Trs.union` wTrs
    sig  = Trs.signature trs
    defs = Trs.definedSymbols trs
    cons = Trs.constructorSymbols sig defs

progressUsingSize :: Problem f v -> Problem f v -> Bool
progressUsingSize p1 p2 = 
  Trs.size (strictDPs p1) /= Trs.size (strictDPs p2)
  || Trs.size (strictTrs p1) /= Trs.size (strictTrs p2)
  || Trs.size (weakDPs p1) /= Trs.size (weakDPs p2)
  || Trs.size (weakTrs p1) /= Trs.size (weakTrs p2)

strictComponents, weakComponents, allComponents :: (Ord f, Ord v) => Problem f v -> Trs f v
strictComponents prob = strictDPs prob `Trs.concat` strictTrs prob
weakComponents prob   = weakDPs prob `Trs.concat` weakTrs prob
allComponents prob    = strictComponents prob `Trs.concat` weakComponents prob

dpComponents, trsComponents :: (Ord f, Ord v) => Problem f v -> Trs f v
dpComponents prob  = strictDPs prob `Trs.concat` weakDPs prob
trsComponents prob = strictTrs prob `Trs.concat` weakTrs prob

isDPProblem :: Problem f v -> Bool
isDPProblem prob = not $ Trs.null (strictDPs prob) && Trs.null (weakDPs prob)

-- TODO MS: is there a better name for this
isDTProblem :: Problem f v -> Bool
isDTProblem prob = isDPProblem prob && Trs.null (strictTrs prob)

isRCProblem, isDCProblem :: Problem f v -> Bool
isRCProblem prob = case startTerms prob of
  BasicTerms{} -> True
  _            -> False
isDCProblem prob = case startTerms prob of
  AllTerms{} -> True
  _          -> False

note :: Bool -> String -> Maybe String
note b st = if b then Just st else Nothing


isDPProblem' :: Problem f v -> Maybe String
isDPProblem' prob = note (not $ isDPProblem  prob) " not a DP problem"

isDTProblem' :: Problem f v -> Maybe String
isDTProblem' prob = isDPProblem' prob <|> note (not $ Trs.null (strictTrs prob)) " contains strict rules"

isRCProblem', isDCProblem' :: Problem f v -> Maybe String
isRCProblem' prob = note (not $ isRCProblem  prob) " not a RC problem"
isDCProblem' prob = note (not $ isDCProblem  prob) " not a DC problem"

isInnermostProblem :: Problem f v -> Bool
isInnermostProblem prob = strategy prob == Innermost

isInnermostProblem' :: Problem f v -> Maybe String
isInnermostProblem' prob = note (not $ isInnermostProblem prob) "not an innermost problem"

isTrivial :: (Ord f, Ord v) => Problem f v -> Bool
isTrivial prob = Trs.null (strictDPs prob) && Trs.null (strictComponents prob)


-- * ruleset
ruleSet :: Problem f v -> RuleSet f v
ruleSet prob = RuleSet 
  { sdps = strictDPs prob
  , wdps = weakDPs prob
  , strs = strictTrs prob
  , wtrs = weakTrs prob }


-- * pretty printing
instance PP.Pretty BS.ByteString where
  pretty = PP.text . BS.unpack

instance Xml.Xml BS.ByteString where
  toXml  = Xml.text . BS.unpack
  toCeTA = Xml.text . BS.unpack

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Problem f v) where
  pretty prob = PP.vcat
    [ PP.text "Strict Rules:"
    , PP.indent 2 $ PP.pretty (strictDPs prob)
    , PP.indent 2 $ PP.pretty (strictTrs prob)
    , PP.text "Weak Rules:"
    , PP.indent 2 $ PP.pretty (weakDPs prob)
    , PP.indent 2 $ PP.pretty (weakTrs prob) ]

