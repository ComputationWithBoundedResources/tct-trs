-- | This module implements the /Weak Dependency Pairs/ and the /Dependency Tuples/ processor.
module Tct.Trs.Method.DP.DependencyPairs
  ( DPKind (..)
  , dependencyPairsDeclaration
  , dependencyPairs
  , dependencyPairs'

  , weakDependencyPairs
  , dependencyTuples
  ) where


import           Control.Applicative         ((<|>))
import           Control.Monad.State.Strict
import qualified Data.Traversable            as F
import           Data.Typeable

import qualified Data.Map                    as M
import qualified Data.Set                    as S

import qualified Data.Rewriting.Rule         as R

import qualified Tct.Core.Common.Pretty      as PP
import qualified Tct.Core.Common.Xml         as Xml
import qualified Tct.Core.Data               as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem        as Prob
import qualified Tct.Trs.Data.ProblemKind    as Prob
import qualified Tct.Trs.Data.Signature      as Sig
import qualified Tct.Trs.Data.Trs            as Trs


-- FIXME:
-- MS Compound Symbols should have identifier component
-- it is necessary to compute a fresh symbol for pretty printing only

data DPKind = WDP | WIDP | DT
  deriving (Eq, Enum, Bounded, Typeable)

instance Show DPKind where
  show WDP  = "wdp"
  show WIDP = "widp"
  show DT   = "dt"

isTuples :: DPKind -> Bool
isTuples = (DT==)


-- maximal subterms that are variables or have a root in the defined symbols
subtermsWDP :: Ord f => Symbols f -> R.Term f v -> [R.Term f v]
subtermsWDP defineds s@(R.Fun f ss)
  | f `S.member` defineds = [s]
  | otherwise             = concatMap (subtermsWDP defineds) ss
subtermsWDP _ v = [v]

subtermsWIDP :: Ord f => Symbols f -> R.Term f v -> [R.Term f v]
subtermsWIDP defineds s@(R.Fun f ss)
  | f `S.member` defineds = [s]
  | otherwise             = concatMap (subtermsWIDP defineds) ss
subtermsWIDP _ _ = []

-- subterms that have a root in the defined symbols
subtermsDT :: Ord f => Symbols f -> R.Term f v -> [R.Term f v]
subtermsDT defineds s@(R.Fun f ss)
  | f `S.member` defineds = s :subs
  | otherwise             = subs
  where subs = concatMap (subtermsDT defineds) ss
subtermsDT _ _ = []

-- MS: we follow tct2 and Com(t)=Com(t) for singleton argument list t; hence rhs always have a compound symbol
markRule :: (R.Term F V -> [R.Term F V]) -> R.Rule F V -> State Int (R.Rule F V)
markRule subtermsOf (R.Rule lhs rhs) = do
  i <- modify succ >> get
  return $ R.Rule (markTerm lhs) (R.Fun (Prob.compoundf i) (map markTerm $ subtermsOf rhs))
  where
    markTerm (R.Fun f fs) = R.Fun (Prob.markFun f) fs
    markTerm v            = v

-- | (Original Rule, DP Rule)
type Transformation f v = (R.Rule f v, R.Rule f v)

fromTransformation :: (Ord f, Ord v) => [Transformation f v] -> Trs f v
fromTransformation = Trs.fromList . snd . unzip

markRules :: (R.Term F V -> [R.Term F V]) -> Trs F V -> State Int [Transformation F V]
markRules subtermsOf trs = F.mapM (\r -> markRule subtermsOf r >>= \r' -> return (r,r')) (Trs.toList trs)

dependencyPairsOf :: DPKind -> Symbols F -> Trs F V -> State Int [Transformation F V]
dependencyPairsOf dpKind defineds = markRules $ case dpKind of
  WDP  -> subtermsWDP defineds
  WIDP -> subtermsWIDP defineds
  DT   -> subtermsDT defineds


--- * processor ------------------------------------------------------------------------------------------------------

data DependencyPairs = DependencyPairs { dpKind_ :: DPKind } deriving Show

data DependencyPairsProof = DependencyPairsProof
  { strictTransformation :: [Transformation F V]
  , weakTransformation   :: [Transformation F V]
  , dpKindUsed           :: DPKind
  , newSignature         :: Signature F }
  deriving Show

instance T.Processor DependencyPairs where
  type ProofObject DependencyPairs = ApplicationProof DependencyPairsProof
  type Problem DependencyPairs     = TrsProblem

  solve p prob                 = return . T.resultToTree p prob $
    maybe dp (T.Fail . Inapplicable) maybeApplicable
    where
      dp = T.Success (T.toId nprob) (Applicable nproof) T.fromId
      maybeApplicable =
        Prob.isRCProblem' prob
        <|> Prob.note (not . Trs.null $ Prob.dpComponents prob) " already containts dependency paris"
        -- <|> if useTuples then Prob.isInnermostProblem' prob else Nothing

      dpKind
        | Prob.strategy prob == Prob.Innermost = dpKind_ p
        | otherwise                            = WDP
      useTuples = isTuples dpKind

      (stricts, weaks) = flip evalState 0 $ do
        let
          defineds = Trs.definedSymbols (Prob.allComponents prob)
          dpsOf    = dependencyPairsOf dpKind defineds
        ss <- dpsOf (Prob.strictTrs prob)
        ws <- dpsOf (Prob.weakTrs prob)
        return (ss,ws)
      sDPs = fromTransformation stricts
      wDPs = fromTransformation weaks
      nsig = unite [Prob.signature prob, Trs.signature sDPs, Trs.signature wDPs]
        where unite = Sig.fromMap . M.unions . map Sig.toMap
      nprob = Prob.sanitiseDPGraph $ prob
        { Prob.startTerms = Prob.BasicTerms (Prob.markFun `S.map` Prob.defineds starts) (Prob.constructors starts)
        , Prob.signature  = nsig

        , Prob.strictDPs = sDPs
        , Prob.weakDPs   = wDPs
        , Prob.strictTrs = if useTuples then Trs.empty else Prob.strictTrs prob
        , Prob.weakTrs   = if useTuples then Prob.trsComponents prob else Prob.weakTrs prob }
        where starts = Prob.startTerms prob
      nproof = DependencyPairsProof
        { strictTransformation = stricts
        , weakTransformation   = weaks
        , dpKindUsed           = dpKind
        , newSignature         = nsig }


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty DependencyPairsProof where
  pretty proof = PP.vcat
    [ PP.text $ "We add the following " ++ info (dpKindUsed proof) ++ ":"
    , PP.empty
    , PP.text "Strict DPs"
    , PP.indent 2 $ PP.pretty (fromTransformation $ strictTransformation proof)
    , PP.text "Weak DPs"
    , PP.indent 2 $ PP.pretty (fromTransformation $ weakTransformation proof)
    , PP.empty
    , PP.text "and mark the set of starting terms." ]
    where
      info WDP  = "weak dependency pairs"
      info WIDP = "weak innermost dependency pairs"
      info DT   = "dependency tuples"


-- TODO: MS: there should be a new CeTA version that supports wdps
instance Xml.Xml DependencyPairsProof where
  toXml proof =
    Xml.elt "dp"
      [ Xml.elt (if isTuples (dpKindUsed proof) then "tuples" else "pairs") []
      , Xml.elt "strictDPs" [Xml.toXml (fromTransformation $ strictTransformation proof) ]
      , Xml.elt "weakDPs" [Xml.toXml (fromTransformation $ weakTransformation proof)] ]
  toCeTA proof
    | dpKindUsed proof /= DT = Xml.unsupported
    | otherwise =
      Xml.elt "dtTransformation"
        [ Xml.toCeTA $ Sig.filter Prob.isCompoundf (newSignature proof)
        , Xml.elt "strictDTs" (map ruleWith $ strictTransformation proof)
        , Xml.elt "weakDTs" (map ruleWith $ weakTransformation proof)
        -- FIXME: MS this should probably be marked starting terms;
        , Xml.elt "innermostLhss" (map lhss $ strictTransformation proof ++ weakTransformation proof) ]
      where
        ruleWith (old,new) = Xml.elt "ruleWithDT" [ Xml.toCeTA old, Xml.toCeTA new ]
        lhss (_, new)      = Xml.toCeTA (R.lhs new)


--- * instances ------------------------------------------------------------------------------------------------------

dpKindArg :: T.Argument T.Required DPKind
dpKindArg = T.arg
  `T.withName` "kind"
  `T.withHelp`  ["Specifies preferred kind of dependency pairs. Overrides to wdp for non-innermost problems."]
  `T.withDomain` fmap show [(minBound :: DPKind)..]

instance T.SParsable prob DPKind where
  parseS = T.mkEnumParser (undefined :: DPKind)

description :: [String]
description = ["Applies the (weak) dependency pairs transformation."]

dependencyPairsDeclaration :: T.Declaration ('[T.Argument 'T.Optional DPKind] T.:-> T.Strategy TrsProblem)
dependencyPairsDeclaration = T.declare "dependencyPairs" description (T.OneTuple dpArg) (T.Proc . DependencyPairs)
  where dpArg = dpKindArg `T.optional` WIDP

dependencyPairs :: T.Strategy TrsProblem
dependencyPairs = T.deflFun dependencyPairsDeclaration

dependencyPairs' :: DPKind -> T.Strategy TrsProblem
dependencyPairs' = T.declFun dependencyPairsDeclaration

weakDependencyPairs :: T.Strategy TrsProblem
weakDependencyPairs = dependencyPairs' WIDP

dependencyTuples :: T.Strategy TrsProblem
dependencyTuples = dependencyPairs' DT

