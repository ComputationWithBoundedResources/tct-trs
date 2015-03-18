-- | This module implements the /Weak Dependency Pairs/ and the /Dependency Tuples/ processor.
module Tct.Trs.Method.DP.DependencyPairs
  ( dependencyPairsDeclaration
  , dependencyPairs
  , dependencyTuplesDeclaration
  , dependencyTuples
  ) where


import           Control.Applicative         ((<|>))
import           Control.Monad.State.Strict
import qualified Data.Traversable            as F

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
import qualified Tct.Trs.Data.Trs            as Trs
import qualified Tct.Trs.Data.Signature      as Sig


-- FIXME:
-- MS Compound Symbols should have identifier component
-- it is necessary to compute a fresh symbol for pretty printing only

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
subtermsWDT :: Ord f => Symbols f -> R.Term f v -> [R.Term f v]
subtermsWDT defineds s@(R.Fun f ss)
  | f `S.member` defineds = s :subs
  | otherwise             = subs
  where subs = concatMap (subtermsWDT defineds) ss
subtermsWDT _ _ = []

-- MS: we follow tct2 and Com(t)=Com(t) for singleton argument list t; hence rhs always have a compound symbol
markRule :: (R.Term F V -> [R.Term F V]) -> R.Rule F V -> State Int (R.Rule F V)
markRule subtermsOf (R.Rule lhs rhs)= do
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

dependencyPairsOf :: Bool -> Prob.Strategy -> Symbols F -> Trs F V -> State Int [Transformation F V]
dependencyPairsOf useTuples strat defineds trs
  | useTuples               = markRules (subtermsWDT defineds) trs
  | strat == Prob.Innermost = markRules (subtermsWIDP defineds) trs
  | otherwise               = markRules (subtermsWDP defineds) trs


--- * processor ------------------------------------------------------------------------------------------------------

data DependencyPairs = DependencyPairs { useTuples_ :: Bool } deriving Show

data DependencyPairsProof = DependencyPairsProof
  { strictTransformation :: [Transformation F V]
  , weakTransformation   :: [Transformation F V]
  , tuplesUsed           :: Bool
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
        <|> if useTuples then Prob.isInnermostProblem' prob else Nothing

      (stricts, weaks) = flip evalState 0 $ do
        let defineds = Trs.definedSymbols (Prob.allComponents prob)
        ss <- dependencyPairsOf useTuples (Prob.strategy prob) defineds (Prob.strictTrs prob)
        ws <- dependencyPairsOf useTuples (Prob.strategy prob) defineds (Prob.weakTrs prob)
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
      nproof = DependencyPairsProof
        { strictTransformation = stricts
        , weakTransformation   = weaks
        , tuplesUsed   = useTuples
        , newSignature = nsig }

      useTuples = useTuples_ p
      starts = Prob.startTerms prob


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty DependencyPairsProof where
  pretty proof
    = PP.vcat
      [ PP.text $ "We add the following "
        ++ (if tuplesUsed proof then "dependency tuples" else "weak dependency pairs") ++ ":"
      , PP.empty
      , PP.text "Strict DPs"
      , PP.indent 2 $ PP.pretty (fromTransformation $ strictTransformation proof)
      , PP.text "Weak DPs"
      , PP.indent 2 $ PP.pretty (fromTransformation $ weakTransformation proof)
      , PP.empty
      , PP.text "and mark the set of starting terms." ]

instance Xml.Xml DependencyPairsProof where
  toXml proof =
    Xml.elt "dp"
      [ Xml.elt (if tuplesUsed proof then "tuples" else "pairs") []
      , Xml.elt "strictDPs" [Xml.toXml (fromTransformation $ strictTransformation proof) ]
      , Xml.elt "weakDPs" [Xml.toXml (fromTransformation $ weakTransformation proof)] ]
  toCeTA proof
    | not (tuplesUsed proof) = Xml.elt "unknown" []
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

dependencyPairsDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
dependencyPairsDeclaration = T.declare "dependencyPairs" description () (T.Proc $ DependencyPairs False)
  where description = [ "Applies the (weak) dependency pairs transformation." ]

dependencyPairs :: T.Strategy TrsProblem
dependencyPairs = T.declFun dependencyPairsDeclaration

dependencyTuplesDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
dependencyTuplesDeclaration = T.declare "dependencyTuples" description () (T.Proc $ DependencyPairs True)
  where description = [ "Applies the dependency tuples transformation." ]

dependencyTuples :: T.Strategy TrsProblem
dependencyTuples = T.declFun dependencyTuplesDeclaration

