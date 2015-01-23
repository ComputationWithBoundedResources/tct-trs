-- | This module implements the /weak dependency pair/ and the /dependency tuples/ transformation.
module Tct.Trs.Method.DP.DependencyPairs
  (
  dependencyPairs
  , dependencyPairsDeclaration
  , dependencyTuples
  , dependencyTuplesDeclaration
  ) where

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
import qualified Tct.Trs.Data.Trs            as Trs


-- FIXME: 
-- MS Compound Symbols should have identifier component
-- it is necessary to compute a fresh symbol

subtermsWDP :: Ord f => S.Set f -> R.Term f v -> [R.Term f v]
subtermsWDP defineds s@(R.Fun f ss)
  | f `S.member` defineds = [s]
  | otherwise             = concatMap (subtermsWDP defineds) ss
subtermsWDP _ v = [v]

subtermsWIDP :: Ord f => S.Set f -> R.Term f v -> [R.Term f v]
subtermsWIDP defineds s@(R.Fun f ss)
  | f `S.member` defineds = [s]
  | otherwise             = concatMap (subtermsWDP defineds) ss
subtermsWIDP _ _ = []

subtermsWDT :: Ord f => S.Set f -> R.Term f v -> [R.Term f v]
subtermsWDT defineds s@(R.Fun f ss)
  | f `S.member` defineds = s :subs
  | otherwise             = subs
  where subs = concatMap (subtermsWDT defineds) ss
subtermsWDT _ _ = []

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

dependencyPairsOf :: Bool -> Prob.Strategy -> Trs F V -> State Int [Transformation F V]
dependencyPairsOf useTuples strat trs
  | useTuples               = markRules (subtermsWDT defineds) trs
  | strat == Prob.Innermost = markRules (subtermsWIDP defineds) trs
  | otherwise               = markRules (subtermsWDP defineds) trs
  where defineds = Trs.definedSymbols trs


--- * processor ------------------------------------------------------------------------------------------------------

data DPProcessor = DPProc { useTuples_ :: Bool } deriving Show

data DPProof = DPProof
  { strictTransformation :: [Transformation F V]
  , weakTransformation   :: [Transformation F V]
  , tuplesUsed           :: Bool
  , newSignature         :: Signature F }
  deriving Show

instance T.Processor DPProcessor where
  type ProofObject DPProcessor = ApplicationProof DPProof
  type Problem DPProcessor     = TrsProblem
  solve p prob                 = return . T.resultToTree p prob $ solveDP p prob

solveDP :: (T.Forking p ~ T.Id, T.Problem p ~ TrsProblem, T.ProofObject p ~ ApplicationProof DPProof) 
  => DPProcessor -> TrsProblem -> T.Result p
solveDP p prob
  | not (Trs.null $ Prob.dpComponents prob)                 = T.Fail (Inapplicable "already contains dependency pairs")
  | useTuples_ p && (Prob.strategy prob /= Prob.Innermost) = T.Fail (Inapplicable "not an innermost problem")
solveDP p prob = case Prob.startTerms prob of
  (Prob.AllTerms _)       -> T.Fail (Inapplicable "not an rc problem")
  (Prob.BasicTerms ds cs) -> T.Success (T.toId nprob) (Applicable nproof) T.fromId
    where
      useTuples = useTuples_ p
      (stricts, weaks) = flip evalState 0 $ do
        ss <- dependencyPairsOf useTuples (Prob.strategy prob) (Prob.strictTrs prob)
        ws <- dependencyPairsOf useTuples (Prob.strategy prob) (Prob.weakTrs prob)
        return (ss,ws)
      sDPs = fromTransformation stricts
      wDPs = fromTransformation weaks
      nsig = unite [Prob.signature prob, Trs.signature sDPs, Trs.signature wDPs]
        where unite = Signature . M.unions . map runSignature
      nprob = prob
        { Prob.startTerms = Prob.BasicTerms (Prob.markFun `S.map` ds) cs
        , Prob.signature  = nsig

        , Prob.strictDPs = sDPs
        , Prob.weakDPs   = wDPs
        , Prob.strictTrs = if useTuples then Trs.empty else Prob.strictTrs prob
        , Prob.weakTrs   = if useTuples then Prob.trsComponents prob else Prob.weakTrs prob }
      nproof = DPProof
        { strictTransformation = stricts
        , weakTransformation   = weaks
        , tuplesUsed   = useTuples
        , newSignature = nsig }



--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty DPProof where
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

instance Xml.Xml DPProof where
  toXml proof =
    Xml.elt "dp"
      [ Xml.elt (if tuplesUsed proof then "tuples" else "pairs") []
      , Xml.elt "strictDPs" [Xml.toXml (fromTransformation $ strictTransformation proof) ]
      , Xml.elt "weakDPs" [Xml.toXml (fromTransformation $ weakTransformation proof)] ]
  toCeTA proof
    | not (tuplesUsed proof) = Xml.elt "unknown" []
    | otherwise = 
      Xml.elt "dtTransformation"
        [ Xml.toXml (M.filterWithKey (\k _ -> Prob.isCompoundf k) `Trs.onSignature` newSignature proof)
        , Xml.elt "strictDTs" (map ruleWith $ strictTransformation proof)
        , Xml.elt "weakDTs" (map ruleWith $ weakTransformation proof)
        , Xml.elt "innermostLhss" (map lhss $ strictTransformation proof ++ weakTransformation proof) ] --TODO: MS left hand sides of all components?
      where 
        ruleWith (old,new) = Xml.elt "ruleWithDT" [ Xml.toXml old, Xml.toXml new ]
        lhss (_, new)      = Xml.toXml (R.lhs new)


--- * instances ------------------------------------------------------------------------------------------------------

dependencyPairs :: T.Strategy TrsProblem
dependencyPairs = T.Proc (DPProc False)

dependencyPairsDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
dependencyPairsDeclaration = T.declare "dependencyPairs" description () dependencyPairs
  where description = [ "Applies the (weak) dependency pairs transformation." ]

dependencyTuples :: T.Strategy TrsProblem
dependencyTuples = T.Proc (DPProc True)

dependencyTuplesDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
dependencyTuplesDeclaration = T.declare "dependencyTuples" description () dependencyTuples
  where description = [ "Applies the dependency tuples transformation." ]

