-- | This module implements the /weak dependency pair/ and the /dependency tuples/ transformation.
module Tct.Trs.Method.DP.DependencyPairs
  (
  dependencyPairs
  , dependencyTuples
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

import           Tct.Trs.Data.Problem        (AFun (..), Fun, Problem, Signature, Trs, Var, Rule)
import qualified Tct.Trs.Data.Problem        as Prob
import qualified Tct.Trs.Data.Trs            as Trs
import qualified Tct.Trs.Data.Xml            as Xml


-- FIXME: 
-- MS Compound Symbols should have identifier component
-- it is necessary to compute a fresh symbol

dependencyPairs :: T.Strategy Problem
dependencyPairs = T.Proc (DPProc False)

dependencyTuples :: T.Strategy Problem
dependencyTuples = T.Proc (DPProc True)


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

markFun :: AFun f -> AFun f
markFun (TrsFun f) = DpFun f
markFun _          = error "Tct.Trs.Method.DP.dependencyPairs.markRule: not a trs symbol"


markRule :: (R.Term (AFun f) v -> [R.Term (AFun f) v]) -> R.Rule (AFun f) v -> State Int (R.Rule (AFun f) v)
markRule subtermsOf (R.Rule lhs rhs)= do
  i <- modify succ >> get
  return $ R.Rule (markTerm lhs) (R.Fun (ComFun i) (map markTerm $ subtermsOf rhs))
  where
    markTerm (R.Fun f fs) = R.Fun (markFun f) fs
    markTerm v = v

-- | (Original Rule, DP Rule)
type Transformation = (Rule, Rule)

fromTransformation :: [Transformation] -> Trs
fromTransformation = Trs.fromList . snd . unzip

markRules :: (R.Term Fun Var -> [R.Term Fun Var]) -> Trs -> State Int [Transformation]
markRules subtermsOf trs = F.mapM (\r -> markRule subtermsOf r >>= \r' -> return (r,r')) (Trs.toList trs)

dependencyPairsOf :: Bool -> Prob.Strategy -> Trs -> State Int [Transformation]
dependencyPairsOf useTuples strat trs
  | useTuples               = markRules (subtermsWDT defineds) trs
  | strat == Prob.Innermost = markRules (subtermsWIDP defineds) trs
  | otherwise               = markRules (subtermsWDP defineds) trs
  where defineds = Trs.definedSymbols trs


data DPProcessor = DPProc { useTuples_ :: Bool } deriving Show

data DPProof = DPProof
  { strictTransformation :: [Transformation]
  , weakTransformation   :: [Transformation]
  , tuplesUsed           :: Bool
  , newSignature         :: Signature }
  deriving Show

instance T.Processor DPProcessor where
  type ProofObject DPProcessor = ApplicationProof DPProof
  type Problem DPProcessor     = Prob.Problem
  solve p prob = return . T.resultToTree p prob $ solveDP p prob

solveDP :: (T.Forking p ~ T.Id, T.Problem p ~ Problem, T.ProofObject p ~ ApplicationProof DPProof) => DPProcessor -> Problem -> T.Result p
solveDP p prob
  | not (Trs.null $ Prob.dpComponents prob)                 = T.Fail (Inapplicable "already contains dependency pairs")
  | useTuples_ p && (Prob.strategy prob /= Prob.Innermost) = T.Fail (Inapplicable "not an innermost problem")
solveDP p prob = case Prob.startTerms prob of
  (Prob.AllTerms _)       -> T.Fail (Inapplicable "not an rc problem")
  (Prob.BasicTerms ds cs) -> T.Success (T.Id nprob) (Applicable nproof) (\(T.Id c)  -> c)
    where
      useTuples = useTuples_ p
      (stricts, weaks) = flip evalState 0 $ do
        ss <- dependencyPairsOf useTuples (Prob.strategy prob) (Prob.strictTrs prob)
        ws <- dependencyPairsOf useTuples (Prob.strategy prob) (Prob.weakTrs prob)
        return (ss,ws)
      sDPs = fromTransformation stricts
      wDPs = fromTransformation weaks
      nsig = M.unions [Prob.signature prob, Trs.signature sDPs, Trs.signature wDPs]
      nprob = prob
        { Prob.startTerms = Prob.BasicTerms (markFun `S.map` ds) cs
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


----------------------------------------------------------------------------------------------------------------------
--  proofdata

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
      , Xml.elt "strictDPs" [Xml.rules (fromTransformation $ strictTransformation proof) ]
      , Xml.elt "weakDPs" [Xml.rules (fromTransformation $ weakTransformation proof)] ]
  -- FXIME: for some unknown reason toCeTA is not called; whereas it works for eg empty processor
  toCeTA proof
    | not (tuplesUsed proof) = Xml.elt "unknown" []
    | otherwise = 
      Xml.elt "dtTransformation"
        [ Xml.signature (M.filterWithKey (\k _ -> isCompound k) $ newSignature proof)
        , Xml.elt "strictDTs" (map ruleWith $ strictTransformation proof)
        , Xml.elt "weakDTs" (map ruleWith $ weakTransformation proof)
        , Xml.elt "innermostLhss" (map lhss $ strictTransformation proof ++ weakTransformation proof) ] --TODO: MS left hand sides of all components?
      where 
        isCompound (ComFun _) = True
        isCompound _ = False
        ruleWith (old,new) = Xml.elt "ruleWithDT" [ Xml.rule old, Xml.rule new ]
        lhss (_, new)      = Xml.term (R.lhs new)

