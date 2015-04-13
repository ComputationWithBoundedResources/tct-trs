module Tct.Trs.Data.RuleSelector
  (
  RuleSelector (..)
  -- * RuleSet Selectors
  , RuleSetSelector
  , selInter
  -- ** Constructors
  , selRules
  , selDPs
  , selStricts
  , selWeaks

  , selLeafWDG
  , selLeafCDG

  , selFromDG
  , selFromWDG
  , selFromCDG

  , selIndependentSG
  , selCycleIndependentSG
    -- ** Combinators
  -- * Selector Expressions
  , SelectorExpression (..)
  , ExpressionSelector
  , selectorArg
  -- ** Boolean Selectors
  , selAnyOf
  , selAllOf
  , selFirstAlternative
  -- ** Misc
  , rules
  , dpRules
  , trsRules
  ) where


import           Data.Typeable

import qualified Tct.Core.Common.Parser       as P
import qualified Tct.Core.Data                as T

import           Tct.Trs.Data.DependencyGraph (CDG, DG, DependencyGraph)
import qualified Tct.Trs.Data.DependencyGraph as DG
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.RuleSet         as Rs
import           Tct.Trs.Data.Trs             (SelectorExpression (..), Trs)
import qualified Tct.Trs.Data.Trs             as Trs


-- | This datatype is used to select a subset of rules recorded in a problem.
data RuleSelector f v a = RuleSelector
  { rsName   :: String            -- ^ Name of the rule selector.
  , rsSelect :: Prob.Problem f v -> a -- ^ Given a problem, computes an 'SelectorExpression' that
                                  -- determines which rules to select.
  } deriving Typeable

instance Show (RuleSelector f v a) where show = rsName

type RuleSetSelector f v    = RuleSelector f v (Rs.RuleSet f v)
type ExpressionSelector f v = RuleSelector f v (SelectorExpression f v)

selectorArg :: T.Argument 'T.Required (ExpressionSelector f v)
selectorArg = T.arg { T.argName  = "selector" }

-- FIXME: MS something is wrong; only accepts any all
instance T.SParsable prob (ExpressionSelector Prob.F Prob.V) where
  parseS = P.choice
    [ P.string (sym1 ++ sym2) >> return (comb prim)| (sym1,comb) <- combs, (sym2,prim) <- prims ]
    where
      combs =
        [ ("any ", selAnyOf)
        , ("all ", selAllOf)]
      prims =
        [ ("all", selDPs `selUnion` selRules)
        , ("dps", selDPs)
        , ("rules", selRules)
        , ("stricts", selStricts)
        , ("weaks", selWeaks) ]
        {-, ("first congruence", selFirstCongruence)                      -}
        {-, ("first strict congruence", selFirstStrictCongruence) ]-}



{-
-- | Inverses the selection.
selInverse :: RuleSetSelector -> RuleSetSelector
selInverse s = RuleSelector { rsName = "inverse of " ++ rsName s
                            , rsSelect = fn }
    where fn prob = Prob.Ruleset { Prob.sdp  = inv Prob.strictDPs Prob.sdp
                                 , Prob.wdp  = inv Prob.weakDPs Prob.wdp
                                 , Prob.strs = inv Prob.strictTrs Prob.strs
                                 , Prob.wtrs = inv Prob.weakTrs Prob.wtrs }
            where rs = rsSelect s prob
                  inv pfn rfn = pfn prob Trs.\\ rfn rs
-}

-- | Combine two rule-selectors component-wise.
selCombine :: (String -> String -> String) -> (Trs.Trs f v -> Trs.Trs f v -> Trs.Trs f v) -> RuleSetSelector f v -> RuleSetSelector f v -> RuleSetSelector f v
selCombine cn ctrs s1 s2 = RuleSelector { rsName = cn (rsName s1) (rsName s2)
                                        , rsSelect = fn }
        where fn prob = Rs.RuleSet { Rs.sdps = un Rs.sdps
                                   , Rs.wdps = un Rs.wdps
                                   , Rs.strs = un Rs.strs
                                   , Rs.wtrs = un Rs.wtrs }
                where rs1 = rsSelect s1 prob
                      rs2 = rsSelect s2 prob
                      un rfn = rfn rs1 `ctrs` rfn rs2

-- | Select union of selections of given rule-selectors.
selUnion :: (Ord f, Ord v) => RuleSetSelector f v -> RuleSetSelector f v -> RuleSetSelector f v
selUnion = selCombine (\ n1 n2 -> "union of " ++ n1 ++ " and " ++ n2) Trs.union

-- | Select intersection of selections of given rule-selectors.
selInter :: (Ord f, Ord v) => RuleSetSelector f v -> RuleSetSelector f v -> RuleSetSelector f v
selInter= selCombine (\ n1 n2 -> "intersect of " ++ n1 ++ " and " ++ n2) Trs.intersect


-- | Select rewrite rules, i.e., non dependency pair rules.
selRules :: RuleSetSelector f v
selRules = RuleSelector { rsName   = "rewrite-rules" , rsSelect = fn } where
  fn prob = Rs.RuleSet
    { Rs.sdps = Trs.empty
    , Rs.wdps = Trs.empty
    , Rs.strs = Prob.strictTrs prob
    , Rs.wtrs = Prob.weakTrs prob }

-- | Select dependency pairs.
selDPs :: RuleSetSelector f v
selDPs = RuleSelector { rsName = "DPs" , rsSelect = fn } where
  fn prob = Rs.RuleSet
    { Rs.sdps = Prob.strictDPs prob
    , Rs.wdps = Prob.weakDPs prob
    , Rs.strs = Trs.empty
    , Rs.wtrs = Trs.empty }

-- | Select strict rules.
selStricts :: RuleSetSelector f v
selStricts = RuleSelector { rsName = "strict-rules" , rsSelect = fn } where
  fn prob = Rs.RuleSet
    { Rs.sdps = Prob.strictDPs prob
    , Rs.wdps = Trs.empty
    , Rs.strs = Prob.strictTrs prob
    , Rs.wtrs = Trs.empty }

-- | Select strict rules.
selWeaks :: RuleSetSelector f v
selWeaks = RuleSelector { rsName = "weak-rules" , rsSelect = fn } where
  fn prob = Rs.RuleSet
    { Rs.sdps = Trs.empty
    , Rs.wdps = Prob.weakDPs prob
    , Rs.strs = Trs.empty
    , Rs.wtrs = Prob.weakTrs prob }

-- | Select from the dependency graph, using the given function.
-- The first parameter should specify a short name for the rule-selector.
selFromDG :: (DependencyGraph f v -> Rs.RuleSet f v) -> RuleSetSelector f v
selFromDG f = RuleSelector 
  { rsName   = "selected from DG"
  , rsSelect = f . Prob.dpGraph }

-- | Select from the dependency graph, using the given function.
-- The first parameter should specify a short name for the rule-selector.
selFromWDG :: (DG f v -> Rs.RuleSet f v) -> RuleSetSelector f v
selFromWDG f = RuleSelector 
  { rsName   = "selected from WDG"
  , rsSelect = f . Prob.dependencyGraph }

-- | Select from the congruence dependency graph, using the given function.
-- The first parameter should specify a short name for the rule-selector.
selFromCDG :: (CDG f v -> Rs.RuleSet f v) -> RuleSetSelector f v
selFromCDG f = RuleSelector 
  { rsName   = "selected from CWDG"
  , rsSelect = f . Prob.congruenceGraph }

{-
restrictToCongruences :: Prob.Ruleset -> [NodeId] -> CDG -> Prob.Ruleset
restrictToCongruences rs ns cdg = rs { Prob.sdp = Trs.fromRules [ r | (DG.StrictDP, r) <- rr]
                                     , Prob.wdp = Trs.fromRules [ r | (DG.WeakDP, r) <- rr] }
    where rr = allRulesFromNodes cdg ns

-- | Selects all rules from root-nodes in the congruence graph.
selFirstCongruence :: RuleSetSelector
selFirstCongruence = (selFromCWDG fn) { rsName =  "first congruence from CWDG"}
    where fn cdg = restrictToCongruences Prob.emptyRuleset (roots cdg) cdg

-- | Selects all rules from nodes @n@ of the CWDG that satisfy
-- (i) the node @n@ references at least one strict rule, and (ii)
-- there is no node between a root of the CWDG and @n@ containing a strict rule.
selFirstStrictCongruence :: RuleSetSelector
selFirstStrictCongruence = (selFromCWDG fn) { rsName = "first congruence with strict rules from CWDG" }
    where
      fn cdg = restrictToCongruences Prob.emptyRuleset ns cdg
        where
          ns = take 1 $ [ n | n <- bfsn (roots cdg) cdg
                            , any ((==) DG.StrictDP . fst) (allRulesFromNodes cdg [n])  ]

-}

selLeafWDG :: (Ord f, Ord v) => RuleSetSelector f v
selLeafWDG = (selFromWDG sel) { rsName = "leafs in WDG" } where
  sel wdg = Rs.emptyRuleSet { Rs.sdps = Trs.fromList . DG.asRules . DG.withNodeLabels' wdg $ DG.leafs wdg }

selLeafCDG :: (Ord f, Ord v) => RuleSetSelector f v
selLeafCDG = (selFromCDG sel) { rsName = "rules of CDG leaf" } where
  sel cdg       = Rs.emptyRuleSet { Rs.sdps = Trs.fromList . map DG.theRule $ leafRules cdg }
  leafRules cdg = DG.allRulesFromNodes cdg (DG.leafs cdg)

selIndependentSG :: (Ord f, Ord v) => RuleSetSelector f v
selIndependentSG = (selFromWDG f) { rsName = "independent sub-graph" } where
  f wdg = case DG.nodes wdg' of
    []  -> Rs.emptyRuleSet
    n:_ -> Rs.emptyRuleSet 
      { Rs.sdps = Trs.fromList . DG.asRules $ DG.filterStrict rs 
      , Rs.wdps = Trs.fromList . DG.asRules $ DG.filterWeak rs }
      where rs = DG.withNodeLabels' wdg' $ DG.reachablesBfs wdg' [n]
    where wdg' = DG.undirect wdg

selCycleIndependentSG :: (Ord f, Ord v) => RuleSetSelector f v
selCycleIndependentSG = (selFromWDG f) { rsName = "cycle independent sub-graph" } where
  f wdg = case DG.nodes wdg of
    []  -> Rs.emptyRuleSet
    n:_ -> Rs.emptyRuleSet 
      { Rs.sdps = Trs.fromList . DG.asRules $ DG.filterStrict rs 
      , Rs.wdps = Trs.fromList . DG.asRules $ DG.filterWeak rs }
      where 
        ns = walk wdg n [n]
        rs = DG.withNodeLabels' wdg ns
  walk wdg n ns
    | iscycle = ns ++ DG.reachablesBfs wdg [n]
    | otherwise = case succs of
      [] -> ns
      (m:_) -> walk wdg m $ m:ns
    where
      succs   = DG.successors wdg n
      iscycle = n `elem` (succs ++ DG.reachablesBfs wdg succs)

{-
selCloseWith :: (Problem -> DG) -> (String -> String) -> RuleSetSelector -> RuleSetSelector
selCloseWith mkWdg mkName rs =
  RuleSelector {rsName = mkName $ rsName rs
               , rsSelect = f }
  where
    f prob = sel { Prob.sdp = Trs.fromRules [r | (DG.StrictDP, r) <- fwclosed] `Trs.union` Prob.sdp sel
                 , Prob.wdp = Trs.fromRules [r | (DG.WeakDP, r) <- fwclosed] `Trs.union` Prob.wdp sel}
      where sel = rsSelect rs prob
            fwclosed = map snd $ DG.withNodeLabels' wdg $ DG.reachablesBfs wdg ns
            wdg = mkWdg prob
            ns = [ n | (n,(_,r)) <- lnodes wdg, Trs.member dps r ]
            dps = Prob.sdp sel `Trs.union` Prob.wdp sel

selCloseForward :: RuleSetSelector -> RuleSetSelector
selCloseForward = selCloseWith mkWdg (\n -> n ++ ", forward closed")
  where mkWdg = DG.estimatedDependencyGraph DG.defaultApproximation

selCloseBackward :: RuleSetSelector -> RuleSetSelector
selCloseBackward = selCloseWith mkWdg (\n -> n ++ ", backward closed")
  where mkWdg = DG.inverse . DG.estimatedDependencyGraph DG.defaultApproximation

-}

selAnyOf :: (Ord f, Ord v) => RuleSetSelector f v -> ExpressionSelector f v
selAnyOf s = RuleSelector { rsName = "any " ++ rsName s, rsSelect = f }
  where f prob = BigOr $ [ SelectDP d | d <- Trs.toList $ Rs.sdps rs `Trs.union` Rs.wdps rs]
                         ++ [ SelectTrs r | r <- Trs.toList $ Rs.strs rs `Trs.union` Rs.wtrs rs]
          where rs = rsSelect s prob

selAllOf :: (Ord f, Ord v) => RuleSetSelector f v -> ExpressionSelector f v
selAllOf s = RuleSelector { rsName = "any " ++ rsName s, rsSelect = f }
  where f prob = BigAnd $ [ SelectDP d | d <- Trs.toList $ Rs.sdps rs `Trs.union` Rs.wdps rs]
                         ++ [ SelectTrs r | r <- Trs.toList $ Rs.strs rs `Trs.union` Rs.wtrs rs]
          where rs = rsSelect s prob

{-
-- | Conjunction
selAnd :: [ExpressionSelector] -> ExpressionSelector
selAnd ss = RuleSelector { rsName = "all [" ++ concat (intersperse ", " [rsName s | s <- ss])  ++ "]"
                         , rsSelect = \ prob -> BigAnd [rsSelect s prob | s <- ss] }

-- | Disjunction
selOr :: [ExpressionSelector] -> ExpressionSelector
selOr ss = RuleSelector { rsName = "any [" ++ concat (intersperse ", " [rsName s | s <- ss])  ++ "]"
                        , rsSelect = \ prob -> BigOr [rsSelect s prob | s <- ss] }
-}

-- | Selects the first alternative from the given rule selector.
selFirstAlternative :: (Ord f, Ord v) => ExpressionSelector f v -> ExpressionSelector f v
selFirstAlternative rs = RuleSelector 
  { rsName = "first alternative of " ++ rsName rs
  , rsSelect = \ prob -> 
    let (dps, trs) = selectFirst $ rsSelect rs prob
    in BigAnd $ [SelectDP d | d <- Trs.toList dps] ++ [SelectTrs r | r <- Trs.toList trs] }

  where 
    selectFirst (BigAnd ss)     = (Trs.unions dpss, Trs.unions trss)
      where (dpss, trss) = unzip [selectFirst sel | sel <- ss]
    selectFirst (BigOr [])      = (Trs.empty,Trs.empty)
    selectFirst (BigOr (sel:_)) = selectFirst sel
    selectFirst (SelectDP d)    = (Trs.singleton d, Trs.empty)
    selectFirst (SelectTrs r)   = (Trs.empty, Trs.singleton r)


-- | returns the pair of dps and rules mentioned in a 'SelectorExpression'
rules :: (Ord f, Ord v) => SelectorExpression f v -> (Trs f v, Trs f v)
rules e =
  case e of
    BigAnd ss   -> rules' ss
    BigOr ss    -> rules' ss
    SelectDP d  -> (Trs.singleton d, Trs.empty)
    SelectTrs r -> (Trs.empty, Trs.singleton r)
  where rules' ss = let (dpss,trss) = unzip (rules `fmap` ss) in (Trs.unions dpss, Trs.unions trss)

-- | dpRules = fst . rules
dpRules :: (Ord f, Ord v) => SelectorExpression f v -> Trs f v
dpRules = fst . rules

-- | trsRules = snd . rules
trsRules :: (Ord f, Ord v) => SelectorExpression f v -> Trs f v
trsRules = snd . rules

