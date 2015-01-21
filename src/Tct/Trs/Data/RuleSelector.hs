module Tct.Trs.Data.RuleSelector
  (
  RuleSelector (..)
  -- * RuleSet Selectors
  , RuleSetSelector
  -- ** Constructors
  , selRules
  , selDPs
  , selStricts
  , selWeaks
    -- ** Combinators
  -- * Selector Expressions
  , SelectorExpression (..)
  , ExpressionSelector
  , selectorArg
  -- ** Boolean Selectors
  , selAnyOf
  , selAllOf
  -- ** Misc
  , rules
  ) where


import           Data.Typeable

import qualified Tct.Core.Common.Parser as P
import qualified Tct.Core.Data          as T

import qualified Tct.Trs.Data.Problem   as Prob
import           Tct.Trs.Data.Trs       (SelectorExpression (..), Trs)
import qualified Tct.Trs.Data.Trs       as Trs


-- | This datatype is used to select a subset of rules recorded in a problem.
data RuleSelector a = RuleSelector
  { rsName   :: String            -- ^ Name of the rule selector.
  , rsSelect :: Prob.Problem -> a -- ^ Given a problem, computes an 'SelectorExpression' that
                                  -- determines which rules to select.
  } deriving Typeable

instance Show (RuleSelector a) where show = rsName

type RuleSetSelector f v    = RuleSelector (Prob.Ruleset f v)
type ExpressionSelector f v = RuleSelector (SelectorExpression f v)

selectorArg :: T.Argument 'T.Required (ExpressionSelector f v)
selectorArg = T.arg { T.argName  = "selector" }

instance T.SParsable prob (ExpressionSelector Prob.Fun Prob.Var) where
  parseS = P.choice
    [ P.symbol (sym1 ++ sym2) >> return (comb prim)| (sym1,comb) <- combs, (sym2,prim) <- prims ]
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
        where fn prob = Prob.Ruleset { Prob.sdp  = un Prob.sdp
                                     , Prob.wdp  = un Prob.wdp
                                     , Prob.strs = un Prob.strs
                                     , Prob.wtrs = un Prob.wtrs }
                where rs1 = rsSelect s1 prob
                      rs2 = rsSelect s2 prob
                      un rfn = rfn rs1 `ctrs` rfn rs2

-- | Select union of selections of given rule-selectors.
selUnion :: (Ord f, Ord v) => RuleSetSelector f v -> RuleSetSelector f v -> RuleSetSelector f v
selUnion = selCombine (\ n1 n2 -> "union of " ++ n1 ++ " and " ++ n2) Trs.union

{-
-- | Select intersection of selections of given rule-selectors.
selInter :: RuleSetSelector -> RuleSetSelector -> RuleSetSelector
selInter= selCombine (\ n1 n2 -> "intersect of " ++ n1 ++ " and " ++ n2) Trs.intersect
-}

-- | Select rewrite rules, i.e., non dependency pair rules.
selRules :: RuleSetSelector Prob.Fun Prob.Var
selRules = RuleSelector { rsName   = "rewrite-rules" , rsSelect = fn } where
  fn prob = Prob.Ruleset
    { Prob.sdp  = Trs.empty
    , Prob.wdp  = Trs.empty
    , Prob.strs = Prob.strictTrs prob
    , Prob.wtrs = Prob.weakTrs prob }

-- | Select dependency pairs.
selDPs :: RuleSetSelector Prob.Fun Prob.Var
selDPs = RuleSelector { rsName = "DPs" , rsSelect = fn } where
  fn prob = Prob.Ruleset
    { Prob.sdp  = Prob.strictDPs prob
    , Prob.wdp  = Prob.weakDPs prob
    , Prob.strs = Trs.empty
    , Prob.wtrs = Trs.empty }

-- | Select strict rules.
selStricts :: RuleSetSelector Prob.Fun Prob.Var
selStricts = RuleSelector { rsName = "strict-rules" , rsSelect = fn } where
  fn prob = Prob.Ruleset
    { Prob.sdp  = Prob.strictDPs prob
    , Prob.wdp  = Trs.empty
    , Prob.strs = Prob.strictTrs prob
    , Prob.wtrs = Trs.empty }

-- | Select strict rules.
selWeaks :: RuleSetSelector Prob.Fun Prob.Var
selWeaks = RuleSelector { rsName = "weak-rules" , rsSelect = fn } where
  fn prob = Prob.Ruleset
    { Prob.sdp  = Trs.empty
    , Prob.wdp  = Prob.weakDPs prob
    , Prob.strs = Trs.empty
    , Prob.wtrs = Prob.weakTrs prob }

{-
-- | Select from the dependency graph, using the given function.
-- The first parameter should specify a short name for the rule-selector.
selFromWDG :: (DG -> Prob.Ruleset) -> RuleSetSelector
selFromWDG f = RuleSelector { rsName = "selected from WDG"
                              , rsSelect = \ prob -> f (dg prob) }
    where dg = DG.estimatedDependencyGraph DG.defaultApproximation

-- | Select from the congruence dependency graph, using the given function.
-- The first parameter should specify a short name for the rule-selector.
selFromCWDG :: (CDG -> Prob.Ruleset) -> RuleSetSelector
selFromCWDG f = RuleSelector { rsName = "selected from CWDG"
                             , rsSelect = \ prob -> f (dg prob) }
    where dg = toCongruenceGraph . DG.estimatedDependencyGraph DG.defaultApproximation

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

selLeafCWDG :: RuleSetSelector
selLeafCWDG = (selFromCWDG sel) { rsName = "rules of CWDG leaf" }
  where
    sel cwdg = Prob.emptyRuleset { Prob.sdp = Trs.fromRules [ r | (_, r) <- leafRules cwdg] }
    leafRules cwdg = DG.allRulesFromNodes cwdg (DG.leafs cwdg)

selLeafWDG :: RuleSetSelector
selLeafWDG = (selFromWDG sel) { rsName = "leafs in WDG" }
  where
    sel wdg = Prob.emptyRuleset { Prob.sdp = Trs.fromRules [ r | (_, r) <- leafRules wdg] }
    leafRules wdg = [r | (_,r) <- DG.withNodeLabels' wdg $ DG.leafs wdg]

selIndependentSG :: RuleSetSelector
selIndependentSG = (selFromWDG f) { rsName = "independent sub-graph" }
  where
    f wdg =
      case DG.nodes wdg' of
        [] -> Prob.emptyRuleset
        n:_ -> Prob.emptyRuleset { Prob.sdp = Trs.fromRules [r | (_,(DG.StrictDP, r)) <- rs]
                                 , Prob.wdp = Trs.fromRules [r | (_,(DG.WeakDP, r)) <- rs] }
          where rs = DG.withNodeLabels' wdg' $ DG.reachablesBfs wdg' [n]
      where wdg' = DG.undirect wdg

selCycleIndependentSG :: RuleSetSelector
selCycleIndependentSG = (selFromWDG f) { rsName = "cycle independent sub-graph" }
  where
    f wdg =
      case DG.roots wdg of
        [] -> Prob.emptyRuleset
        n:_ -> Prob.emptyRuleset { Prob.sdp = Trs.fromRules [r | (_,(DG.StrictDP, r)) <- rs]
                                 , Prob.wdp = Trs.fromRules [r | (_,(DG.WeakDP, r)) <- rs] }
          where ns = walk n [n]
                rs = DG.withNodeLabels' wdg ns
      where
        walk n ns
          | iscycle = ns ++ DG.reachablesBfs wdg [n]
          | otherwise =
            case succs of
              [] -> ns
              (m:_) -> walk m $ m:ns
          where
            iscycle = n `elem` (succs ++ DG.reachablesBfs wdg succs)
            succs = DG.successors wdg n

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
  where f prob = BigOr $ [ SelectDP d | d <- Trs.toList $ Prob.sdp rs `Trs.union` Prob.wdp rs]
                         ++ [ SelectTrs r | r <- Trs.toList $ Prob.strs rs `Trs.union` Prob.wtrs rs]
          where rs = rsSelect s prob

selAllOf :: (Ord f, Ord v) => RuleSetSelector f v -> ExpressionSelector f v
selAllOf s = RuleSelector { rsName = "any " ++ rsName s, rsSelect = f }
  where f prob = BigAnd $ [ SelectDP d | d <- Trs.toList $ Prob.sdp rs `Trs.union` Prob.wdp rs]
                         ++ [ SelectTrs r | r <- Trs.toList $ Prob.strs rs `Trs.union` Prob.wtrs rs]
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


-- | Selects the first alternative from the given rule selector.
selFirstAlternative :: ExpressionSelector -> ExpressionSelector
selFirstAlternative rs = RuleSelector { rsName = "first alternative of " ++ rsName rs ,
                                        rsSelect = \ prob -> let (dps, trs) = selectFirst $ rsSelect rs prob
                                                             in BigAnd $ [SelectDP d | d <- Trs.rules dps]
                                                                ++ [SelectTrs r | r <- Trs.rules trs]
                                      }
  where selectFirst (BigAnd ss)   = (Trs.unions dpss, Trs.unions trss)
          where (dpss, trss) = unzip [selectFirst sel | sel <- ss]
        selectFirst (BigOr [])      = (Trs.empty,Trs.empty)
        selectFirst (BigOr (sel:_)) = selectFirst sel
        selectFirst (SelectDP d)    = (Trs.singleton d, Trs.empty)
        selectFirst (SelectTrs r)   = (Trs.empty, Trs.singleton r)
-}

-- | returns the pair of dps and rules mentioned in a 'SelectorExpression'
rules :: (Ord f, Ord v) => SelectorExpression f v -> (Trs f v, Trs f v)
rules e =
  case e of
    BigAnd ss   -> rules' ss
    BigOr ss    -> rules' ss
    SelectDP d  -> (Trs.singleton d, Trs.empty)
    SelectTrs r -> (Trs.empty, Trs.singleton r)
  where rules' ss = let (dpss,trss) = unzip [rules sel | sel <- ss] in (Trs.unions dpss, Trs.unions trss)


{-onSelectedRequire :: Boolean a => SelectorExpression -> (Bool -> Rule -> a) -> a-}
{-onSelectedRequire (SelectDP r) f  = f True r-}
{-onSelectedRequire (SelectTrs r) f = f False r-}
{-onSelectedRequire (BigAnd es) f   = bigAnd [ onSelectedRequire e f | e <- es]-}
{-onSelectedRequire (BigOr es) f    = bigOr [ onSelectedRequire e f | e <- es]-}

