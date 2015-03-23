module Tct.Trs.Data.DependencyGraph
  ( module Gr
  -- * dependency graph
  , DependencyGraph (..)
  , DG, DGNode (..)
  , estimatedDependencyGraph
  , empty
  , asRules
  , asNodedRules
  , withRulesPair
  , withRulesPair'
  , filterWeak
  , filterStrict

  -- * congruence graph
  , CDG, CDGNode (..)
  , toCongruenceGraph
  , isCyclicNode

  , congruence
  , allRulesFromNode
  , allRulesFromNodes
  , allRulesPairFromNodes
  ) where


import           Control.Monad.State.Strict
import           Data.Function               (on)
import qualified Data.List                   as L
import           Data.Maybe                  (fromMaybe, isNothing, isJust)
import           Data.Monoid

import qualified Data.Rewriting.Rule         as R (Rule (..))
import qualified Data.Rewriting.Rules        as RS
import qualified Data.Rewriting.Substitution as R
import qualified Data.Rewriting.Term         as R

import qualified Tct.Core.Common.Pretty      as PP
import qualified Tct.Core.Common.Xml         as Xml

import           Tct.Common.Graph            as Gr hiding (empty)
import qualified Tct.Common.Graph            as Gr (empty)

import qualified Tct.Trs.Data.ProblemKind    as Prob
import qualified Tct.Trs.Data.Rewriting      as R
import qualified Tct.Trs.Data.RuleSet        as Rs
import qualified Tct.Trs.Data.Trs            as Trs


--- * dependency graph -----------------------------------------------------------------------------------------------

data DGNode f v = DGNode
  { theRule  :: R.Rule f v
  , isStrict :: Bool }
  deriving (Eq, Show)

type DG f v = Graph (DGNode f v) Int

data CDGNode f v = CDGNode
  { theSCC   :: [(NodeId, DGNode f v)]
  , isCyclic :: Bool }
  deriving (Eq, Show)

type CDG f v = Graph (CDGNode f v) (R.Rule f v, Int)

data DependencyGraph f v = DependencyGraph
  { dependencyGraph :: DG f v
  , congruenceGraph :: CDG f v
  } deriving (Eq, Show)

empty :: DependencyGraph f v
empty = DependencyGraph Gr.empty Gr.empty


asRules :: [(n, DGNode f v)] -> [R.Rule f v]
asRules = map (theRule . snd)

asNodedRules :: [(n, DGNode f v)] -> [(n, R.Rule f v)]
asNodedRules = map (fmap theRule)

filterWeak :: [(n, DGNode f v)] -> [(n, DGNode f v)]
filterWeak = filter (not . isStrict . snd)

filterStrict :: [(n, DGNode f v)] -> [(n, DGNode f v)]
filterStrict = filter (isStrict . snd)

withRulesPair :: [(n, DGNode f v)] -> ([(n, R.Rule f v)], [(n, R.Rule f v)])
withRulesPair = foldl k ([],[])
  where k (srs,wrs) (n,nl) = if isStrict nl then ((n,theRule nl):srs, wrs) else (srs,(n,theRule nl):wrs)

withRulesPair' :: [(n, DGNode f v)] -> ([n], [R.Rule f v], [R.Rule f v])
withRulesPair' = foldl k ([],[],[])
  where k (ns,srs,wrs) (n,nl) = if isStrict nl then (n:ns,theRule nl:srs, wrs) else (n:ns,srs,theRule nl:wrs)



--- ** estimated dependency graph -------------------------------------------------------------------------------------

estimatedDependencyGraph :: (Ord f, Ord v) => Rs.RuleSet f v -> Prob.Strategy -> DependencyGraph f v
estimatedDependencyGraph rs strat  = DependencyGraph wdg cdg where
  wdg = estimatedDependencyGraph' rs strat
  cdg = toCongruenceGraph wdg

estimatedDependencyGraph' :: (Ord v, Ord f, Num b, Enum b) => Rs.RuleSet f v -> Prob.Strategy -> Graph (DGNode f v) b
estimatedDependencyGraph' rs strat = mkGraph ns es
  where
    (strictDPs, weakDPs) = (Trs.toList $ Rs.sdps rs, Trs.toList $ Rs.wdps rs)
    ns = zip [1..] $ [ DGNode r True | r <- strictDPs ] ++ [ DGNode r False | r <- weakDPs ]
    es = [ (n1, n2, i) | (n1,r1) <- ns, (n2,r2) <- ns, i <- theRule r1 `edgesTo` theRule r2 ]

    (R.Rule s t) `edgesTo` (R.Rule u v)=
      case t of
        R.Var _    -> []
        R.Fun _ ts -> [ i | (i,ti) <- zip [1..] ts, (s,ti) `edgeTo` (u,v) ]

    (s,t) `edgeTo` (u,_) =
      let
        s'   = R.rename (Right . R.Old) s
        u'   = R.rename (Right . R.Old) u
        t' f = R.rename Left . f $ R.rename R.Old t

        trsComponents = Trs.toList (Rs.strs rs) ++ Trs.toList (Rs.wtrs rs)
        lhss          = RS.lhss trsComponents
      in
      case strat of
          Prob.Innermost -> case R.unify (t' $ R.icap trsComponents) u' of
            Nothing  -> False
            Just mgu -> isINF (R.apply mgu s') && isINF (R.apply mgu u')
              where isINF v = all isNothing [ l `R.match` vi | l <- lhss, vi <- R.properSubterms v ]

          _              -> isJust $ R.unify (t' $ R.tcap trsComponents) u'


      --   unifyNF t1 t2 = case R.unify t1 t2 of
      --     Just  d -> isQNF (R.apply d s') && isQNF (R.apply d u')
      --     Nothing -> False
      --   isQNF v = all isNothing [ vi `R.match` l | l <- qsLhss, vi <- R.properSubterms v ]
      --
      --   qsLhss = case strat of
      --     Prob.Innermost -> lhss
      --     _              -> []
      --
      -- tcap <- R.qcapM lhss qsLhss [s',t'] t'
      -- if unifyNF tcap u'
      --   then R.tcapM rhss u' >>= \ucap -> return (unifyNF ucap t') -- what does this
      --   else return False


--- * congruence graph -----------------------------------------------------------------------------------------------

toCongruenceGraph :: DG f v -> CDG f v
toCongruenceGraph gr = mkGraph ns es
  where
    ns    = zip [1..] [sccNode scc | scc <- sccs gr]
    sccNode scc = CDGNode
      { theSCC   = [ (n, lookupNodeLabel' gr n) | n <- scc]
      , isCyclic = checkCyclic scc}
    checkCyclic [n] = n `elem` successors gr n
    checkCyclic _   = True

    es    = [ (n1, n2, i) | (n1, cn1) <- ns, (n2, cn2) <- ns,  n1 /= n2, i <- cn1 `edgesTo` cn2 ]

    cn1 `edgesTo` cn2 =
      [ (theRule r1, i) | (n1,r1) <- theSCC cn1, (n, _, i) <- lsuccessors gr n1, n `elem` map fst (theSCC cn2)]

allRulesFromNode :: CDG f v -> NodeId -> [DGNode f v]
allRulesFromNode gr n = case lookupNodeLabel gr n of
  Nothing -> []
  Just cn -> [ sr | (_, sr) <- theSCC cn]

allRulesFromNodes :: CDG f v -> [NodeId] -> [DGNode f v]
allRulesFromNodes gr = concatMap (allRulesFromNode gr)

allRulesPairFromNodes :: CDG f v -> [NodeId] -> ([R.Rule f v], [R.Rule f v])
allRulesPairFromNodes cdg = foldl k ([],[]) . allRulesFromNodes cdg
  where k (srs,wrs) nl = if isStrict nl then (theRule nl:srs, wrs) else (srs,theRule nl:wrs)



congruence :: CDG f v -> NodeId -> [NodeId]
congruence cdg n = fromMaybe [] ((map fst . theSCC) `liftM` lookupNodeLabel cdg n)

isCyclicNode :: CDG f v -> NodeId -> Bool
isCyclicNode cdg n = isCyclic $ lookupNodeLabel' cdg n


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty [NodeId] where
  pretty = PP.set . map PP.int

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (DG f v) where
  pretty wdg
    | null rs   = PP.text "empty"
    | otherwise = PP.vcat [ ppnode n rule PP.<$> PP.empty | (n, rule) <- rs]
    where
      rs = L.sortBy (compare `on` fst) [ (n, theRule r) | (n, r) <- lnodes wdg]
      ppnode n rule =
        PP.int n <> PP.colon <> PP.pretty rule PP.<$$> PP.indent 3
        (PP.vcat [ arr i <> PP.pretty (theRule r_m)  <> PP.colon <> PP.int m | (m,r_m,i) <- lsuccessors wdg n ])
      arr i = PP.text "-->_" <> PP.int i


instance (Xml.Xml f, Xml.Xml v) => Xml.Xml (DG f v) where
  toXml wdg  =
    Xml.elt "dependencygraph" [xmlnodes, xmledges]
    where
      xmlnodes = Xml.elt "nodes" [ Xml.toXml (n, theRule cn)| (n,cn) <- lnodes wdg ]
      xmledges = Xml.elt "edges"
        [  Xml.elt "edge" $ xmlnode "source" n :[ xmlnode "target" m | m <- successors wdg n] | n <- nodes wdg ]
      xmlnode s n = Xml.elt s [Xml.int n]

