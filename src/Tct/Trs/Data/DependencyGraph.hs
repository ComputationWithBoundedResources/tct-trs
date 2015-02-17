module Tct.Trs.Data.DependencyGraph 
  ( 
  DependencyGraph (..)
  , empty
  , DG 
  , CDG
  , estimatedDependencyGraph 
  ) where

import           Control.Monad.State.Strict
import Data.Maybe (catMaybes, isNothing, fromMaybe)
import qualified Data.List as L ((\\))

import qualified Data.Graph.Inductive as Gr
import Data.Graph.Inductive.Basic (undir)
import Data.Graph.Inductive.Query.DFS (dfs)
import qualified Data.Graph.Inductive.Query.DFS as DFS
import Data.Graph.Inductive.Query.BFS (bfsn)

import qualified Data.Rewriting.Term         as R
import qualified Data.Rewriting.Rule         as R (Rule (..))
import qualified Data.Rewriting.Substitution as R

import qualified Tct.Trs.Data.RuleSet as Rs
import qualified Tct.Trs.Data.Trs as Trs
import qualified Tct.Trs.Data.ProblemKind as Prob


--- * dependency graph -----------------------------------------------------------------------------------------------

type NodeId = Gr.Node

data Strictness = StrictDP | WeakDP deriving (Ord, Eq, Show)

type DGNode f v = (Strictness, R.Rule f v)
type DG f v = Graph (DGNode f v) Int

data CDGNode f v = CDGNode 
  { theSCC   :: [(NodeId, DGNode f v)]
  , isCyclic :: Bool } 
  deriving (Eq, Show)

type CDG f v = Graph (CDGNode f v) (R.Rule f v, Int)

type Graph n e = Gr.Gr n e

data DependencyGraph f v = DependencyGraph
  { dependencyGraph :: DG f v
  , congruenceGraph :: CDG f v
  } deriving (Eq, Show)

empty :: DependencyGraph f v
empty = DependencyGraph Gr.empty Gr.empty

--- * inspection -----------------------------------------------------------------------------------------------------

nodes :: Graph n e -> [NodeId]
nodes = Gr.nodes

lnodes :: Graph n e -> [(NodeId,n)]
lnodes = Gr.labNodes

roots :: Graph n e -> [NodeId]
roots gr = [n | n <- Gr.nodes gr, Gr.indeg gr n == 0]

leafs :: Graph n e -> [NodeId]
leafs gr = [n | n <- Gr.nodes gr, Gr.outdeg gr n == 0]

lookupNodeLabel :: Graph n e -> NodeId -> Maybe n
lookupNodeLabel = Gr.lab

lookupNodeLabel' :: Graph n e -> NodeId -> n
lookupNodeLabel' gr n = err `fromMaybe` lookupNodeLabel gr n
  where err = error $ "DependencyGraph.lookupNodelabel': node not found " ++ show n

withNodeLabels :: Graph n e -> [NodeId] -> [(NodeId, Maybe n)]
withNodeLabels gr ns = [(n, lookupNodeLabel gr n) | n <- ns]

withNodeLabels' :: Graph n e -> [NodeId] -> [(NodeId, n)]
withNodeLabels' gr ns = [(n, lookupNodeLabel' gr n) | n <- ns]

lookupNode :: Eq n => Graph n e -> n -> Maybe NodeId
lookupNode gr n = lookup n [(n',i) | (i,n') <- Gr.labNodes gr]

lookupNode' :: Eq n => Graph n e -> n -> NodeId
lookupNode' gr n = err `fromMaybe` lookupNode gr n
  where err = error $ "DependencyGraph.lookupNode': node not found."

inverse :: Graph n e -> Graph n e
inverse gr = Gr.mkGraph ns es
  where ns = Gr.labNodes gr
        es = [ (n2, n1, i) | (n1,n2,i) <- Gr.labEdges gr ]

topsort :: Graph n e -> [NodeId]
topsort = DFS.topsort

sccs :: Graph n e -> [[NodeId]]
sccs = DFS.scc

undirect :: Eq e => Graph n e -> Graph n e
undirect = undir

successors :: Graph n e -> NodeId -> [NodeId]
successors = Gr.suc

reachablesBfs :: Graph n e -> [NodeId] -> [NodeId]
reachablesBfs = flip bfsn

reachablesDfs :: Graph n e -> [NodeId] -> [NodeId]
reachablesDfs = flip dfs

predecessors :: Graph n e -> NodeId -> [NodeId]
predecessors = Gr.pre

lsuccessors :: Graph n e -> NodeId -> [(NodeId, n, e)]
lsuccessors gr nde = [(n, lookupNodeLabel' gr n, e) | (n,e) <- Gr.lsuc gr nde]

lpredecessors :: Graph n e -> NodeId -> [(NodeId, n, e)]
lpredecessors gr nde = [(n, lookupNodeLabel' gr n, e) | (n,e) <- Gr.lpre gr nde]

isEdgeTo :: Graph n e -> NodeId -> NodeId -> Bool
isEdgeTo g n1 n2 = n2 `elem` successors g n1 

isLEdgeTo :: Eq e => Graph n e -> NodeId -> e -> NodeId -> Bool
isLEdgeTo g n1 e n2 = n2 `elem` [n | (n, _, e2) <- lsuccessors g n1, e == e2]

subGraph :: Graph n e -> [NodeId] -> Graph n e
subGraph g ns = Gr.delNodes (nodes g L.\\ ns) g


--- * estimated dependency graph -------------------------------------------------------------------------------------


data Unique v = S v | U v | T v | Some v deriving (Eq, Ord, Show)
data Fresh v = Old v | Fresh Int deriving (Eq, Ord, Show)

freshVar :: State Int (R.Term f (Fresh v))
freshVar = (R.Var . Fresh) `liftM` (modify succ >> get)

estimatedDependencyGraph :: (Ord f, Ord v) => Rs.RuleSet f v -> Prob.Strategy -> DependencyGraph f v
estimatedDependencyGraph rs strat  = DependencyGraph dg cdg where
  dg  = estimatedDependencyGraph' rs strat
  cdg = toCongruenceGraph dg

estimatedDependencyGraph' :: (Gr.Graph gr, Ord v, Ord f, Num b, Enum b) 
  => Rs.RuleSet f v -> Prob.Strategy -> gr (Strictness, R.Rule f v) b
estimatedDependencyGraph' rs strat = Gr.mkGraph ns es
  where
    (strictDPs, weakDPs) = (Trs.toList $ Rs.sdps rs, Trs.toList $ Rs.wdps rs)
    ns = zip [1..] $ [ (StrictDP, r) | r <- strictDPs ] ++ [ (WeakDP, r) | r <- weakDPs ]
    es = [ (n1, n2, i) | (n1,(_,r1)) <- ns, (n2,(_,r2)) <- ns, i <- r1 `edgesTo` r2 ]
    
    (R.Rule s _) `edgesTo` (R.Rule u v)=
      case v of
        R.Var _    -> []
        R.Fun _ ts -> [ i | (i,ti) <- zip [1..] ts, (s,ti) `edgeTo` (u,v) ]

    (s,t) `edgeTo` (u,_) = flip evalState 0 $ do
      let 
        (s',t',u') = (R.rename (Old . S) s, R.rename (Old . T) t, R.rename (Old . U) u)
        trsComponents = Trs.toList (Rs.strs rs) ++ Trs.toList (Rs.wtrs rs)
        lhss = map (R.rename (Old . Some) . R.lhs) trsComponents
        rhss = map (R.rename (Old . Some) . R.rhs) trsComponents
        
        unifyNF t1 t2 = case R.unify t1 t2 of
          Just delta -> isQNF (R.apply delta s') && isQNF (R.apply delta u')
          Nothing    -> False
        qs = case strat of
          Prob.Innermost -> lhss
          _ -> []
        isQNF v = all isNothing [ vi `R.match` l | l <- qs, vi <- R.properSubterms v ]

      tcap <- icap lhss qs [s', u'] t'
      if unifyNF tcap u'
        then icap rhss [] [] u' >>= \ucap -> return (unifyNF ucap t')
        else return False


icap :: (Ord f, Ord v) => [R.Term f (Fresh v)] -> [R.Term f (Fresh v)] -> [R.Term f (Fresh v)] -> R.Term f (Fresh v) -> State Int (R.Term f (Fresh v))          
icap rs qs ss u = icap' u where
  icap' t@(R.Var v)
    | all (`elem` qs) rs && or [v `elem` R.vars s | s <- ss] = return t
    | otherwise                                               = freshVar
  icap' (R.Fun f ts) = do
    t' <- R.Fun f `fmap` mapM icap' ts
    let matches = catMaybes [ (,) l `liftM` R.unify t' l | l <- rs ]
    if and [ any (not . isQNF) [ s | s <- [R.apply delta s | s <- ss] ++ directSubterms (R.apply delta l) ] | (l,delta) <- matches]
      then return t'
      else freshVar                                                                                                                                       
  
  directSubterms (R.Var _)    = []
  directSubterms (R.Fun _ ts) = ts
  isQNF t = all isNothing [t `R.match` q | q <- qs]



--- * congruence graph -----------------------------------------------------------------------------------------------

toCongruenceGraph :: DG f v -> CDG f v
toCongruenceGraph gr = Gr.mkGraph ns es
  where 
    ns    = zip [1..] [sccNode scc | scc <- DFS.scc gr]
    sccNode scc = CDGNode 
      { theSCC   = [ (n, lookupNodeLabel' gr n) | n <- scc]
      , isCyclic = checkCyclic scc}
    checkCyclic [n] = n `elem` successors gr n
    checkCyclic _   = True

    es    = [ (n1, n2, i) | (n1, cn1) <- ns, (n2, cn2) <- ns,  n1 /= n2, i <- cn1 `edgesTo` cn2 ]

    cn1 `edgesTo` cn2 = 
      [ (r1, i) | (n1,(_,r1)) <- theSCC cn1, (n, _, i) <- lsuccessors gr n1, n `elem` map fst (theSCC cn2)]



{-icap :: (Ord f, Ord v, Enum v) => S.Set (R.Term f v) -> S.Set (R.Term f v) -> S.Set (R.Term f v) -> R.Term f v -> State v (R.Term f v)-}
{-icap lhss qnfs snfs u = icap' u-}
  {-where-}
    {-icap' t@(R.Var _)-}
      {-| qnfs `S.isSubsetOf` rnfs && anyS ((t `elem`) . R.subterms) snfs = return t-}
      {-| otherwise                                                       = freshVar-}
    {-icap' (R.Fun f ts) = do-}
      {-t1 <- R.Fun f `liftM` mapM icap' ts-}
      {-let mgus = catMaybes $ do-}
        {-let-}
          {-t2 = T.rename Left t1-}


{-isUnifiableWith :: (Ord v1, Ord v2, Eq f) => T.Term f v1 -> T.Term f v2 -> Bool-}
{-isUnifiableWith t1 t2 = isJust (S.unify (T.rename Left t1) (T.rename Right t2))-}


    {-anyS f = S.foldl' (\acc -> (acc ||) . f) False-}




{-

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Method.DP.DependencyGraph
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module provides dependency graphs.
--------------------------------------------------------------------------------   


module Tct.Method.DP.DependencyGraph 
    (
     -- * Unified Graph Interface
     -- ** Datatypes
     DependencyGraph
     -- | @DependencyGraph n e@ is a Graph with node-labels @n@ and 
     -- edge-labels 'e'
    , Strictness (..)
    , NodeId
     -- | A node in the dependency graph. Most operations work on @NodeId@s. 
     -- Use @lookupNodeLabel@ to get the label of the node

     -- ** Operations
    , nodes
    -- | Returns the set of nodes. 
    , lnodes
    -- | Returns the set of nodes together with their labels. 
     , roots 
     -- | Returns the list of nodes without predecessor.
     , leafs
     -- | Returns the list of nodes without successor.
     , lookupNodeLabel
     -- | Returns the label of the given node, if present.
     , lookupNodeLabel'
     -- | Returns the label of the given node, if present. 
     -- Otherwise an exception is raised
     , lookupNode
     -- | Returns the node with given label.       
     , lookupNode'
     -- | Returns the node with given label.       
     -- Otherwise an exception is raised
     , withNodeLabels
     -- | List version of @lookupNodeLabel@.
     , withNodeLabels'
     -- | List version of @lookupNodeLabel'@.
     , inverse
     -- | Returns the same graph with edges inversed.
     , topsort
     -- | returns a /topologically sorted/ set of nodes.
     , sccs
     -- | returns the list of /strongly connected components/, including trivial ones. 
     , undirect
     -- | Make the graph undirected, i.e. for every edge from A to B, there exists an edge from B to A. 
     , successors
    -- | Returns the list of successors in a given node.
     , reachablesDfs
    -- | @reachable gr ns@ closes the list of nodes @ns@ under 
    -- the successor relation with respect to @ns@ in a depth-first manner.
     , reachablesBfs
    -- | @reachable gr ns@ closes the list of nodes @ns@ under 
    -- the successor relation with respect to @ns@ in a breath-first manner.
     , lsuccessors
    -- | Returns the list of successors in a given node, including their labels.
     , predecessors
    -- | Returns the list of predecessors in a given node.
     , lpredecessors
    -- | Returns the list of predecessors in a given node, including their labels.
    , isEdgeTo
    -- | @isEdgeTo dg n1 n2@ checks wheter @n2@ is a successor of @n1@ in 
    -- the dependency graph @dg@
    , isLEdgeTo
    -- | @isLEdgeTo dg n1 l n2@ checks wheter @n2@ is a successor of @n1@ in 
    -- the dependency graph @dg@, where the edge from @n1@ to @n2@ is 
    -- labeled by @l@.
    , subGraph
    -- | Computes the subgraph based on the given nodes.
      
    -- * Dependency Graph
    -- ** Datatype 
    , DG
    -- | The dependency graph.
    , DGNode
    -- | Nodes of the DG are labeled by rules and their strictness-annotation.
    , Approximation (..)
    , defaultApproximation   
    -- | Construct an estimated dependency graph, using the given approximation.
    , estimatedDependencyGraph
    -- * Congruence Graph
    -- ** Datatype 
    , CDG
    -- | The congruence dependency graph.
    , CDGNode (..)

    -- ** Operations
    ,  toCongruenceGraph
    -- | Computes the congruence graph of a given dependency graph.
    , allRulesFromNode 
    -- | Returns the list of annotated rules of the given node.
    , allRulesFromNodes
    -- | List version of @allRulesFromNode@.
    , congruence
    -- | @congruence cdg n@ 
    -- returns the nodes from the original dependency graph (i.e., the one 
    -- given to @toCongruenceGraph@) that is denoted by the congruence-node @n@.
    , isCyclicNode
    -- | @isCyclicNode cdg n@ 
    -- returns @True@ iff there is an edge from a node in @congruence cdg n@
    -- to @congruence cdg n@ in the original dependency graph (i.e., the one 
    -- given to @toCongruenceGraph@).

    -- ** Utilities
    , pprintCWDGNode
      -- | @pprintCWDGNode cdg sig vars node@ is a default printer for the 
      -- CDG-node @node@. It shows the nodes of the dependency graph denoted by @node@  as a set.
    , pprintCWDG
      -- | Default pretty printer for CDGs. Prints the given CDG in a tree-like shape.
    , pprintNodeSet      
      -- | Default pretty printer for set of nodes.
    , toXml
     -- | Xml representation of given 'DG'. 
    , toGraphViz
      -- | translates 'DG' into a GraphViz graph.
    , saveGraphViz
      -- | output 'DG' as Svg.
    , graphVizSVG
      -- | return 'DG' as Svg string.
    , graphvizShowDG
      -- | show a 'DG' in a GraphViz canvas.
    -- * Misc
    , pprintLabeledRules
    )
where

import qualified Data.Graph.Inductive.Graph as Graph
import Data.Graph.Inductive.Basic (undir)
import qualified Data.Graph.Inductive.Tree as GraphT
import Data.Graph.Inductive.Query.DFS (dfs)
import qualified Data.Graph.Inductive.Query.DFS as DFS
import Data.Graph.Inductive.Query.BFS (bfsn)

import qualified Data.GraphViz.Types.Monadic as GV
import qualified Data.GraphViz.Attributes as GVattribs
import qualified Data.GraphViz.Attributes.Complete as GVattribsc
import Data.GraphViz.Types.Generalised
import qualified Data.GraphViz.Commands as GVcommands
import Data.Text.Lazy (pack)
import System.IO
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC

import qualified Control.Monad.State.Lazy as State
import Data.List (delete, sortBy)
import qualified Data.List as List
import Control.Monad (liftM)
import Control.Monad.Trans (lift)
import Data.Typeable 
import Data.Maybe (fromJust, fromMaybe, catMaybes)
import qualified Data.Map as Map

import qualified Termlib.Substitution as Sub
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Signature as Sig
import qualified Termlib.Variable as V
import qualified Termlib.Problem as Prob
import Termlib.Problem (Problem)
import qualified Termlib.Term as Term
import Termlib.Term (Term, properSubterms)
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs
import Termlib.Trs.PrettyPrint (pprintTrs)
import Text.PrettyPrint.HughesPJ hiding (empty, isEmpty, Str)
import qualified Text.PrettyPrint.HughesPJ as PP
import Termlib.Utils
import Tct.Utils.PPrint
import qualified Tct.Utils.Xml as Xml
import qualified Tct.Utils.Xml.Encoding as XmlE

--------------------------------------------------------------------------------
-- Dependency Graph Type
--------------------------------------------------------------------------------

type DependencyGraph n e = GraphT.Gr n e

type NodeId = Graph.Node

data Strictness = StrictDP | WeakDP deriving (Ord, Eq, Show)

type DGNode = (Strictness, R.Rule)
type DG = DependencyGraph DGNode Int

data CDGNode = CongrNode { theSCC :: [(NodeId, DGNode)]
                         , isCyclic :: Bool } deriving (Show)

type CDG = DependencyGraph CDGNode (R.Rule, Int)

--------------------------------------------------------------------------------
-- Graph Inspection
--------------------------------------------------------------------------------

nodes :: DependencyGraph n e -> [NodeId]
nodes = Graph.nodes

lnodes :: DependencyGraph n e -> [(NodeId,n)]
lnodes = Graph.labNodes

roots :: DependencyGraph n e -> [NodeId]
roots gr = [n | n <- Graph.nodes gr, Graph.indeg gr n == 0]

leafs :: DependencyGraph n e -> [NodeId]
leafs gr = [n | n <- Graph.nodes gr, Graph.outdeg gr n == 0]

lookupNodeLabel :: DependencyGraph n e -> NodeId -> Maybe n
lookupNodeLabel = Graph.lab

lookupNodeLabel' :: DependencyGraph n e -> NodeId -> n
lookupNodeLabel' gr n = fromJust $ lookupNodeLabel gr n

withNodeLabels :: DependencyGraph n e -> [NodeId] -> [(NodeId, Maybe n)]
withNodeLabels gr ns = [(n,lookupNodeLabel gr n) | n <- ns]

withNodeLabels' :: DependencyGraph n e -> [NodeId] -> [(NodeId, n)]
withNodeLabels' gr ns = [(n,lookupNodeLabel' gr n) | n <- ns]

lookupNode :: Eq n => DependencyGraph n e -> n -> Maybe NodeId
lookupNode gr n = lookup n [(n',i) | (i,n') <- Graph.labNodes gr]

lookupNode' :: Eq n => DependencyGraph n e -> n -> NodeId
lookupNode' gr n = fromJust $ lookupNode gr n

inverse :: DependencyGraph n e -> DependencyGraph n e
inverse gr = Graph.mkGraph ns es
  where ns = Graph.labNodes gr
        es = [ (n2, n1, i) | (n1,n2,i) <- Graph.labEdges gr ]

topsort :: DependencyGraph n e -> [NodeId]
topsort = DFS.topsort

sccs :: DependencyGraph n e -> [[NodeId]]
sccs = DFS.scc

undirect :: Eq e => DependencyGraph n e -> DependencyGraph n e
undirect = undir

successors :: DependencyGraph n e -> NodeId -> [NodeId]
successors = Graph.suc

reachablesBfs :: DependencyGraph n e -> [NodeId] -> [NodeId]
reachablesBfs = flip bfsn

reachablesDfs :: DependencyGraph n e -> [NodeId] -> [NodeId]
reachablesDfs = flip dfs

predecessors :: DependencyGraph n e -> NodeId -> [NodeId]
predecessors = Graph.pre

lsuccessors :: DependencyGraph n e -> NodeId -> [(NodeId, n, e)]
lsuccessors gr nde = [(n, lookupNodeLabel' gr n, e) | (n,e) <- Graph.lsuc gr nde]

lpredecessors :: DependencyGraph n e -> NodeId -> [(NodeId, n, e)]
lpredecessors gr nde = [(n, lookupNodeLabel' gr n, e) | (n,e) <- Graph.lpre gr nde]

isEdgeTo :: DependencyGraph n e -> NodeId -> NodeId -> Bool
isEdgeTo g n1 n2 = n2 `elem` successors g n1 

isLEdgeTo :: Eq e => DependencyGraph n e -> NodeId -> e -> NodeId -> Bool
isLEdgeTo g n1 e n2 = n2 `elem` [n | (n, _, e2) <- lsuccessors g n1, e == e2]

subGraph :: DependencyGraph n e -> [NodeId] -> DependencyGraph n e
subGraph g ns = Graph.delNodes (nodes g List.\\ ns) g

--------------------------------------------------------------------------------
-- Estimated Dependency Graph
--------------------------------------------------------------------------------

data Approximation = EdgStar -- ^ EDG* approximation
                   | Trivial -- ^ Fully connected graph
                   | ICapStar -- ^ Generalised EDG*
                   deriving (Bounded, Ord, Eq, Typeable, Enum) 
                            
instance Show Approximation where 
    show EdgStar = "edgstar"
    show Trivial = "trivial"
    show ICapStar = "icapstar"    
    
defaultApproximation :: Approximation    
defaultApproximation = ICapStar

estimatedDependencyGraph :: Approximation -> Problem -> DG
estimatedDependencyGraph approx prob = Graph.mkGraph ns es
    where ns = zip [1..] ([(StrictDP, r) | r <- Trs.rules $ Prob.strictDPs prob] 
                          ++ [(WeakDP, r) | r <- Trs.rules $ Prob.weakDPs prob])
          es = [ (n1, n2, i) | (n1,(_,r1)) <- ns
                             , (n2,(_,r2)) <- ns
                             , i <- r1 `edgesTo` r2] 
          r1 `edgesTo` r2 = 
            case R.rhs r1 of 
              (Term.Var _) -> []
              t@(Term.Fun f ts) -> [ i | (i,ti) <- zip [1..] ts'
                                       , (s,ti) `edgeTo` (u,v)] 
                where s = R.lhs r1
                      ts' | F.isCompound sig f = ts
                          | otherwise          = [t]
                      u = R.lhs r2
                      v = R.rhs r2
          (s,t) `edgeTo` (u,_) =                     
              case approx of 
                EdgStar -> matchEdg (etcapEdg lhss t) u 
                          && (any Term.isVariable rhss 
                             || matchEdg (etcapEdg rhss u) t)
                          
                ICapStar -> fst $ flip Sig.runSignature vs $ do
                  [s',t'] <- rename [s,t]
                  [u'] <- rename [u]
                  let unifyNF t1 t2 = 
                       case Sub.unify t1 t2 of 
                         Just delta -> isQNF (Sub.apply delta s') && isQNF (Sub.apply delta u')
                         Nothing -> False
                      qs = case Prob.strategy prob of 
                               Prob.Innermost -> lhss
                               _              -> []
                      isQNF v = all not [ v_i `Sub.matches` l | l <- qs, v_i <- properSubterms v]
                  tcap <- icap lhss qs [s',u'] t'
                  case unifyNF tcap u' of 
                    False -> return $ False
                    True -> do 
                      ucap <- icap rhss [] [] u'
                      return $ unifyNF ucap t'
                            
              -- EdgStar -> fst $ Sig.runSignature (s `matchEdgStar` t) vs
              -- s `matchEdgStar` t = 
              --   do s' <- renCap strat lhss s
              --      t' <- renCap strat rhss t
              --      return $ s' `Sub.isUnifiable` t 
              --               && s `Sub.isUnifiable` t'

                        
                _    -> True
          sig = Prob.signature prob
          vs = Prob.variables prob
          rs = Prob.trsComponents prob
          lhss = Trs.lhss rs
          rhss = Trs.rhss rs


--------------------------------------------------------------------------------
-- Congruence Dependency Graph
--------------------------------------------------------------------------------

allRulesFromNode :: CDG -> NodeId -> [(Strictness, R.Rule)]
allRulesFromNode gr n = case lookupNodeLabel gr n of 
                            Nothing -> []
                            Just cn -> [ sr | (_, sr) <- theSCC cn]

allRulesFromNodes :: CDG -> [NodeId] -> [(Strictness, R.Rule)]
allRulesFromNodes gr ns = concatMap (allRulesFromNode gr) ns

congruence :: CDG -> NodeId -> [NodeId]
congruence cdg n = fromMaybe [] ((map fst . theSCC) `liftM` lookupNodeLabel cdg n)

isCyclicNode :: CDG -> NodeId -> Bool
isCyclicNode cdg n = isCyclic $ lookupNodeLabel' cdg n


toCongruenceGraph :: DG -> CDG
toCongruenceGraph gr = Graph.mkGraph ns es
    where ns    = zip [1..] [sccNode scc | scc <- DFS.scc gr]
          es    = [ (n1, n2, i) | (n1, cn1) <- ns
                                 , (n2, cn2) <- ns
                                 , n1 /= n2
                                 , i <- cn1 `edgesTo` cn2 ]
          cn1 `edgesTo` cn2 = [ (r1, i) | (n1,(_,r1)) <- theSCC cn1
                              , (n, _, i) <- lsuccessors gr n1
                              , n `elem` map fst (theSCC cn2)]
          sccNode scc = CongrNode { theSCC = [ (n, fromJust $ lookupNodeLabel gr n) | n <- scc]
                                  , isCyclic = checkCyclic scc}
          checkCyclic [n] = n `elem` successors gr n
          checkCyclic _   = True

instance PrettyPrintable (DG, F.Signature, V.Variables) where 
  pprint (wdg, sig, vars) | isEmpty   = text "empty" 
                          | otherwise = vcat [ ppnode n rule $+$ text "" | (n, rule) <- rs]
    where isEmpty = length rs == 0
          rs = sortBy compFst [ (n, rule) | (n, (_, rule)) <- Graph.labNodes wdg]
            where (a1,_) `compFst` (a2,_) = a1 `compare` a2
          ppnode n rule = hang (text (show n) <> text ":" <+> pprule rule) 3 $ 
                            vcat [ arr i <+> pprule rule_m  <+> text ":" <> text (show m) 
                                 | (m,(_, rule_m),i) <- lsuccessors wdg n ]
          pprule r = pprint (r, sig, vars)
          arr i = text "-->_" <> text (show i)

-- utilities
-- edg transformation
data GroundContext = Hole | Fun F.Symbol [GroundContext]
  deriving (Eq,Show)

-- deleteAll :: Eq a => a -> [a] -> [a]
-- deleteAll _ [] = []
-- deleteAll a (b:bs) | a == b = deleteAll a bs
--                    | otherwise = b : deleteAll a bs
                                 
matchEdg :: GroundContext -> Term -> Bool
matchEdg c t = match' [(c, t)] []
    where match' [] mergeqs = matchmergeEdg mergeqs
          match' ((Hole,_) : eqs) mergeqs = match' eqs mergeqs
          match' ((c', Term.Var x) : eqs) mergeqs = match' eqs ((c',x) : mergeqs)
          match' ((Fun f ss, Term.Fun g ts) : eqs) mergeqs
            | f /= g || length ss /= length ts = False
            | otherwise = match' (zip ss ts ++ eqs) mergeqs

matchmergeEdg :: [(GroundContext, V.Variable)] -> Bool
matchmergeEdg [] = True
matchmergeEdg ((c,x):eqs) = 
  case List.find ((== x) . snd) eqs of
    Nothing     -> matchmergeEdg eqs
    Just (d, y) -> case merge c d of
                  Nothing -> False
                  Just e  -> matchmergeEdg ((e, x) : delete (d, y) eqs)
  where merge Hole c' = Just c'
        merge c' Hole = Just c'
        merge (Fun f ss) (Fun g ts) 
          | f /= g                 = Nothing
          | length ss /= length ts = Nothing
          | any (== Nothing) cs    = Nothing 
          | otherwise              = Just $ Fun f cs'
              where cs  = zipWith merge ss ts
                    cs' = map fromJust cs


etcapEdg :: [Term] -> Term -> GroundContext
etcapEdg _ (Term.Var _)       = Hole
etcapEdg lhss (Term.Fun f ts) = if any (matchEdg c) lhss then Hole else c
    where c = Fun f $ map (etcapEdg lhss) ts

rename :: [Term] -> V.VariableMonad [Term]
rename ss = State.evalStateT (mapM rename' ss) Map.empty
  where rename' v@(Term.Var _) = Term.Var `liftM` var v
        rename' (Term.Fun f ts) = Term.Fun f `liftM` mapM rename' ts
        freshVar = lift $ V.fresh "fresh"
        var v  = do
          m <- State.get 
          case Map.lookup v m of
            Just v' -> return v'
            Nothing -> do 
              v' <- freshVar
              State.put (Map.insert v v' m)
              return v'          

-- renCap :: Prob.Strategy -> [Term] -> Term -> V.VariableMonad Term
-- renCap strat lhss t = State.evalStateT (cap' t) Map.empty
--   where cap' v@(Term.Var _) = var v
--         cap' (Term.Fun f ts) 
--           | replaceP f = freshVar
--           | otherwise = Term.Fun f `liftM` mapM cap' ts

--         replaceP f = any fOrVar [Term.root l | l <- lhss]
--           where fOrVar (Left _) = True
--                 fOrVar (Right g) | f == g = True
--                                  | otherwise = False

--         var v | strat /= Prob.Innermost = freshVar
--               | otherwise = do
--                 m <- State.get 
--                 case Map.lookup v m of
--                   Just v' -> return $ v'
--                   Nothing -> do 
--                          v' <- freshVar
--                          State.put (Map.insert v v' m)
--                          return v'
                         
--         freshVar = lift $ Term.Var `liftM` V.fresh "fresh"
                
icap :: [Term] -> [Term] -> [Term] -> Term -> V.VariableMonad Term          
icap rs qs ss u = icap' u
  where icap' t = 
          case t of 
            (Term.Var _) 
              | all (`elem` qs) rs
                && or [ t `Term.isSubtermOf` s | s <- ss] -> return t
              | otherwise -> freshVar
            (Term.Fun f ts) -> do 
              t' <- Term.Fun f `liftM` mapM icap' ts
              let matches = catMaybes [ (,) l `liftM` Sub.unify t' l | l <- rs]
              if and [ any (not . isQNF) [ s | s <- [Sub.apply delta s | s <- ss] 
                                                   ++ Term.immediateSubterms (Sub.apply delta l) ]
                     | (l,delta) <- matches]
               then return t'  
               else freshVar
                    
        freshVar = Term.Var `liftM` V.fresh "fresh"
        isQNF t = all not [ t `Sub.matches` q | q <- qs]

----------------------------------------------------------------------
--- pretty printing          
        
pprintNodeSet :: [NodeId] -> Doc
pprintNodeSet ns = braces $ hcat $ punctuate (text ",") [ text $ show n | n <- ns]
  
pprintCWDGNode :: CDG -> F.Signature -> V.Variables -> NodeId -> Doc
-- pprintCWDGNode cwdg _ _ n = text (show n) <> (text ":") <> pprintNodeSet (congruence cwdg n)
pprintCWDGNode cwdg _ _ n = pprintNodeSet (congruence cwdg n)

pprintCWDG :: CDG -> F.Signature -> V.Variables -> ([NodeId] -> NodeId -> Doc) -> Doc
pprintCWDG cwdg sig vars ppLabel | isEmpty = text "empty"
                                 | otherwise = 
    printTree 45 ppNode ppLabel pTree
    $+$ text ""
    $+$ text "Here dependency-pairs are as follows:"
    $+$ text ""
    $+$ pprintLabeledRules "Strict DPs" sig vars (rs StrictDP)
    $+$ pprintLabeledRules "Weak DPs" sig vars (rs WeakDP)
    where isEmpty = null $ allRulesFromNodes cwdg (nodes cwdg)
          ppNode _ n    = printNodeId n
          pTree = PPTree { pptRoots = sortBy compareLabel $ roots cwdg
                         , pptSuc = sortBy compareLabel . snub . successors cwdg}
          compareLabel n1 n2 = congruence cwdg n1 `compare` congruence cwdg n2
          printNodeId = pprintCWDGNode cwdg sig vars 
          rs strictness = sortBy compFst $ concatMap (\ (_, cn) -> [ (n, rule) | (n, (s, rule)) <- theSCC cn, s == strictness]) (Graph.labNodes cwdg)
            where (a1,_) `compFst` (a2,_) = a1 `compare` a2
          
instance PrettyPrintable (CDG, F.Signature, V.Variables) where 
  pprint (cwdg, sig, vars) = pprintCWDG cwdg sig vars (\ _ _ -> PP.empty)

pprintLabeledRules :: PrettyPrintable l => String -> F.Signature -> V.Variables -> [(l,R.Rule)] -> Doc
pprintLabeledRules _    _   _ [] = PP.empty
pprintLabeledRules name sig vars rs = text name <> text ":"
                                      $+$ indent (pprintTrs pprule rs)
  where pprule (l,r) = pprint l <> text ":" <+> pprint (r, sig, vars)


-- graphviz output of dgs



toGraphViz :: [(DG,F.Signature,V.Variables)] -> Bool -> DotGraph String
toGraphViz dgs showLabels = GV.digraph' $ mapM digraph $ zip [(1::Int)..] dgs
  where digraph (i,(dg,sig,vars)) = do
          GV.graphAttrs [GVattribsc.Size size]
          GV.cluster (Str $ pack $ "dg_" ++ show i) $
            if showLabels then graphM >> labelM else graphM
          where nds   = nodes dg
                size = GVattribsc.GSize { 
                                      GVattribsc.width = 12.0
                                    , GVattribsc.height = Just 6.0
                                    , GVattribsc.desiredSize = True }
                graphM = do
                  mapM_ sccToGV $ zip [(1::Int)..] (DFS.scc dg)
                  mapM_ edgesToGV nds
                labelM = GV.graphAttrs [GVattribs.toLabel pplabel]
                lrules = [(n,r) | (n,(_,r)) <- withNodeLabels' dg nds]
                pprule r = st (R.lhs r) ++ " -> " ++ st (R.rhs r) ++ "\\l"
                  where st t = [c | c <- show $ pprint (t,sig,vars), c /= '\n']
                pplabel = "Below rules are as follows:\\l" ++ concatMap (\ (n,r) -> " " ++ show n ++ ": " ++ pprule r) lrules

                sccToGV (j,scc) = GV.cluster (Str $ pack $ show i ++ "_" ++ show j) $ mapM nodesToGV $ withNodeLabels' dg scc
                nodesToGV (n,(strictness,r)) = GV.node (nde n) attribs
                  where 
                    attribs = [ GVattribs.toLabel (show n) 
                              , GVattribsc.Tooltip (pack $ pprule r) ]
                               ++ shape strictness
                    shape StrictDP = [GVattribs.shape GVattribs.Circle]
                    shape WeakDP   = [GVattribs.shape GVattribs.Circle, GVattribs.style GVattribs.dotted]
                edgesToGV n = mapM (\ (m,_,k) -> GV.edge (nde n) (nde m) [GVattribs.toLabel (show k)]) (lsuccessors dg n)
                nde n = show i ++ "_" ++ show n
                
saveGraphViz :: [(DG,F.Signature,V.Variables)] -> Bool -> FilePath -> IO FilePath
saveGraphViz dgs showLabels = GVcommands.runGraphvizCommand GVcommands.Dot (toGraphViz dgs showLabels) GVcommands.Svg

graphVizSVG :: [(DG,F.Signature,V.Variables)] -> Bool -> String
graphVizSVG dgs showLabels = unsafePerformIO $ 
  GVcommands.graphvizWithHandle GVcommands.Dot (toGraphViz dgs showLabels) GVcommands.Svg rd
    where rd h = do 
            bs <- BS.hGetContents h
            hClose h
            return $! BSC.unpack bs
  
            
    
graphvizShowDG :: [(DG,F.Signature,V.Variables)] -> IO ()              
graphvizShowDG dgs = GVcommands.runGraphvizCanvas GVcommands.Dot (toGraphViz dgs True) GVcommands.Gtk


toXml :: (DG, F.Signature, V.Variables) -> Xml.XmlContent
toXml (dg,sig,vs) = 
    Xml.elt "dependencygraph" [] 
           [
            -- Xml.elt "svg" [] [ Xml.text $ graphVizSVG [(dg,sig,vs)] False ]
           Xml.elt "nodes" [] [ XmlE.rule r (Just n) sig vs | (n,(_,r)) <- lnodes dg  ]
           , Xml.elt "edges" [] [ Xml.elt "edge" [] $ 
                                          Xml.elt "source" [] [Xml.int n] : [ Xml.elt "target" [] [Xml.int  m] | m <- successors dg n ] 
                                  | n <- nodes dg] ]
           -- , Xml.elt "edges" [] [ Xml.elt "edge" [] $ 
           --                                Xml.elt "source" [] [Xml.rule r (Just n) sig vs]
           --                                       : [ Xml.elt "targets" [] [Xml.rule s (Just m) sig vs | (m,(_,s),_) <- lsuccessors dg n ] ]
           --                        | (n,(_,r)) <- lnodes dg] ]

-}
