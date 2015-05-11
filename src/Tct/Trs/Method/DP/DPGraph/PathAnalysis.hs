-- | This module provides the \Path Analysis\ processor.
module Tct.Trs.Method.DP.DPGraph.PathAnalysis 
  ( pathAnalysisDeclaration
  , pathAnalysis
  , pathAnalysis'
  , linearPathAnalysis
  ) where

-- notes:
-- congruence graph, (with nodes  P1,...,Pn), is acyclic
-- a derivation starts in root nodes
-- theory states that we can consider paths (P1, ..., Pm)


-- linear path analysis:
-- we consider all paths from root nodes to leaf nodes
-- the weak/strict dp rules of each node are collected on the path
-- optimisation: r1 is subsumed by r2 if nodes(r1) is a subset of nodes(r2)

-- path analysis:
-- we consider all paths starting from root nodes
-- each path constitutes to a problem, where
-- * weak dps: consits of all rules peviously visited along the path + the weak rules of the current node
-- * strict dps: consists of all strict rules of the current node
-- optimisation: non-leaf congruence nodes consisting of only weak rules are subsumed by longer paths

import           Data.Either                  (partitionEithers)
import qualified Data.List                    as L
import           Data.Monoid
import qualified Data.Set                     as S


import qualified Tct.Core.Common.Pretty       as PP
import           Tct.Core.Common.SemiRing     (add)
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import           Tct.Trs.Data.DependencyGraph
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.RuleSet         as Prob
import qualified Tct.Trs.Data.Trs             as Trs


type Path         = [NodeId]
type Subsumed f v = Either (Path, [Path]) (Path, RuleSet f v)


data PathAnalysis = PathAnalysis { onlyLinear :: Bool } deriving Show

data PathAnalysisProof
  = PathAnalysisProof
    { paths_         :: [Path]
    , wdg_           :: DG F V
    , cdg_           :: CDG F V
    , subsumedBy_    :: [(Path,[Path])]
    , isLinearProof_ :: Bool }
  | PathAnalysisFail
  deriving Show


instance T.Processor PathAnalysis where
  type ProofObject PathAnalysis = ApplicationProof PathAnalysisProof
  type I PathAnalysis           = TrsProblem
  type O PathAnalysis           = TrsProblem
  type Forking PathAnalysis     = []

  solve p prob =  return . T.resultToTree p prob $
    maybe computePaths (T.Fail . Inapplicable) (Prob.isDPProblem' prob)
    where
      computePaths
        | null (drop 1 paths) = T.Fail (Applicable PathAnalysisFail)
        | otherwise           = T.Success (map nprob probPaths) (Applicable proof) (foldl add (T.timeUBCert T.linear))
        where

          wdg = Prob.dependencyGraph prob
          cdg = Prob.congruenceGraph prob

          nprob (_,rs) = prob { Prob.strictDPs=Prob.sdps rs, Prob.weakDPs=Prob.wdps rs }
          proof = PathAnalysisProof
            { paths_         = paths
            , wdg_           = wdg
            , cdg_           = cdg
            , subsumedBy_    = subsumedBy
            , isLinearProof_ = onlyLinear p }

          (subsumedBy, probPaths) = partitionEithers $ concatMap (walk cdg) (roots cdg)
            where walk = if onlyLinear p then walkFromL else walkFromQ

          paths = [pth | (pth, _) <- subsumedBy] ++ [pth | (pth,_) <- probPaths]

nodesFrom :: (Ord v, Ord f) => CDG f v -> NodeId -> (Trs f v, Trs f v)
nodesFrom cdg n = (Trs.fromList srs, Trs.fromList wrs)
  where (srs,wrs) = allRulesPairFromNodes cdg [n]

walkFromL :: (Ord v, Ord f) => CDG f v -> NodeId -> [Subsumed f v]
walkFromL cdg root = map toSubsumed walked where
  walked = walkFromL' ([],S.empty) Prob.emptyRuleSet root
  toSubsumed (path1, nds1, rs1) =
    -- TODO: MS can there not be identic node sets
    case [ path2 | (path2, nds2 , _) <- walked , nds1 `S.isProperSubsetOf` nds2 ] of
      []   -> Right (path1, rs1)
      pths -> Left  (path1, pths)

  walkFromL' (path, visited)  rs n = new ++ concatMap (walkFromL' (path',visited') rs') sucs where
    (stricts,weaks) = nodesFrom cdg n

    path'    = path ++ [n]
    visited' = S.insert n visited
    sucs = L.nub $ successors cdg n
    new
      | null sucs = [(path',visited',rs')]
      | otherwise = []
    rs' = rs
      { Prob.sdps = Prob.sdps rs `Trs.union` stricts
      , Prob.wdps = Prob.wdps rs `Trs.union` weaks }

walkFromQ :: (Ord v, Ord f) => CDG f v -> NodeId -> [Subsumed f v]
walkFromQ cdg root = walkFromQ' [] Prob.emptyRuleSet root where
  walkFromQ' path rs n = new ++ concatMap (walkFromQ' path' rs') sucs where
    (stricts,weaks) = nodesFrom cdg n

    path' = path ++ [n]
    sucs = L.nub $ successors cdg n
    new
      | subsumed  = [Left  (path, [path ++ [n'] | n' <- sucs])]
      | otherwise = [Right (path, rs')]
      where subsumed = not (null sucs) && Trs.null stricts
    rs' = rs
      { Prob.sdps = stricts
      , Prob.wdps = (Prob.sdps rs `Trs.union` Prob.wdps rs) `Trs.union` weaks }


--- * instances ------------------------------------------------------------------------------------------------------

pathAnalysisStrategy :: Bool -> TrsStrategy
pathAnalysisStrategy b = T.Proc $ PathAnalysis { onlyLinear=b }

pathAnalysisDeclaration :: T.Declaration ('[T.Argument 'T.Optional Bool] T.:-> TrsStrategy)
pathAnalysisDeclaration = T.declare "pathAnalysis" desc (T.OneTuple linArg) pathAnalysisStrategy
  where
    desc = ["This processor implements path-analysis as described in the dependency pair paper."]
    linArg = T.bool
      `T.withName` "linear"
      `T.withHelp` ["If this flag is set, linear path analysis is employed."]
      `T.optional` True

pathAnalysis :: Bool -> TrsStrategy
pathAnalysis = T.declFun pathAnalysisDeclaration

pathAnalysis' :: TrsStrategy
pathAnalysis' = T.deflFun pathAnalysisDeclaration

linearPathAnalysis :: TrsStrategy
linearPathAnalysis = pathAnalysisStrategy True


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty PathAnalysisProof where
  pretty PathAnalysisFail      = PP.text "Path analysis is not successfull."
  pretty p@PathAnalysisProof{} = PP.vcat $
    [ PP.text $ "We employ '" ++ nm ++ "path analysis' using the following approximated dependency graph:" 
    , PP.indent 2 $ PP.pretty (wdg_ p) 
    , PP.text $ "Obtaining following paths:"
    , PP.indent 2 $ PP.enumerate (map ppPath $ paths_ p) ]
    where
      nm = if isLinearProof_ p then "linear " else ""
      ppPath path = PP.text "Path: " <> PP.list' path

instance Xml.Xml PathAnalysisProof where
  toXml PathAnalysisFail = Xml.elt "pathAnalysis" []
  toXml p@PathAnalysisProof{} = Xml.elt "pathAnalysis" 
    [ Xml.toXml (wdg_ p)
    , Xml.elt "kind" [ Xml.text $ if isLinearProof_ p then "linear" else "quadratic" ]
    , Xml.elt "paths" 
      [ Xml.elt "congruence"
        [ Xml.elt "elt" [ Xml.int m | m <- congruence (cdg_ p) n] | n <- path ]
      | path <- paths_ p ] ]

