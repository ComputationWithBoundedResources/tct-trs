module Tct.Trs.Method.DP.DPGraph.PathAnalysis where

-- notes:
-- congruence graph, (with nodes  P1,...,Pn), is acyclic
-- a derivation starts in root nodes
-- theory states that we can consider paths (P1, ..., Pm)


-- linear path analysis:
-- we consider all paths from root nodes to leaf nodes
-- the weak/strict dp rules of each node are collected on the path

-- path analysis:
-- we consider all paths starting from root nodes
-- each path constitutes to a problem, where 
-- * weak dps: consits of all rules peviously visited along the path + the weak rules of the current node
-- * strict dps: consists of all strict rules of the current node
--
-- optimisation: subsumption wrt to rule set
-- * linear path analysis
--
import qualified Data.List as L (nub)
import qualified Data.Set as S

import Tct.Trs.Data
import qualified Tct.Trs.Data.RuleSet as Prob
import qualified Tct.Trs.Data.Trs as Trs
import Tct.Trs.Data.DependencyGraph

type Path         = [NodeId]
type Subsumed f v = Either (Path, [Path]) (Path, RuleSet f v) 



walkFromL :: (Ord v, Ord f) => NodeId -> [Subsumed f v]
walkFromL root = toSubsume $ walkFromL' [] Prob.emptyRuleSet root
  where
    toSubsume = map check . withNodes
    withNodes = map (\x -> (x, S.fromList $ fst x))
    check ((path1, rs1), nds1) =
      case [ path2 | ((path2, _), nds2) <- withNodes , nds1 `S.isProperSubsetOf` nds2 ] of
        []   -> Right (path1, rs1)
        pths -> Left  (path1, pths)

    walkFromL' :: (Ord f, Ord v) => Path -> RuleSet f v -> NodeId -> [(Path, RuleSet f v)]
    walkFromL' path rs n = new ++ concatMap (walkFromL' path' rs') sucs
      where
        stricts = undefined
        weaks = undefined
        cdg = undefined
        path' = path ++ [n]
        sucs = L.nub $ successors cdg n
        new
          | null sucs = [(path',rs')]
          | otherwise = [] 
        rs' = rs
          { Prob.sdps = Prob.sdps rs `Trs.union` stricts 
          , Prob.wdps = Prob.wdps rs `Trs.union` weaks }

walkFromQ :: (Ord v, Ord f) => NodeId -> [Subsumed f v]
walkFromQ root = walkFromQ' [] Prob.emptyRuleSet root

walkFromQ' :: (Ord v, Ord f) => [NodeId] -> RuleSet f v -> NodeId -> [Subsumed f v]
walkFromQ' path rs n = new ++ concatMap (walkFromQ' path' rs') sucs
  where
    stricts = undefined
    weaks = undefined
    cdg = undefined
    path' = path ++ [n]
    sucs = L.nub $ successors cdg n
    new
      | subsumed  = [Left  (path, [path ++ [n'] | n' <- sucs])]
      | otherwise = [Right (path, rs')] 
      where subsumed = not (null sucs) && Trs.null stricts
    rs' = rs
      { Prob.sdps = stricts 
      , Prob.wdps = (Prob.sdps rs `Trs.union` Prob.wdps rs) `Trs.union` weaks }











{-

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Method.DP.PathAnalysis
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module provides the path analysis with respect to dependency
-- graphs.
--------------------------------------------------------------------------------   

module Tct.Method.DP.PathAnalysis 
       (
         pathAnalysis
         -- * Proof Object
       , PathProof
         -- * Processor
       , pathAnalysisProcessor
       , PathAnalysis
       )
where

import qualified Data.List as List
import qualified Data.Set as Set
import Control.Monad (liftM)
import Control.Applicative ((<|>))
-- import Control.Monad.Trans (liftIO)
import Data.Maybe (fromMaybe)
import Data.Either (partitionEithers)
import qualified Text.PrettyPrint.HughesPJ as PP 
import Text.PrettyPrint.HughesPJ hiding (empty)

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Termlib.Trs as Trs
import qualified Termlib.Variable as V
import Termlib.Utils

import Tct.Certificate
import Tct.Method.DP.DependencyGraph as DG
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args as A
import Tct.Utils.PPrint
import Tct.Utils.Enum
import qualified Tct.Utils.Xml as Xml
import Tct.Processor.Args.Instances ()
import Tct.Method.DP.Utils

----------------------------------------------------------------------
-- Proof objects

data Path = Path { thePath :: [NodeId] } deriving (Eq, Show)

data PathProof = PathProof { computedPaths   :: [Path]
                           , computedCongrDG :: CDG
                           , computedDG      :: DG
                           , subsumedBy      :: [(Path,[Path])]
                           , variables       :: V.Variables
                           , signature       :: F.Signature
                           , isLinearProof   :: Bool}
                 | Error DPError

data PathAnalysis = PathAnalysis

instance T.Transformer PathAnalysis where
    name PathAnalysis        = "pathanalysis"
    description PathAnalysis = ["This processor implements path-analysis as described in the dependency pair paper."]
    type ArgumentsOf PathAnalysis = Arg Bool
    type ProofOf PathAnalysis = PathProof
    arguments PathAnalysis = opt { A.name = "linear"
                                 , A.description = unlines [ "If this flag is set, linear path analysis is employed."]
                                 , A.defaultValue = False }
    transform inst prob 
           | not $ Prob.isDPProblem prob = return $ T.NoProgress $ Error NonDPProblemGiven
           | otherwise                 = return $ res
        where lin = T.transformationArgs inst
              res | progressed = T.Progress p (enumeration [(thePath pth, prob') | (pth,prob') <- pathsToProbs ])
                  | otherwise  = T.NoProgress p
              edg  = estimatedDependencyGraph defaultApproximation prob
              cedg = toCongruenceGraph edg
              rts  = roots cedg
              -- lfs  = leafs cedg
              p = PathProof { computedPaths   = paths
                            , computedCongrDG = cedg
                            , computedDG      = edg
                            , subsumedBy      = subsume
                            , variables       = Prob.variables prob
                            , signature       = Prob.signature prob
                            , isLinearProof   = lin}
              (subsume, pathsToProbs) = partitionEithers $ concatMap walk rts
                 where walk | lin       = walkFromL 
                            | otherwise = walkFromQ
              paths = [pth | (pth, _) <- subsume] ++ [pth | (pth,_) <- pathsToProbs]


              walkFromL n = [ toSubsumed r | r <- walked]
                 where walked = walkFromL' prob { Prob.strictDPs = Trs.empty, Prob.weakDPs = Trs.empty} ([],Set.empty) n
                       toSubsumed (path, nds,pprob) = 
                                case [ Path path2 | (path2, nds2, _) <- walked , nds `Set.isProperSubsetOf` nds2 ] of
                                   []   -> Right (Path path, pprob)
                                   pths -> Left (Path path, pths)
              walkFromL' pprob (prefix, nds) n = new ++ concatMap (walkFromL' pprob' (prefix', nds')) sucs
                  where sucs    = List.nub $ successors cedg n
                        prefix' = prefix ++ [n]
                        nds'    = n `Set.insert` nds
                        pprob'  = pprob { Prob.strictDPs = Prob.strictDPs pprob `Trs.union` stricts
                                        , Prob.weakDPs   = Prob.weakDPs pprob `Trs.union` weaks }

                        new | null sucs = [ ( prefix', nds', pprob') ]
                            | otherwise = []
                        rs      = allRulesFromNodes cedg [n]
                        {-stricts = Trs.fromRules [ r | (StrictDP, r) <- rs]-}
                        {-weaks   = Trs.fromRules [ r | (WeakDP, r) <- rs]-}
                          
              walkFromQ = walkFromQ' Trs.empty []
              walkFromQ' weaks prefix n = new ++ concatMap (walkFromQ' weaks' path) sucs
                  where path = prefix ++ [n]
                        sucs = List.nub $ successors cedg n
                        rs = allRulesFromNodes cedg [n]
                        strict_n = Trs.fromRules [ r | (StrictDP, r) <- rs]
                        weak_n = Trs.fromRules [ r | (WeakDP, r) <- rs]
                        weaks' = strict_n `Trs.union` weak_n `Trs.union` weaks
                        new | subsumed  = [Left  ( Path path, [Path $ path ++ [n'] | n' <- sucs ] )]
                            | otherwise = [Right ( Path path
                                                 , prob { Prob.strictDPs = strict_n, Prob.weakDPs = weaks} )]
                            where subsumed = not (null sucs) && Trs.isEmpty strict_n

              progressed = 
                  case paths of 
                    [pth] -> length spath < length sprob
                      where spath = [ r | (StrictDP, r) <- allRulesFromNodes cedg (thePath pth) ]
                            sprob = Trs.toRules $ Prob.strictDPs prob
                    _     -> True

              -- progressed | lin = length (rts ++ lfs) > 2
              --            | otherwise = 
              --               case paths of 
              --                  [pth] -> length spath < length sprob
              --                      where spath = [ r | (StrictDP, r) <- allRulesFromNodes cedg (thePath pth) ]
              --                            sprob = Trs.toRules $ Prob.strictDPs prob
              --                  _     -> True

printPathName :: CDG -> F.Signature -> V.Variables -> Path -> Doc
printPathName cwdg sig vars (Path ns) = hcat $ punctuate (text "->") [printNodeId n | n <- ns] 
  where printNodeId = pprintCWDGNode cwdg sig vars 


instance T.TransformationProof PathAnalysis where
    answer proof = case T.transformationResult proof of 
                     T.NoProgress _ -> T.answerFromSubProof proof
                     T.Progress _ subprobs -> 
                         case mproofs of 
                           Just proofs -> if all P.succeeded proofs
                                          then P.CertAnswer $ certified (unknown, mkUb proofs)
                                          else P.MaybeAnswer
                           Nothing  -> P.MaybeAnswer
                         where mproofs = sequence [ T.findProof e proof | (SN e,_) <- subprobs]
                               mkUb proofs = maximum $ (Poly $ Just 1) : [upperBound $ P.certificate p | p <- proofs]

    tproofToXml _ _ (Error e) = ("pathanalysis", [errorToXml e])
    tproofToXml _ _ p = 
        ( "pathanalysis"
        , [ DG.toXml (dg, sig, vs)
          , Xml.elt "kind" [] [ Xml.text kind ]
          , Xml.elt "paths" [] [ pToXml path | path <- computedPaths p ]
          ])
            where 
              sig = signature p
              vs = variables p
              dg = computedDG p
              cwdg = computedCongrDG p
              kind | isLinearProof p = "linear"
                   | otherwise = "quadratic"
              pToXml path = Xml.elt "path" [] [ Xml.elt "congruence" [] [ Xml.elt "elt" [] [Xml.text $ show m] |  m <- congruence cwdg n] 
                                                | n <- thePath path]
                        
                           
    pprintProof proof mde = 
        case T.transformationProof proof of 
          Error   e   -> pprint e
          tproof -> paragraph ("We employ '" ++ nm ++ "' using the following approximated dependency graph:")
                   $+$ pprintCWDG cwdg sig vars ppLabel
                   $+$ text ""
                   $+$ ppDetails
              where cwdg = computedCongrDG tproof
                    sig = signature tproof
                    vars = variables tproof
  
                    nm | isLinearProof tproof = "linear path analysis"
                       | otherwise            = "path analysis"
                    ppLabel pth _ = PP.brackets $ centering 20 $ ppMaybeAnswerOf (Path pth)
                        where centering n d =  text $ take pre ss ++ s ++ take post ss
                                  where s = show d
                                        l = length s
                                        ss = repeat ' '
                                        pre = floor $ (fromIntegral (n - l) / 2.0 :: Double)
                                        post = n - l - pre

                    ppMaybeAnswerOf pth = fromMaybe (text "?") (ppSpAns <|> ppSubsumed)
                        where ppSpAns    = pprint `liftM` P.answer `liftM` findSubProof pth
                              ppSubsumed = const (text "subsumed") `liftM` List.lookup pth (subsumedBy tproof)

                    findSubProof pth = T.findProof (thePath pth) proof
                    ppPathName path = printPathName cwdg sig vars path

                    ppDetails = vcat $ List.intersperse (text "") 
                                         [ (text "*" <+> (underline (text "Path" <+> ppPathName path <> text ":" <+> ppMaybeAnswerOf path)
                                                          $+$ text ""
                                                          $+$ ppDetail path))
                                           | path <- List.sortBy comparePath $ computedPaths tproof]
                        where comparePath p1 p2 = mkpath p1 `compare` mkpath p2
                              mkpath p = [congruence cwdg n | n <- thePath p]
                              ppDetail path = fromMaybe errMsg (ppsubsumed <|> ppsubproof)
                                  where errMsg = text "CANNOT find proof of path" <+> ppPathName path <> text "." 
                                                 <+> text "Propably computation has been aborted since some other path cannot be solved."
                                        ppsubsumed = do paths <- List.lookup path (subsumedBy tproof)
                                                        return $ (text "This path is subsumed by the proof of paths" 
                                                                  <+> sep (punctuate (text ",") [ppPathName pth | pth <- paths])
                                                                  <> text ".")
                                        ppsubproof = do subproof <- findSubProof path
                                                        return $ P.pprintProof subproof mde

    pprintTProof _ _ (Error e) _ = pprint e
    pprintTProof _ _ tproof    _ = block' "Transformation Details" [ppTrans]
        where ppTrans = paragraph "Following congruence DG was used:"
                        $+$ text ""
                        $+$ pprintCWDG cwdg (signature tproof) (variables tproof) (\ _ _ -> text "")
              cwdg = computedCongrDG tproof





pathAnalysisProcessor :: T.Transformation PathAnalysis P.AnyProcessor
pathAnalysisProcessor = T.Transformation PathAnalysis

-- | Implements path analysis. If the given argument is 'True', then
-- linear path analysis is employed.
pathAnalysis :: Bool -> T.TheTransformer PathAnalysis
pathAnalysis lin = T.Transformation PathAnalysis `T.withArgs` lin
-}
