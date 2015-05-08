{- | This module provides the /Dependency Graph Decomposition/ (/dependencyDG/) transformation.

@
  |- <Su# + S / Wu# + W, Q, T#>    |- <Sl# + S / Wl# + sep(Su# + Wu#) + W, Q, T#> :g
  ----------------------------------------------------------------------------------
      |- <Su# + Sl# + S / Wu# + Wl# + W, Q, T#> :f*g
@

, where
(1) @Sl# + Wl#@ is forward closed and
(2) @pre(Sl# + Wl#)@ and @Wu#@ have no common elements.

Here @sep(R#) = {l->ri | l -> Com(r1,...,rk) in R#}@.
-}
module Tct.Trs.Method.DP.DPGraph.DecomposeDG
  ( decomposeDGDeclaration
  , decomposeDG
  , decomposeDG'

  , decomposeDGselect

  -- * Processor
  , decomposeDGProc
  , decomposeDGProc'

  , DecomposeDG
  , selectLowerBy
  , solveLowerWith
  , solveUpperWith
  ) where


import qualified Data.List                    as L
import           Data.Monoid
import qualified Data.Set                     as S

import qualified Data.Rewriting.Rule          as R

import qualified Tct.Core.Common.Pretty       as PP
import           Tct.Core.Common.SemiRing
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import           Tct.Trs.Data.DependencyGraph
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.RuleSelector    as RS
import qualified Tct.Trs.Data.RuleSet         as Prob
import qualified Tct.Trs.Data.Trs             as Trs


data DecomposeDG = DecomposeDG
  { onSelection :: ExpressionSelector F V
  , onUpper     :: Maybe TrsStrategy
  , onLower     :: Maybe TrsStrategy
  } deriving Show

data DecomposeDGProof
  = DecomposeDGProof
    { wdg_         :: DG F V
    , unselected_  :: Trs F V
    , selected_    :: Trs F V
    , extension_   :: Trs F V }
  | DecomposeDGFail String
  deriving Show

certfn :: T.Pair T.Certificate -> T.Certificate
certfn (T.Pair (c1,c2)) = zero { T.timeUB = T.timeUB c1 `mul` T.timeUB c2, T.timeLB = T.timeLB c1 `add` T.timeLB c2}

instance T.Processor DecomposeDG where
  type ProofObject DecomposeDG = ApplicationProof DecomposeDGProof
  type I DecomposeDG     = TrsProblem
  type O DecomposeDG     = TrsProblem
  type Forking DecomposeDG     = T.Pair

  solve p prob = do
    maybe decomposition (return . T.resultToTree p prob . T.Fail . Inapplicable) (Prob.isDPProblem' prob)
    where
      decomposition
        | Trs.null initialDPs             = failx (Applicable $ DecomposeDGFail "no rules were selected")
        | not (any isCut unselectedNodes) = failx (Applicable $ DecomposeDGFail "no rule was cut")
        | prob `isSubsetDP` lowerProb     = failx (Applicable $ DecomposeDGFail "lower component not simpler")
        | otherwise                       = do
          lowerProof <- mapply (onLower p) lowerProb
          upperProof <- mapply (onUpper p) upperProb
          -- TODO: MS: what is the desired behaviour; currently we just ignore if they make any progress
          -- tct2 description states a similar behaviour; but the tct2 implementation requires that the processors suceeds
          case (lowerProof,upperProof) of
            (T.Halt _, _) -> failx (Applicable $ DecomposeDGFail "lower strategy floped")
            (_, T.Halt _) -> failx (Applicable $ DecomposeDGFail "upper strategy floped")
            (lpt, rpt)  ->
              return . T.Continue $ T.Progress (T.ProofNode p prob (Applicable proof)) certfn (T.Pair (T.fromReturn lpt, T.fromReturn rpt))
        where
          failx              = return . T.resultToTree p prob . T.Fail
          mapply s pr        = maybe (return . T.Continue $ T.Open pr) (flip T.evaluate pr) s
          p1 `isSubsetDP` p2 = Prob.strictDPs p1 `Trs.isSubset` Prob.strictDPs p2 && Prob.weakDPs p1 `Trs.isSubset` Prob.weakDPs p2

          wdg = Prob.dependencyGraph prob

          -- compute forward closed lower component from the selector (1)
          initialDPs = fst . RS.rules $ RS.rsSelect (RS.selFirstAlternative $ onSelection p) prob
          selected = withNodeLabels' wdg $ reachablesDfs wdg initialNodes
            where initialNodes = [ n | (n,nl) <- (lnodes wdg), theRule nl `Trs.member` initialDPs]
          (selectedNodes, selectedStrictDPs, selectedWeakDPs) = (S.fromList ns, Trs.fromList srs, Trs.fromList wrs)
            where (ns,srs,wrs) = withRulesPair' selected

          unselectedNodes  = filter (`S.notMember` selectedNodes) (nodes wdg)
          unselectedLNodes = withNodeLabels' wdg $ unselectedNodes

          -- to fulfill (2) we move weak predecessors in the upper component (cut nodes) to the strict component
          isCut n = any (`S.member` selectedNodes) (successors wdg n)
          (cutWeakDPs, uncutWeakDPs) = L.partition (isCut . fst) (filterWeak unselectedLNodes)
          unselectedStrictDPs = Trs.fromList $ asRules cutWeakDPs ++ asRules (filterStrict unselectedLNodes)
          unselectedWeakDPs   = Trs.fromList $ asRules uncutWeakDPs

          -- compute extension rules sep
          extension = sep unselectedStrictDPs `Trs.union` sep unselectedWeakDPs where
            sep = Trs.fromList . concatMap sepRule . Trs.toList
            sepRule (R.Rule l (R.Fun f ts)) | Prob.isCompoundf f = [ R.Rule l ti | ti <- ts ]
            sepRule (R.Rule l r) = [ R.Rule l r ]

          -- TODO: proper dp graph update
          upperProb = Prob.sanitiseDPGraph $ prob
            { Prob.strictDPs = unselectedStrictDPs
            , Prob.weakDPs   = unselectedWeakDPs }

          lowerProb = Prob.sanitiseDPGraph $ prob
            { Prob.strictDPs = selectedStrictDPs
            , Prob.weakDPs   = extension `Trs.union` selectedWeakDPs }

          proof = DecomposeDGProof
            { wdg_         = wdg
            , selected_    = selectedStrictDPs `Trs.union` selectedWeakDPs
            , unselected_  = Trs.fromList $ asRules unselectedLNodes
            , extension_   = extension }


--- * instances ------------------------------------------------------------------------------------------------------

-- | This is the default 'RuleSelector' used with 'decomposeDG'.
decomposeDGselect :: ExpressionSelector F V
decomposeDGselect = RS.selAllOf (RS.selFromDG f) { RS.rsName = "below first cut in WDG" }
  where
    f dg = Prob.emptyRuleSet
      { Prob.sdps = Trs.fromList selectedStrict
      , Prob.wdps = Trs.fromList selectedWeak }
      where
        wdg = dependencyGraph dg
        cdg = congruenceGraph dg

        snub = S.toList . S.fromList
        cyclic = isCyclicNode cdg

        (selectedStrict,selectedWeak) = allRulesPairFromNodes cdg (snub $ concat $ [ successors cdg n | n <-S.toList cutNodes])

        cutNodes = S.unions [ cutNodesFrom r (cyclic r) | r <- roots cdg ]
          where
            cutNodesFrom n isCyclic'
              | isCutCongruence n = S.singleton n
              | otherwise         = S.unions [ cutNodesFrom m (isCyclic' || cyclic m) | m <- successors cdg n ]
            isCutCongruence n = any isCut ms
              where
                ms = [ m | (m,_) <- theSCC $ lookupNodeLabel' cdg n ]
                isCut m = not . null $
                  [ (m1,m2) | let lsuccs = lsuccessors wdg m
                    , (m1, _, i) <- lsuccs
                    , m1 `elem` ms
                    , (m2, _, j) <- lsuccs
                    , i /= j
                    , m2 `notElem` ms ]

decomposeDGProcessor :: ExpressionSelector F V -> Maybe TrsStrategy -> Maybe TrsStrategy
  -> DecomposeDG
decomposeDGProcessor sel st1 st2 = DecomposeDG
  { onSelection = sel
  , onUpper     = st1
  , onLower     = st2 }

help :: [String]
help =
  [ "This processor implements processor 'compose' specifically for the"
  , "(weak) dependency pair setting."
  , "It tries to estimate the complexity of the input problem"
  , "based on the complexity of dependency pairs of upper congruence classes"
  , "(with respect to the congruence graph)"
  , "relative to the dependency pairs in the remaining lower congruence classes."
  , "The overall upper bound for the complexity of the input problem"
  , "is estimated by multiplication of upper bounds of the sub problems."
  , "Note that the processor allows the optional specification of processors"
  , "that are applied on the two individual subproblems."
  , "The transformation results into the systems which could not be oriented"
  , "by those processors." ]

selArg :: T.Argument 'T.Optional (ExpressionSelector F V)
selArg = RS.selectorArg
  `T.withName` "onSelection"
  `T.withHelp`
    [ "Determines the strict rules of the selected upper conguence rules." ]
  `T.optional` decomposeDGselect

upperArg :: T.Argument 'T.Optional (Maybe TrsStrategy)
upperArg = T.some T.strat
  `T.withName` "onUpper"
  `T.withHelp` ["Use this processor to solve the upper component."]
  `T.optional` Nothing

lowerArg :: T.Argument 'T.Optional (Maybe TrsStrategy)
lowerArg = T.some T.strat
  `T.withName` "onLower"
  `T.withHelp` ["Use this processor to solve the lower component."]
  `T.optional` Nothing

decomposeDGProcDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional (ExpressionSelector F V)
   , T.Argument 'T.Optional (Maybe TrsStrategy)
   , T.Argument 'T.Optional (Maybe TrsStrategy) ]
  T.:-> DecomposeDG)
decomposeDGProcDeclaration = T.declare "decomposeDG" help (selArg,upperArg,lowerArg) decomposeDGProcessor


decomposeDGProc :: 
  ExpressionSelector F V -> Maybe TrsStrategy -> Maybe TrsStrategy
  -> (DecomposeDG -> DecomposeDG) -> TrsStrategy
decomposeDGProc sel st1 st2 f = T.Proc . f $ T.declFun decomposeDGProcDeclaration sel st1 st2

decomposeDGProc' :: (DecomposeDG -> DecomposeDG) -> TrsStrategy
decomposeDGProc' f = T.Proc . f $ T.deflFun decomposeDGProcDeclaration

solveUpperWith :: TrsStrategy -> DecomposeDG -> DecomposeDG
solveUpperWith st p = p{ onUpper=Just st } 

solveLowerWith :: TrsStrategy -> DecomposeDG -> DecomposeDG
solveLowerWith st p = p{ onLower=Just st } 

selectLowerBy :: ExpressionSelector F V -> DecomposeDG -> DecomposeDG
selectLowerBy sel p = p{ onSelection=sel }

-- | This processor implements processor \'dependency graph decomposition\'.
-- It tries to estimate the
-- complexity of the input problem based on the complexity of
-- dependency pairs of upper congruence classes (with respect to the
-- congruence graph) relative to the dependency pairs in the remaining
-- lower congruence classes. The overall upper bound for the
-- complexity of the input problem is estimated by multiplication of
-- upper bounds of the sub problems.
-- Note that the processor allows the optional specification of
-- processors that are applied on the two individual subproblems. The
-- transformation results into the systems which could not be oriented
-- by those processors.
decomposeDGDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional (ExpressionSelector F V)
   , T.Argument 'T.Optional (Maybe TrsStrategy)
   , T.Argument 'T.Optional (Maybe TrsStrategy) ]
  T.:-> TrsStrategy)
decomposeDGDeclaration = T.declare "decomposeDG" help (selArg,upperArg,lowerArg) (\x y z -> T.Proc (decomposeDGProcessor x y z))

decomposeDG :: ExpressionSelector F V -> Maybe TrsStrategy -> Maybe TrsStrategy -> TrsStrategy
decomposeDG = T.declFun decomposeDGDeclaration

decomposeDG' :: TrsStrategy
decomposeDG' = T.deflFun decomposeDGDeclaration


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty DecomposeDGProof where
  pretty (DecomposeDGFail reason) =
    PP.text "Dependency graph decomposition failed: " <> PP.text reason <> PP.dot
  pretty p@DecomposeDGProof{}     = PP.vcat . L.intersperse PP.empty $
    [ PP.text "We decompose the input problem according to the dependency graph into the upper component"
    , PP.indent 2 $ PP.pretty (unselected_ p)
    , PP.text "and a lower component"
    , PP.indent 2 $ PP.pretty (selected_ p)
    , PP.text "Further, following extension rules are added to the lower component."
    , PP.indent 2 $ PP.pretty (extension_ p) ]

instance Xml.Xml DecomposeDGProof where
  toXml (DecomposeDGFail s) = Xml.elt "decomposeDG" [Xml.text s]
  toXml DecomposeDGProof{}  = Xml.elt "decomposeDG" [] -- TODO

