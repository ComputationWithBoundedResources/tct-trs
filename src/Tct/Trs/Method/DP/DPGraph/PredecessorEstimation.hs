{-|
This module provides the /Predecessor Estimation/ Processor.

@
  <Pre(S1#) + S2# + S / S1# + W# + W, Q, T#> :f
  ---------------------------------------------
      <S1# + S2# + S / W# + W, Q, T#> :f
@

Here @Pre(R#)@, is defined as the union of all direct predecessors of all rules in @R#@.

We compute @S1#@ from a 'ExpressionSelector' sucht that @Pre(S1#)@ is a subset of @S2#@, ie., all predeccessors occur
in the strict components.
-}
-- MS: TODO currently only the static variant is provided
-- we do not support solvePartial as in tct2
-- provide functions to easily integreate predecessorEstimation with other processors
module Tct.Trs.Method.DP.DPGraph.PredecessorEstimation
  ( predecessorEstimation
  , predecessorEstimationOn
  , predecessorEstimationOnDeclaration
  ) where


import           Control.Monad                (guard)
import           Data.List                    (find)
import           Data.Maybe                   (catMaybes)
import           Data.Monoid
import qualified Data.Rewriting.Rule          as R (Rule)

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import           Tct.Trs.Data.DependencyGraph
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.RuleSelector    as RS
import qualified Tct.Trs.Data.Trs             as Trs


data Selected = Selected
  { node  :: NodeId
  , rule  :: R.Rule F V
  , preds :: [(NodeId,R.Rule F V)]
  } deriving Show

data PredecessorEstimation = PredecessorEstimation
  { onSelection :: ExpressionSelector F V
  -- , withStrategy :: T.Strategy TrsProblem
  } deriving Show

data PredecessorEstimationProof
  = PredecessorEstimationProof
    { wdg_      :: DG F V
    , selected_ :: [Selected]}
  | PredecessorEstimationFail
  deriving Show


instance T.Processor (PredecessorEstimation) where
  type ProofObject PredecessorEstimation = ApplicationProof PredecessorEstimationProof
  type Problem PredecessorEstimation     = TrsProblem

  solve p prob =  return . T.resultToTree p prob $
    maybe estimate (T.Fail . Inapplicable) (Prob.isDPProblem' prob)
    where
      estimate
        | null candidates = T.Fail (Applicable PredecessorEstimationFail)
        | otherwise       = T.Success (T.toId nprob) (Applicable proof) T.fromId
        where
          wdg = Prob.dependencyGraph prob
          initialDPs = fst . RS.rules $ RS.rsSelect (RS.selFirstAlternative $ onSelection p) prob

          candidates = do
            (n,cn) <- lnodes wdg
            let predss = [ (n1,cn1) | (n1,cn1,_) <- lpredecessors wdg n ]
            guard $ isStrict cn && Trs.member (theRule cn) initialDPs
            guard $ all (\(n1,cn1) -> n1 /= n && isStrict cn1) predss
            return $ Selected { node=n, rule=theRule cn, preds=fmap theRule `map` predss }

          -- MS: estimate in bottom-upway
          sort cs = reverse $ catMaybes [find ((n==) . node) cs | n <- topsort wdg]
          select []     sel = sel
          select (c:cs) sel = select cs sel' where
            sel'
              | any (c `isPredecessorOf`) sel = sel
              | otherwise                     = c:sel
            s1 `isPredecessorOf` s2 = node s2 `elem` reachablesBfs wdg [node s1]


          selected = select (sort candidates) []

          shiftStrict = Trs.fromList [ r | s <- selected , (_,r) <- preds s ]
          shiftWeak   = Trs.fromList [ rule s | s <- selected ]
          nprob = prob
            { Prob.strictDPs = (Prob.strictDPs prob `Trs.difference` shiftWeak) `Trs.union` shiftStrict
            , Prob.weakDPs   = (Prob.weakDPs prob `Trs.union` shiftWeak) `Trs.difference` shiftStrict }
          proof = PredecessorEstimationProof
            { wdg_      = wdg
            , selected_ = selected }


--- * instances ------------------------------------------------------------------------------------------------------

predecessorEstimation :: T.Strategy TrsProblem
predecessorEstimation = T.defaultFun predecessorEstimationOnDeclaration

predecessorEstimationOn :: ExpressionSelector F V -> T.Strategy TrsProblem
predecessorEstimationOn sel = T.Proc $ PredecessorEstimation { onSelection=sel }

predecessorEstimationOnDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional (ExpressionSelector F V) ]
  T.:-> T.Strategy TrsProblem)
predecessorEstimationOnDeclaration =
  T.declare "predecessorEstimationOn" desc (T.OneTuple selArg) predecessorEstimationOn
  where
    desc =
      [ "Moves a strict dependency into the weak component, if all predecessors in the dependency graph are strict"
      , "and there is no edge from the rule to itself." ]
    selArg = RS.selectorArg
      `T.withName` "onSelection"
      `T.withHelp`
        [ "Determines which rules to select."
        , "Per default all dependency pairs are selected for knowledge propagation." ]
      `T.optional` (RS.selAllOf RS.selDPs)


--- * proof data -----------------------------------------------------------------------------------------------------

instance PP.Pretty PredecessorEstimationProof where
  pretty PredecessorEstimationFail = PP.text "Predecessor estimation is not applicable on selected rules."
  pretty p@PredecessorEstimationProof{} = PP.vcat
    [ PP.text "We estimate the number of application of"
    , PP.indent 2 ppEstimated
    , PP.text "by application of"
    , PP.indent 2 $ PP.text "Pre" <> PP.parens ppEstimated <> PP.text " = " <> ppPredecessors <> PP.dot
    , PP.text "Here rules are labeld as follows:"
    , PP.indent 2 $ ppRules ]
    where
      ppRules        = PP.pretty [ (n, theRule cn) | (n,cn) <- lnodes (wdg_ p) ]
      ppEstimated    = PP.set [ PP.int (node s) | s <- selected_ p ]
      ppPredecessors = PP.set [ PP.int n | s <- selected_ p, (n,_) <- preds s]

instance Xml.Xml PredecessorEstimationProof where
  toXml PredecessorEstimationFail      = Xml.elt "predecessorEstimation" []
  toXml p@PredecessorEstimationProof{} =
    Xml.elt "predecessorEstimation"
      [ Xml.toXml (wdg_ p)
      , Xml.elt "pe" $ concat
          [ [ Xml.toXml (node s,rule s)
            , Xml.elt "predecessors" [ Xml.toXml (n1,r1) | (n1,r1) <- preds s ]]
          | s <- selected_ p]
      ]

