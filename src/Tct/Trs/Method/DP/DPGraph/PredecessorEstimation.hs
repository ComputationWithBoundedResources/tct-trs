{-|
This module provides the /Predecessor Estimation/ and the /Predecessor Estimation CP/ processor.

@
  |- <pre(S1#) + S2# + S / S1# + W# + W, Q, T#> :f
  ------------------------------------------------
      |- <S1# + S2# + S / W# + W, Q, T#> :f
@

Here @pre(R#)@, is defined as the union of all direct predecessors of all rules in @R#@.

We compute @S1#@ from a 'ExpressionSelector' sucht that @pre(S1#)@ is a subset of @S2#@, ie., all predeccessors occur
in the strict components.
-}
-- MS: TODO:
-- the subproof for predecessor estimation cp is currently stored as closed left branch (using assumption)
-- good: normally printed; (partially) certificable
-- bad: the (generic) proof output is a bit awkward
module Tct.Trs.Method.DP.DPGraph.PredecessorEstimation
  ( predecessorEstimationDeclaration
  , predecessorEstimation
  , predecessorEstimation'

  , predecessorEstimationCPDeclaration
  , predecessorEstimationCP
  , predecessorEstimationCP'
  ) where


import           Control.Applicative           ((<$>), (<|>))
import           Control.Monad                 (guard)
import           Data.List                     (find)
import           Data.Maybe                    (catMaybes)
import           Data.Monoid
import qualified Data.Set                      as S

import qualified Data.Rewriting.Rule           as R (Rule)

import qualified Tct.Core.Common.Pretty        as PP
import           Tct.Core.Common.SemiRing      (bigAdd, zero)
import qualified Tct.Core.Common.Xml           as Xml
import qualified Tct.Core.Data                 as T
import           Tct.Core.Processor.Assumption (assumeWith)

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import qualified Tct.Trs.Data.ComplexityPair   as CP
import           Tct.Trs.Data.DependencyGraph
import qualified Tct.Trs.Data.Problem          as Prob
import qualified Tct.Trs.Data.RuleSelector     as RS
import qualified Tct.Trs.Data.Trs              as Trs

import qualified Tct.Trs.Method.ComplexityPair as CP



data Selected = Selected
  { node  :: NodeId
  , rule  :: R.Rule F V
  , preds :: [(NodeId,R.Rule F V)]
  } deriving Show


data PredecessorEstimation = PredecessorEstimation
  { onSelection :: ExpressionSelector F V }
  deriving Show

data PredecessorEstimationProof
  = PredecessorEstimationProof
    { wdg_      :: DG F V
    , selected_ :: [Selected] }
  | PredecessorEstimationCPProof
    { wdg_      :: DG F V
    , selected_ :: [Selected]
    , cp_       :: ComplexityPair
    , cpproof_  :: ComplexityPairProof
    , cpcert_   :: T.Certificate }
  | PredecessorEstimationFail
  deriving Show


instance T.Processor (PredecessorEstimation) where
  type ProofObject PredecessorEstimation = ApplicationProof PredecessorEstimationProof
  type I PredecessorEstimation           = TrsProblem
  type O PredecessorEstimation           = TrsProblem

  solve p prob = T.resultToTree p prob <$>
    maybe estimate  (return . T.Fail . Inapplicable) (Prob.isDPProblem' prob)
    where
      wdg  = Prob.dependencyGraph prob
      sdps = Prob.strictDPs prob
      wdps = Prob.weakDPs prob

      estimate
        | null candidates = return $ T.Fail (Applicable PredecessorEstimationFail)
        | otherwise       = return $ T.Success (T.toId nprob) (Applicable proof) T.fromId
        where
          initialDPs = RS.dpRules $ RS.rsSelect (RS.selFirstAlternative $ onSelection p) prob

          candidates = do
            (n,cn) <- lnodes wdg
            let predss = [ (n1,cn1) | (n1,cn1,_) <- lpredecessors wdg n ]
            guard $ isStrict cn && Trs.member (theRule cn) initialDPs
            guard $ all (\(n1,cn1) -> n1 /= n && isStrict cn1) predss
            return $ Selected { node=n, rule=theRule cn, preds=fmap theRule `map` predss }

          -- estimate in bottom-upway
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
          -- MS: TODO: dpgraph modify isStrict for selected ones
          nprob = Prob.sanitiseDPGraph $ prob
            { Prob.strictDPs = (sdps `Trs.difference` shiftWeak) `Trs.union` shiftStrict
            , Prob.weakDPs   = (wdps `Trs.union` shiftWeak) `Trs.difference` shiftStrict }
          proof = PredecessorEstimationProof
            { wdg_      = wdg
            , selected_ = selected }


data PredecessorEstimationCP = PredecessorEstimationCP
  { onSelectionCP      :: ExpressionSelector F V
  , withComplexityPair :: ComplexityPair }
  deriving Show

instance T.Processor PredecessorEstimationCP where
  type ProofObject PredecessorEstimationCP = ApplicationProof PredecessorEstimationProof
  type I PredecessorEstimationCP           = TrsProblem
  type O PredecessorEstimationCP           = TrsProblem
  type Forking PredecessorEstimationCP     = T.Pair

  solve p prob =
    maybe (estimate $ withComplexityPair p) (return . T.resultToTree p prob . T.Fail . Inapplicable) (Prob.isDPProblem' prob)
    where
      wdg  = Prob.dependencyGraph prob
      sdps = Prob.strictDPs prob
      wdps = Prob.weakDPs prob

      estimate (CP.ComplexityPair cp) = do
        let
          rs = RS.RuleSelector
            { RS.rsName   = "first alternative for predecessorEstimation " ++ RS.rsName rs
            , RS.rsSelect = withPredecessors . RS.rsSelect (onSelectionCP p) }

        cpproof <- CP.solveComplexityPair cp rs prob
        case cpproof of
            T.Continue cpp -> mkProof cpp
            T.Abort _      -> return . T.resultToTree p prob $ T.Fail (Applicable PredecessorEstimationFail)
            T.Flop         -> return T.Flop

        where
          snub = S.toList . S.fromList

          withPredecessors (RS.SelectDP d) = RS.BigOr $ RS.SelectDP d : predss
            where
              predss = case lookupNode wdg DGNode{theRule=d, isStrict=True} <|> lookupNode wdg DGNode{theRule=d,isStrict=False} of
                Just n  -> [ withPreds n (S.singleton n) ]
                Nothing -> []
              withPreds n seen = bigAnd (k `fmap` snub [ (n', theRule cn') | (n',cn',_) <- lpredecessors wdg n])
                where
                  k (n',r') = if n' `S.member` seen then RS.SelectDP r' else RS.BigOr [RS.SelectDP r', withPreds n' (n' `S.insert` seen) ]
                  bigAnd [a] = a
                  bigAnd as  = RS.BigAnd as

          withPredecessors (RS.SelectTrs ss) = RS.SelectTrs ss
          withPredecessors (RS.BigOr ss)     = RS.BigOr (withPredecessors `fmap` ss)
          withPredecessors (RS.BigAnd ss)    = RS.BigAnd (withPredecessors `fmap` ss)

          mkProof cpproof
            | Trs.null shiftWeak = return . T.resultToTree p prob $ T.Fail (Applicable PredecessorEstimationFail)
            | otherwise          = return . T.Continue $ T.Progress pn bigAdd (T.Pair (subProof, T.Open nprob))

            where
              pn = T.ProofNode
                { T.processor = p
                , T.problem   = prob
                , T.proof     = Applicable proof }

              (known, propagated) = propagate (CP.removableDPs cpproof) []
              propagate seen props
                  | null newp = (seen, props)
                  | otherwise = propagate (Trs.fromList (rule `fmap` newp) `Trs.union` seen) (newp ++ props)
                where
                  newp = do
                    (n,cn) <- lnodes wdg
                    guard $ not (theRule cn `Trs.member` seen)
                    let predss = [ (n1,theRule cn1) | (n1,cn1,_) <- lpredecessors wdg n ]
                    guard $ all (\(_,r) -> r `Trs.member` seen) predss
                    return $ Selected { node=n, rule=theRule cn, preds=predss }

              shiftWeak = sdps `Trs.intersect` known
              nprob = Prob.sanitiseDPGraph $ prob
                { Prob.strictDPs = (sdps `Trs.difference` shiftWeak)
                , Prob.weakDPs   = (wdps `Trs.union` shiftWeak) }
              subProof = assumeWith (T.timeUBCert zero) (CP.result cpproof)
              proof = PredecessorEstimationCPProof
                { wdg_      = wdg
                , selected_ = propagated
                , cp_       = withComplexityPair p
                , cpproof_  = cpproof
                , cpcert_   = T.certificate subProof }


--- * instances ------------------------------------------------------------------------------------------------------

description :: [String]
description =
  [ "Moves a strict dependency into the weak component, if all predecessors in the dependency graph are strict"
  , "and there is no edge from the rule to itself." ]

selArg :: T.Argument 'T.Optional (ExpressionSelector F V)
selArg = RS.selectorArg
  `T.withName` "onSelection"
  `T.withHelp`
    [ "Determines which rules to select."
    , "Per default all dependency pairs are selected for knowledge propagation." ]
  `T.optional` (RS.selAllOf RS.selDPs)


--- ** Predecessor Estimation ----------------------------------------------------------------------------------------

predecessorEstimationStrategy :: ExpressionSelector F V -> TrsStrategy
predecessorEstimationStrategy rs = T.Proc $ PredecessorEstimation { onSelection = rs }

predecessorEstimationDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional (ExpressionSelector F V) ]
   T.:-> TrsStrategy )
predecessorEstimationDeclaration =
  T.declare "predecessorEstimation" description (T.OneTuple selArg) predecessorEstimationStrategy

predecessorEstimation :: ExpressionSelector F V -> TrsStrategy
predecessorEstimation = T.declFun predecessorEstimationDeclaration

predecessorEstimation' :: TrsStrategy
predecessorEstimation' = T.deflFun predecessorEstimationDeclaration


--- ** Predecessor Estimation CP -------------------------------------------------------------------------------------

predecessorEstimationCPStrategy :: ExpressionSelector F V -> ComplexityPair -> TrsStrategy
predecessorEstimationCPStrategy rs cp = T.Proc $ PredecessorEstimationCP { onSelectionCP = rs, withComplexityPair = cp }

predecessorEstimationCPDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional (ExpressionSelector F V)
   , T.Argument 'T.Required ComplexityPair ]
   T.:-> TrsStrategy )
predecessorEstimationCPDeclaration =
  T.declare "predecessorEstimationCP" description (selArg, CP.cpArg) predecessorEstimationCPStrategy

predecessorEstimationCP :: ExpressionSelector F V -> ComplexityPair -> TrsStrategy
predecessorEstimationCP = T.declFun predecessorEstimationCPDeclaration

predecessorEstimationCP' :: ComplexityPair -> TrsStrategy
predecessorEstimationCP' = T.deflFun predecessorEstimationCPDeclaration


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
  pretty p@PredecessorEstimationCPProof{} = PP.vcat
    [ PP.text $ "We first use the processor " ++ show (cp_ p) ++ " to orient following rules strictly:"
    , PP.indent 2 $ PP.listing' rdps
    , PP.indent 2 . PP.pretty $ CP.removableTrs (cpproof_ p)
    , if null (selected_ p)
        then PP.text "The strictly oriented rules are moved into the weak component."
        else PP.vcat
          [ PP.text "Consider the set of all dependency pairs"
          , PP.indent 2 (PP.listing' ndps)
          , PP.text ("Processor " ++ show (cp_ p) ++ "induces the complexity certificate")
            <> PP.pretty (cpcert_ p)
            <> PP.text "on application of the dependency pairs"
          , PP.indent 2 (PP.set' orientedNodes)
          , PP.text "These cover all (indirect) predecessors of dependency pairs"
          , PP.indent 2 (PP.set' knownNodes)
          , PP.text "their number of applications is equally bounded."
          , PP.text "The dependency pairs are shifted into the weak component."] ]
    where
      remdps = CP.removableDPs (cpproof_ p)
      ndps   = asNodedRules $ lnodes (wdg_ p)
      rdps   = filter ((`Trs.member` remdps) . snd) ndps

      orientedNodes = S.fromList $ fst (unzip rdps)
      knownNodes    = orientedNodes `S.union` S.fromList (node `fmap` (selected_ p))


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
  -- MS: TODO:
  toXml PredecessorEstimationCPProof{} = Xml.empty

