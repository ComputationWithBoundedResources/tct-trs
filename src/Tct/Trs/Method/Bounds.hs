{- |
Module      :  Tct.Method.Bounds
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>,
               Georg Moser <georg.moser@uibk.ac.at>,
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>,
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
Stability   :  unstable
Portability :  unportable

This module implements the bounds processor.
-}

module Tct.Trs.Method.Bounds
  ( boundsDeclaration
  , bounds
  , bounds'
  , InitialAutomaton (..)
  , Enrichment (..)
  ) where

import qualified Data.Map                           as M
import           Data.Monoid
import qualified Data.Set                           as S
import           Data.Typeable

import qualified Data.Rewriting.Term                as R

import qualified Tct.Core.Common.Pretty             as PP
import qualified Tct.Core.Common.Xml                as Xml
import qualified Tct.Core.Data                      as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem               as Prob
import qualified Tct.Trs.Data.ProblemKind           as Prob
import qualified Tct.Trs.Data.Rewriting             as R
import qualified Tct.Trs.Data.Signature             as Sig
import qualified Tct.Trs.Data.Trs                   as Trs

import           Tct.Trs.Encoding.Bounds.Automata
import           Tct.Trs.Encoding.Bounds.Violations

-- | This datatype represents the initial automaton employed.
data InitialAutomaton
  = Minimal   -- ^ Employ a minimal set of states,
              -- separating constructors from defined symbols
              -- in the case of runtime complexity analysis.
  | PerSymbol -- ^ Employ a state per function symbol.
              -- Slower, but more precise compared to 'Minimal'.
  deriving (Typeable, Eq, Enum, Bounded)

mkMinRules :: S.Set Symbol -> Signature Symbol -> [State] -> State -> [Rule]
mkMinRules fs sig qs q = [ Collapse (f,0) (take (Sig.arity sig f) qs) q | f <- S.toList $ fs ]

minimalInitialAutomaton :: StartTerms Symbol -> Signature Symbol -> Automaton
minimalInitialAutomaton (Prob.AllTerms fs)   sig = fromRules [1] $ mkMinRules fs sig (repeat 1) 1
minimalInitialAutomaton (Prob.BasicTerms ds cs) sig = fromRules [2] $ mkMinRules ds sig (repeat 2) 1 ++ mkMinRules cs sig (repeat 2) 2

mkPerSymRules :: Signature Symbol -> S.Set Symbol -> Symbol -> [Rule]
mkPerSymRules sig fs f  = [ Collapse (f,0) args (fromEnum f) | args <- listProduct $ take (Sig.arity sig f) ffs ]
  where ffs = repeat [fromEnum g | g <- S.toList fs]

mkPerSymEmptyRules :: Signature Symbol -> State -> Symbol -> [Rule]
mkPerSymEmptyRules sig q f = [Collapse (f,0) (replicate (Sig.arity sig f) q) (fromEnum f)]

perSymInitialAutomaton :: StartTerms Symbol -> Signature Symbol -> Automaton
perSymInitialAutomaton (Prob.AllTerms fs) sign = fromRules [ fromEnum f | f <- fs'] $ concatMap (mkPerSymRules sign fs) fs'
   where fs' = S.toList fs
perSymInitialAutomaton (Prob.BasicTerms ds cs) sign = fromRules [ fromEnum f | f <- cs'] $ mk ds' ++ mk cs'
  where
    fs = S.toList $ ds `S.union` cs
    cs' = S.toList cs
    ds' = S.toList ds
    mk roots = concatMap mkBase roots
    mkBase = if null cs' then mkPerSymEmptyRules sign (maximum [ fromEnum f | f <- fs ] + 1) else mkPerSymRules sign cs

instance Show InitialAutomaton where
  show Minimal   = "minimal"
  show PerSymbol = "perSymbol"

data Bounds = Bounds
  { initialAutomaton_ :: InitialAutomaton
  , enrichment_       :: Enrichment }
  deriving Show

data GRule f
  = GCollapse (f,Label) [State] State
  | GEpsilon State State
  deriving Show

data GAutomaton f = GAutomaton
  { states_      :: [State]
  , boundHeight_ :: Int
  , finalStates_ :: [State]
  , transitions_ :: [GRule f] }
  deriving Show

data BoundsProof = BoundsProof Enrichment (GAutomaton F)
  deriving Show

instance T.Processor Bounds where
  type ProofObject Bounds = ApplicationProof BoundsProof
  type Problem Bounds     = TrsProblem
  type Forking Bounds     = T.Judgement

  -- FIXME: MS:
  -- this is wrong in many other cases; 
  -- a monadic action should always return after computation; otherwise concurrency is not handled correctly
  -- especially important for computation intensive - non-terminating computations
  solve p prob = boundHeight_ automaton `seq` return . T.resultToTree p prob $
    maybe apply (T.Fail . Inapplicable) maybeApplicable
    where
      apply = T.Success (T.Judgement) (Applicable proof) (T.judgement $ T.timeUBCert T.linear)
      maybeApplicable = Trs.isRightLinear' (strict `Trs.union` weak)

      strict       = Prob.strictComponents prob
      weak         = Prob.weakComponents prob
      sig          = Prob.signature prob
      st           = Prob.startTerms prob

      automaton = computeAutomaton sig st strict weak (enrichment_ p) (initialAutomaton_ p)
      proof = BoundsProof (enrichment_ p) automaton

computeAutomaton :: (Ord f, Ord v) => Signature f -> StartTerms f -> Trs f v -> Trs f v -> Enrichment -> InitialAutomaton -> GAutomaton f
computeAutomaton sig st strict weak enrichment initial = toGautomaton $ compatibleAutomaton strict' weak' enrichment $ case initial of
  PerSymbol -> perSymInitialAutomaton  st' sig'
  Minimal   -> minimalInitialAutomaton st' sig'
  where
    toGautomaton a = GAutomaton
      { states_      = states a
      , boundHeight_ = maximum $ 0 : snd `fmap` S.toList (symbols a)
      , finalStates_ = finalStates a
      , transitions_ = k `fmap` toRules a } 
      where
        k (Collapse (s,l) qs q) = GCollapse (canof s,l) qs q
        k (Epsilon p q)         = GEpsilon p q

    (fcano, canof) = ((fm M.!), (rm M.!))
      where
        fs = M.keys $ Sig.toMap sig
        fm = M.fromList $ zip fs [Symbol 1..]
        rm = M.fromList $ zip [Symbol 1..] fs
    tcano = R.map fcano id
    rcano = R.rmap tcano

    strict' = Trs.map rcano strict
    weak'   = Trs.map rcano weak
    st'     = Prob.mapStartTerms fcano st
    sig'    = Sig.fromMap . M.mapKeys fcano $ Sig.toMap sig


--- * instances ------------------------------------------------------------------------------------------------------

initialAutomatonArg :: T.Argument T.Required InitialAutomaton
initialAutomatonArg = T.arg
  `T.withName` "initial"
  `T.withHelp`
    [ "The employed initial automaton."
    , "If 'perSymbol' is set then the initial automaton admits one dedicated"
    , "state per function symbols."
    , "If 'minimal' is set then the initial automaton admits exactly"
    , "one state for derivational-complexity analysis. For runtime-complexity analysis, "
    , "two states are used in order to distinguish defined symbols from constructors." ]
  `T.withDomain` fmap show [(minBound :: InitialAutomaton)..]

enrichmentArg :: T.Argument T.Required Enrichment
enrichmentArg = T.arg
  `T.withName` "enrichment"
  `T.withHelp`
    [ "The employed enrichment." ]
  `T.withDomain` fmap show [(minBound :: Enrichment)..]

instance T.SParsable prob InitialAutomaton where
  parseS = T.mkEnumParser (undefined :: InitialAutomaton)

instance T.SParsable prob Enrichment where
  parseS = T.mkEnumParser (undefined :: Enrichment)

description :: [String]
description =
  [ "This processor implements the (match|roof|top)-bounds technique"
  , "that induces linear derivational- and runtime-complexity for right-linear problems."
  , "For non-right-linear problems this processor fails immediately."]

boundsStrategy :: InitialAutomaton -> Enrichment -> T.Strategy TrsProblem
boundsStrategy i e = T.Proc $ Bounds { initialAutomaton_=i, enrichment_=e }

boundsDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional InitialAutomaton
   , T.Argument 'T.Optional Enrichment ]
   T.:-> T.Strategy TrsProblem )
boundsDeclaration = T.declare "bounds" description (iArg, eArg) boundsStrategy
  where
    iArg = initialAutomatonArg `T.optional` Minimal
    eArg = enrichmentArg `T.optional` Match

bounds :: InitialAutomaton -> Enrichment -> T.Strategy TrsProblem
bounds = T.declFun boundsDeclaration

bounds' :: T.Strategy TrsProblem
bounds' = T.deflFun boundsDeclaration


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty BoundsProof where
  pretty (BoundsProof e a) = PP.vcat
    [ PP.text $ "The problem is " ++ show e ++ "-bounded by " ++ show (boundHeight_ a) ++ "."
    , PP.text $ "The enriched problem is compatible with follwoing automaton."
    , PP.indent 2 $ ppTransitions (transitions_ a) ]
    where
      ppTransitions = PP.vcat . fmap ppTransition
      ppTransition (GCollapse (f,l) qs q) = PP.pretty f <> PP.char '_' <> PP.int l <> PP.tupled' qs <> ppArrow <> PP.int q
      ppTransition (GEpsilon p q)         = PP.int p <> ppArrow <> PP.int q
      ppArrow = PP.text " -> "

instance Xml.Xml BoundsProof where
  toXml (BoundsProof e a) =
    Xml.elt "bounds"
      [ Xml.elt "type" [enrichmentToXml e]
      , Xml.elt "bound"  [Xml.int (boundHeight_ a)]
      , Xml.elt "finalStates" $ stateToXml `fmap` finalStates_ a
      , automatonToXml a ]
    where
      enrichmentToXml en = flip Xml.elt [] $ case en of
        Match -> "match"
        Roof  -> "roof"
        Top   -> "top"
      stateToXml q = Xml.elt "state" [Xml.int q]
      automatonToXml at =
        Xml.elt "treeAutomaton"
          [ Xml.elt "finalStates" $ stateToXml `fmap` states_ at
          , Xml.elt "transitions" $ transition `fmap` transitions_ at ]
        where
          transition (GCollapse (f,l) qs q) =
            Xml.elt "transition"
              [ Xml.elt "lhs" $
                  Xml.toXml f
                  : Xml.elt "height" [Xml.int l]
                  : stateToXml `fmap` qs
              , Xml.elt "rhs" [stateToXml q] ]
          transition (GEpsilon p q) =
            Xml.elt "transition"
              [ Xml.elt "lhs" [stateToXml p]
              , Xml.elt "rhs" [stateToXml q] ]
  toCeTA = Xml.toXml

