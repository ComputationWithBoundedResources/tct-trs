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

This module implements the (relative-) bounds processor.
-}

module Tct.Trs.Method.Bounds
  ( boundsDeclaration
  , bounds
  , bounds'
  , InitialAutomaton (..)
  , Enrichment (..)
  ) where

import Data.Maybe (fromMaybe)
import qualified Data.Map                           as M
import           Data.Monoid                        ((<>))
import qualified Data.Set                           as S
import           Data.Typeable                      (Typeable)

import qualified Data.Rewriting.Term                as R

import qualified Tct.Core.Common.Parser             as P
import qualified Tct.Core.Common.Pretty             as PP
import           Tct.Core.Common.SemiRing           as PP (add)
import qualified Tct.Core.Common.Xml                as Xml
import qualified Tct.Core.Data                      as T
import           Tct.Core.Combinators               ((.>>>))

import           Tct.Common.ProofCombinators        (ApplicationProof(..))

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem               as Prob
import qualified Tct.Trs.Data.ProblemKind           as Prob
import qualified Tct.Trs.Data.Rewriting             as R
import qualified Tct.Trs.Data.Signature             as Sig
import qualified Tct.Trs.Data.Trs                   as Trs
import qualified Tct.Trs.Method.Empty               as E (empty)

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
    fs  = S.toList $ ds `S.union` cs
    cs' = S.toList cs
    ds' = S.toList ds
    mk  = concatMap mkBase
    mkBase = if null cs' then mkPerSymEmptyRules sign (maximum [ fromEnum f | f <- fs ] + 1) else mkPerSymRules sign cs

instance Show InitialAutomaton where
  show Minimal   = "minimal"
  show PerSymbol = "perSymbol"

data Bounds = Bounds
  { initialAutomaton :: InitialAutomaton
  , enrichment       :: Enrichment }
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

data BoundsProof = BoundsProof
  { enrichment_ :: Enrichment
  , automaton_  :: GAutomaton F
  , strict_     :: Trs F V }
  deriving Show

instance T.Processor Bounds where
  type ProofObject Bounds = ApplicationProof BoundsProof
  type I Bounds           = TrsProblem
  type O Bounds           = TrsProblem

  solve p prob =  fmap (T.resultToTree p prob) $
    maybe apply (return . T.Fail . Inapplicable) maybeApplicable
    where
      apply = boundHeight_ automaton `seq`
        return $ T.Success (T.toId nprob) (Applicable proof) (flip T.updateTimeUBCert (`add` T.linear) . T.fromId)
      maybeApplicable = Trs.isRightLinear' (strict `Trs.union` weak)

      strict = Prob.strictComponents prob
      weak   = Prob.weakComponents prob
      sig    = Prob.signature prob
      st     = Prob.startTerms prob

      automaton = computeAutomaton sig st strict weak (enrichment p) (initialAutomaton p)

      -- MS: the problem is actually already solved; but we return a trivial problem so certificatioin is easier to handle
      nprob = Prob.sanitiseDPGraph $ prob
        { Prob.strictDPs = Trs.empty
        , Prob.strictTrs = Trs.empty
        , Prob.weakDPs   = Prob.weakDPs prob `Trs.union` Prob.strictDPs prob
        , Prob.weakTrs   = Prob.weakTrs prob `Trs.union` Prob.strictTrs prob }
      proof = BoundsProof
        { enrichment_ = enrichment p
        , automaton_  = automaton
        , strict_     = strict }

computeAutomaton :: (Ord f, Ord v) => Signature f -> StartTerms f -> Trs f v -> Trs f v -> Enrichment -> InitialAutomaton -> GAutomaton f
computeAutomaton sig st strict weak enrich initial = toGautomaton $ compatibleAutomaton strict' weak' enrich $ case initial of
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

    find m f = error ("Bounds.cano: not found:") `fromMaybe` M.lookup f m

    (fcano, canof) = (find fm, find rm)
      where
        fs = M.keys $ Sig.toMap sig
        fm = M.fromList $ zip fs [Symbol 1..]
        rm = M.fromList $ zip [Symbol 1..] fs
    tcano = R.map fcano id
    rcano = R.rmap tcano

    strict' = Trs.map rcano strict
    weak'   = Trs.map rcano weak
    st'     = Prob.mapStartTerms fcano st
    sig'    = Sig.map fcano sig


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

instance T.SParsable i i InitialAutomaton where
  parseS = P.enum

instance T.SParsable i i Enrichment where
  parseS = P.enum

description :: [String]
description =
  [ "This processor implements the (match|roof|top)-bounds technique"
  , "that induces linear derivational- and runtime-complexity for right-linear problems."
  , "For non-right-linear problems this processor fails immediately."]

boundsStrategy :: InitialAutomaton -> Enrichment -> TrsStrategy
boundsStrategy i e = T.Proc (Bounds { initialAutomaton = i, enrichment = e }) .>>> E.empty

boundsDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional InitialAutomaton
   , T.Argument 'T.Optional Enrichment ]
   T.:-> TrsStrategy )
boundsDeclaration = T.declare "bounds" description (iArg, eArg) boundsStrategy
  where
    iArg = initialAutomatonArg `T.optional` Minimal
    eArg = enrichmentArg `T.optional` Match

bounds :: InitialAutomaton -> Enrichment -> TrsStrategy
bounds = T.declFun boundsDeclaration

bounds' :: TrsStrategy
bounds' = T.deflFun boundsDeclaration


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty BoundsProof where
  pretty p = PP.vcat
    [ PP.text $ "The problem is " ++ show (enrichment_ p) ++ "-bounded by " ++ show (boundHeight_ $ automaton_ p) ++ "."
    , PP.text $ "The enriched problem is compatible with follwoing automaton."
    , PP.indent 2 $ ppTransitions (transitions_ $ automaton_ p) ]
    where
      ppTransitions = PP.vcat . fmap ppTransition
      ppTransition (GCollapse (f,l) qs q) = PP.pretty f <> PP.char '_' <> PP.int l <> PP.tupled' qs <> ppArrow <> PP.int q
      ppTransition (GEpsilon q1 q2)         = PP.int q1 <> ppArrow <> PP.int q2
      ppArrow = PP.text " -> "


instance Xml.Xml BoundsProof where
  toXml p = Xml.elt "relativeBounds" [xbounds, xtrs] where
    xbounds = Xml.elt "bounds"
        [ Xml.elt "type" [xenrichment (enrichment_ p)]
        , Xml.elt "bound"  [Xml.int (boundHeight_ $ automaton_ p)]
        , Xml.elt "finalStates" $ xstate `fmap` finalStates_ (automaton_ p)
        , xautomaton (automaton_ p) ]
      where
        xenrichment en = flip Xml.elt [] $ case en of
          Match -> "match"
          Roof  -> "roof"
          Top   -> "top"
        xstate q = Xml.elt "state" [Xml.int q]
        xautomaton at =
          Xml.elt "treeAutomaton"
            [ Xml.elt "finalStates" $ xstate `fmap` states_ at
            , Xml.elt "transitions" $ xtransition `fmap` transitions_ at ]
          where
            xtransition (GCollapse (f,l) qs q) =
              Xml.elt "transition"
                [ Xml.elt "lhs" $
                    Xml.toXml f
                    : Xml.elt "height" [Xml.int l]
                    : xstate `fmap` qs
                , Xml.elt "rhs" [xstate q] ]
            xtransition (GEpsilon q1 q2) =
              Xml.elt "transition"
                [ Xml.elt "lhs" [xstate q1]
                , Xml.elt "rhs" [xstate q2] ]
    xtrs = Xml.elt "trs" [Xml.toXml (strict_ p)]
  toCeTA p
    | enrichment_ p == Top = Xml.unsupported
    | otherwise            = Xml.toXml p

