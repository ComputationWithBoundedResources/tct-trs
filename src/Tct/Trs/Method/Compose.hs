{-# LANGUAGE RecordWildCards #-}
module Tct.Trs.Method.Compose 
  (
  decompose
  , decomposeDeclaration
  ) where

import           Data.Typeable
import           Control.Applicative

import qualified Data.Rewriting.Term           as R (isVariantOf)
import qualified Data.Rewriting.Rule           as R (Rule)

import qualified Tct.Core.Common.Parser        as P
import qualified Tct.Core.Common.Pretty        as PP
import qualified Tct.Core.Common.Xml           as Xml
import qualified Tct.Core.Data                 as T

import           Tct.Common.ProofCombinators

import qualified Tct.Trs.Data.Problem as Prob
import qualified Tct.Trs.Data.Rewriting        as R
import           Tct.Trs.Data.RuleSelector
import Tct.Trs.Data
import qualified Tct.Trs.Data.Trs as Trs

data DecomposeBound
  = Add
  | RelativeAdd
  | RelativeMul
  | RelativeComp
  deriving (Eq, Show, Typeable)

-- checks condition on R and S
isApplicableRandS :: (Ord f, Ord v) => Problem f v -> DecomposeBound -> Maybe String
isApplicableRandS prob compfn = case compfn of
  Add          -> Prob.isDCProblem' prob <|> Trs.isLinear' trs <|> Trs.isNonErasing' trs
  RelativeAdd  -> Nothing
  RelativeMul  -> Prob.isDCProblem' prob <|> Trs.isNonSizeIncreasing' trs
  RelativeComp -> Prob.isDCProblem' prob <|> Trs.isNonDuplicating' trs
  where trs = Prob.allComponents prob

-- for Add and RelativeComp rules in rProb have to be non-size increasing
selectForcedRules :: (Ord f, Ord v) => Problem f v -> DecomposeBound -> SelectorExpression f v
selectForcedRules prob compfn =
  BigAnd $ [SelectDP r | r <- forcedDps ] ++ [SelectTrs r | r <- forcedTrs ]
  where
    (forcedDps, forcedTrs) =
      case compfn of
        RelativeComp -> (fsi Prob.dpComponents, fsi Prob.trsComponents)
        Add          -> (fsi Prob.dpComponents, fsi Prob.trsComponents)
        _ -> ([],[])
        where fsi f = [ rule | rule <- Trs.toList (f prob), not (R.isNonSizeIncreasing rule)]

-- for Add rProb and sProb commute
isApplicableRModuloS :: (Ord f, Ord v) => Problem f v -> Problem f v -> DecomposeBound -> Maybe String
isApplicableRModuloS rProb sProb Add = Prob.note (not $ isCommutative rRules sRules) "commutative criterion not fulfilled"
  where (rRules, sRules)   = (Trs.toList $ Prob.allComponents rProb, Trs.toList $ Prob.allComponents sProb)
isApplicableRModuloS _ _ _ = Nothing

isCommutative :: (Ord f, Ord v) => [R.Rule f v] -> [R.Rule f v] -> Bool
isCommutative rRules' sRules' = isCommutative' 5 cps
  where
    rews               = R.rewrites (rRules' ++ sRules')
    reducts l          = iterate rews $ rews (R.rewrite rRules' l)
    reductOf r         = any (any (R.isVariantOf r))
    cps                = R.toPairs $ R.forwardPairs rRules' sRules'
    isCommutative' n    = all (\(l,r) -> r `reductOf` take n (reducts l))

mkProbs :: (Ord f, Ord v) => Problem f v -> DecomposeBound -> Trs f v -> Trs f v -> (Problem f v, Problem f v)
mkProbs prob compfn dps trs = (rProb, sProb)
  where
    rDps = dps `Trs.intersect` Prob.strictDPs prob
    rTrs = trs `Trs.intersect` Prob.strictTrs prob
    sDps = Prob.strictDPs prob `Trs.difference` rDps
    sTrs = Prob.strictTrs prob `Trs.difference` rTrs

    rProb = Prob.sanitise $ prob
      { Prob.strictDPs = rDps
      , Prob.strictTrs = rTrs
      , Prob.weakTrs   = sTrs `Trs.union` Prob.weakTrs prob
      , Prob.weakDPs   = sDps `Trs.union` Prob.weakDPs prob }

    sProb = Prob.sanitise $ case compfn of
      Add -> prob
        { Prob.strictTrs  = sTrs
        , Prob.strictDPs  = sDps
        , Prob.weakTrs    = rTrs `Trs.union` Prob.weakTrs prob
        , Prob.weakDPs    = rDps `Trs.union` Prob.weakDPs prob }
      _ -> prob
        { Prob.strictTrs  = sTrs
        , Prob.strictDPs  = sDps }

-- * ProofData

data DecomposeProof
  = DecomposeStaticProof
    { proofBound       :: DecomposeBound
    , proofSelectedTrs :: Trs F V
    , proofSelectedDPs :: Trs F V
    , proofSubProblems :: (TrsProblem, TrsProblem) }
    deriving Show

instance PP.Pretty DecomposeProof where
  pretty proof@DecomposeStaticProof{..}
    | progress proof = PP.vcat
        [ PP.text "We analyse the complexity of following sub-problems (R) and (S)."
        , case proofBound of
          Add -> PP.text
            "Problem (S) is obtained by removing rules in (R) from the input problem."
          RelativeAdd -> PP.text
            "Problem (S) is obtained from the input problem by shifting strict rules from (R) into the weak component."
          RelativeMul -> PP.paragraph $ unwords
            [ "Observe that Problem (R) is non-size-increasing. "
            , "Once the complexity of (R) has been assessed, it suffices "
            , "to consider only rules whose complexity has not been estimated in (R) "
            , "resulting in the following Problem (S). Overall the certificate is obtained by multiplication." ]
          RelativeComp -> PP.paragraph $ unwords
            [ "Observe that weak rules from Problem (R) are non-size-increasing. "
            , "Once the complexity of (R) has been assessed, it suffices "
            , "to consider only rules whose complexity has not been estimated in (R) "
            , "resulting in the following Problem (S). Overall the certificate is obtained by composition." ]
        , PP.empty
        , PP.text "Problem (R)"
        , PP.indent 2 $ PP.pretty (fst proofSubProblems)
        , PP.empty
        , PP.text "Problem (S)"
        , PP.indent 2 $ PP.pretty (snd proofSubProblems) ]
    | otherwise =  PP.text "No rule was selected."

instance Xml.Xml DecomposeProof where
  toXml _ = Xml.elt "decompose" []

progress :: DecomposeProof -> Bool
progress DecomposeStaticProof{..} =
  case proofBound of
    Add -> not $ Trs.null (Prob.allComponents rProb) || Trs.null (Prob.allComponents sProb)
    _   -> not $ Prob.isTrivial rProb || Prob.isTrivial sProb
    where  (rProb, sProb) = proofSubProblems


-- * Decompose Static

data DecomposeStaticProcessor = DecomposeStaticProc (ExpressionSelector F V) DecomposeBound
  deriving Show

instance T.Processor DecomposeStaticProcessor where
  type ProofObject DecomposeStaticProcessor = ApplicationProof DecomposeProof
  type Problem DecomposeStaticProcessor = TrsProblem
  type Forking DecomposeStaticProcessor = T.Pair
  solve p@(DecomposeStaticProc rs compfn) prob = return . T.resultToTree p prob $
    maybe decomposition (T.Fail . Inapplicable) maybeApplicable
    where
      decomposition
        | progress proof = T.Success (T.Pair (rProb,sProb)) (Applicable proof) undefined -- FIXME
        | otherwise      = T.Fail (Applicable proof)
      maybeApplicable = isApplicableRandS prob compfn <|> isApplicableRModuloS rProb sProb compfn
      (dps,trs) = rules $ BigAnd [ rsSelect rs prob, selectForcedRules prob compfn]
      (rProb, sProb) = mkProbs prob compfn dps trs
      proof = DecomposeStaticProof
        { proofBound       = compfn
        , proofSelectedTrs = trs
        , proofSelectedDPs = dps
        , proofSubProblems = (rProb, sProb) }


--- * Instances ------------------------------------------------------------------------------------------------------

decompose :: ExpressionSelector F V -> DecomposeBound -> T.Strategy TrsProblem
decompose rs = T.Proc . DecomposeStaticProc rs

decomposeDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional (ExpressionSelector F V)
   , T.Argument 'T.Optional DecomposeBound ]
   T.:-> T.Strategy TrsProblem )
decomposeDeclaration = T.declare "decomposeStatic" description (selectorArg', boundArg') decompose
  where
    boundArg'    = boundArg `T.optional` RelativeAdd
    selectorArg' = selectorArg `T.optional` selAnyOf selStricts

description :: [String]
description =
  [ "This transformation implements techniques for splitting the complexity problem"
  , "into two complexity problems (R) and (S) so that the complexity of the input problem"
  , "can be estimated by the complexity of the transformed problem."
  , "The processor closely follows the ideas presented in"
  , "/Complexity Bounds From Relative Termination Proofs/"
  , "(<http://www.imn.htwk-leipzig.de/~waldmann/talk/06/rpt/rel/main.pdf>)" ]

boundArg :: T.Argument 'T.Required DecomposeBound
boundArg = T.arg { T.argName = "allow", T.argDomain = "<bound>"} `T.withHelp` help
  where
    help =
      [ "This argument type determines"
      , "how the complexity certificate should be obtained from subproblems (R) and (S)."
      , "Consequently, this argument also determines the shape of (S)."
      , "<bound> is one of " ++ show [Add, RelativeAdd, RelativeMul, RelativeComp] ]

instance T.SParsable prob DecomposeBound where
  parseS = P.choice
    [ P.symbol (show Add) >> return Add
    , P.symbol (show RelativeAdd) >> return RelativeAdd
    , P.symbol (show RelativeMul) >> return RelativeMul
    , P.symbol (show RelativeComp) >> return RelativeComp ]

