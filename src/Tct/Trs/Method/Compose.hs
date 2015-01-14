{-# LANGUAGE RecordWildCards #-}
module Tct.Trs.Method.Compose 
  (
  decompose
  , decomposeStatic
  , decomposeStaticDeclaration
  ) where

import           Control.Monad.Trans           (lift)
import           Data.Typeable

import qualified Data.Rewriting.Term           as R (isVariantOf)

import qualified Tct.Core.Common.Parser        as P
import qualified Tct.Core.Common.Pretty        as PP
import qualified Tct.Core.Common.Xml           as Xml
import           Tct.Core.Common.SemiRing
import qualified Tct.Core.Data                 as T

import           Tct.Common.ProofCombinators

import           Control.Applicative
import           Tct.Trs.Data.PartialProcessor
import           Tct.Trs.Data.Problem
import qualified Tct.Trs.Data.Rewriting        as R
import           Tct.Trs.Data.RuleSelector
import           Tct.Trs.Data.Trs


data DecomposeBound
  = Add
  | RelativeAdd
  | RelativeMul
  | RelativeComp
  deriving (Eq, Show, Typeable)

-- checks condition on R and S
isApplicableRandS :: Problem -> DecomposeBound -> Maybe String
isApplicableRandS prob compfn = case compfn of
  Add          -> isDCProblem' prob <|> isLinear' trs <|> isNonErasing' trs
  RelativeAdd  -> Nothing
  RelativeMul  -> isDCProblem' prob <|> isNonSizeIncreasing' trs
  RelativeComp -> isDCProblem' prob <|> isNonDuplicating' trs
  where trs = allComponents prob

-- for Add and RelativeComp rules in rProb have to be non-size increasing
selectForcedRules :: Problem -> DecomposeBound -> SelectorExpression
selectForcedRules prob compfn =
  BigAnd $ [SelectDP r | r <- forcedDps ]
             ++ [SelectTrs r | r <- forcedTrs ]
  where
    (forcedDps, forcedTrs) =
      case compfn of
        RelativeComp -> (fsi dpComponents, fsi trsComponents)
        Add          -> (fsi dpComponents, fsi trsComponents)
        _ -> ([],[])
        where fsi f = [ rule | rule <- ruleList (f prob), not (R.isNonSizeIncreasing rule)]

-- for Add rProb and sProb commute
isApplicableRModuloS :: Problem -> Problem -> DecomposeBound -> Maybe String
isApplicableRModuloS rProb sProb Add = note (not $ isCommutative rRules sRules) "commutative criterion not fulfilled"
  where (rRules, sRules)   = (ruleList $ allComponents rProb, ruleList $ allComponents sProb)
isApplicableRModuloS _ _ _ = Nothing

isCommutative :: [Rule] -> [Rule] -> Bool
isCommutative rRules' sRules' = isCommutative' 5 cps
  where
    rews               = R.rewrites (rRules' ++ sRules')
    reducts l          = iterate rews $ rews (R.rewrite rRules' l)
    reductOf r         = any (any (R.isVariantOf r))
    cps                = R.toPairs $ R.forwardPairs rRules' sRules'
    isCommutative' n    = all (\(l,r) -> r `reductOf` take n (reducts l))

mkProbs :: Problem -> DecomposeBound -> Trs -> Trs -> (Problem, Problem)
mkProbs prob compfn dps trs = (rProb, sProb)
  where
    rDps = dps `intersect` strictDPs prob
    rTrs = trs `intersect` strictTrs prob
    sDps = strictDPs prob `difference` rDps
    sTrs = strictTrs prob `difference` rTrs

    rProb = sanitise $ prob
      { strictDPs = rDps
      , strictTrs = rTrs
      , weakTrs   = sTrs `union` weakTrs prob
      , weakDPs   = sDps `union` weakDPs prob }

    sProb = sanitise $ case compfn of
      Add -> prob
        { strictTrs  = sTrs
        , strictDPs  = sDps
        , weakTrs    = rTrs `union` weakTrs prob
        , weakDPs    = rDps `union` weakDPs prob }
      _ -> prob
        { strictTrs  = sTrs
        , strictDPs  = sDps }

-- * ProofData

data DecomposeProof
  = DecomposeStaticProof
    { proofBound       :: DecomposeBound
    , proofSelectedTrs :: Trs
    , proofSelectedDPs :: Trs
    , proofSubProblems :: (Problem, Problem) }
  | DecomposeDynamicProof
    { proofBound    :: DecomposeBound
    , proofSubProof :: PartialProof }
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
  pretty proof@DecomposeDynamicProof{..}
    | progress proof = PP.vcat
        [ PP.text "We use the processor" PP.<+> PP.text (ppProcName pp) PP.<+> PP.text "to orient following rules striclty."
        , PP.empty
        , ppRules "DPs" (ppRemovableDPs pp)
        , ppRules "Trs" (ppRemovableTrs pp)
        , PP.empty
        , PP.text "The induced complexity on above rules (module renaming rules) is:"
            PP.<+> (PP.pretty . T.certificate . T.fromReturn $ ppResult pp) PP.<> PP.dot
        ]

    | isEmpty stricts =
        PP.text "We fail to orient any rules."
    | otherwise = PP.vcat
        [ PP.text "We fail to orient at least following rules strictly:"
        , PP.empty
        , ppRules "Strict Rules" stricts ]
    where
      pp = proofSubProof
      ppRules s rs = PP.text s PP.<$$> PP.indent 2 (PP.pretty rs)
      stricts = ppRemovableDPs pp `union` ppRemovableTrs pp

instance Xml.Xml DecomposeProof where
  toXml _ = Xml.text "decompose"

progress :: DecomposeProof -> Bool
progress DecomposeStaticProof{..} =
  case proofBound of
    Add -> not $ isEmpty (allComponents rProb) || isEmpty (allComponents sProb)
    _   -> not $ isTrivial rProb || isTrivial sProb
    where  (rProb, sProb) = proofSubProblems
progress DecomposeDynamicProof{..} =
  not (isEmpty . strictComponents $ ppInputProblem pp) &&
  not (isEmpty (ppRemovableDPs pp) && isEmpty (ppRemovableTrs pp))
  where pp = proofSubProof


-- * Decompose Static

data DecomposeStaticProcessor = DecomposeStaticProc ExpressionSelector DecomposeBound
  deriving Show

instance T.Processor DecomposeStaticProcessor where
  type ProofObject DecomposeStaticProcessor = ApplicationProof DecomposeProof
  type Problem DecomposeStaticProcessor = Problem
  type Forking DecomposeStaticProcessor = T.Pair
  solve p@(DecomposeStaticProc rs compfn) prob = return . T.resultToTree p prob $
    maybe decomposition (T.Fail . Inapplicable) maybeApplicable
    where
      decomposition
        | progress proof = T.Success (T.Pair (rProb,sProb)) (Applicable proof) undefined
        | otherwise      = T.Fail (Applicable proof)
      maybeApplicable = isApplicableRandS prob compfn <|> isApplicableRModuloS rProb sProb compfn
      (dps,trs) = rules $ BigAnd [ rsSelect rs prob, selectForcedRules prob compfn]
      (rProb, sProb) = mkProbs prob compfn dps trs
      proof = DecomposeStaticProof
        { proofBound       = compfn
        , proofSelectedTrs = trs
        , proofSelectedDPs = dps
        , proofSubProblems = (rProb, sProb) }

-- * Decompose Dynamic

data DecomposeDynamicProcessor = DecomposeDynamicProc ExpressionSelector DecomposeBound PartialStrategy
  deriving Show

instance T.Processor DecomposeDynamicProcessor where
  type ProofObject DecomposeDynamicProcessor = ApplicationProof DecomposeProof
  type Problem DecomposeDynamicProcessor = Problem
  type Forking DecomposeDynamicProcessor = T.Pair
  solve p@(DecomposeDynamicProc rs compfn st) prob = do
    app <- runApplicationT $ do
      test (isApplicableRandS prob compfn)
      let rs' = BigAnd [ rsSelect rs prob, selectForcedRules prob compfn ]
      pp <- lift $ evaluatePartial rs' st prob
      let
        (rProb, sProb) = mkProbs prob compfn (ppRemovableDPs pp) (ppRemovableTrs pp)
        proof = DecomposeDynamicProof
          { proofBound          = compfn
          , proofSubProof       = pp}
      test (isApplicableRModuloS rProb sProb compfn)
      return $ if not (progress proof)
        then T.resultToTree p prob $ T.Fail (Applicable proof)
        else T.Continue $ T.Progress (pn (Applicable proof)) certfn (T.Pair (T.fromReturn (ppResult pp), T.Open sProb))
    return $ case app of
      Inapplicable s -> T.resultToTree p prob $ T.Fail (Inapplicable s)
      Closed         -> T.resultToTree p prob $ T.Fail Closed
      Applicable pt  -> pt
    where
      test = maybe (return ()) (ApplicationT . return . Inapplicable)
      pn proof = T.ProofNode
        { T.processor = p
        , T.problem   = prob
        , T.proof     = proof }
      certfn (T.Pair (c1,c2)) = case compfn of
        Add          -> c1 `add` c2
        RelativeAdd  -> c1 `add` c2
        RelativeMul  -> c1 `mul` c2
        RelativeComp -> T.timeUBCert (T.timeUB c1 `T.compose` T.timeUB c2)


--- * Instances ------------------------------------------------------------------------------------------------------

decompose :: ExpressionSelector -> DecomposeBound -> PartialStrategy -> T.Strategy Problem
decompose rs compfn = T.Proc . DecomposeDynamicProc rs compfn

decomposeStatic :: ExpressionSelector -> DecomposeBound -> T.Strategy Problem
decomposeStatic rs = T.Proc . DecomposeStaticProc rs

decomposeStaticDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional ExpressionSelector
   , T.Argument 'T.Optional DecomposeBound ]
   T.:-> T.Strategy Problem )
decomposeStaticDeclaration = T.declare "decomposeStatic" description (selectorArg', boundArg') decomposeStatic
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

