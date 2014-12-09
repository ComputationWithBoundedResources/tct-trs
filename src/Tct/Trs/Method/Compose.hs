module Tct.Trs.Method.Compose where

import qualified Data.Rewriting.Term as R (isVariantOf)

import qualified Tct.Core.Data as T
import qualified Tct.Core.Common.Pretty as PP

import Tct.Common.ProofCombinators

import Control.Applicative
import Tct.Trs.Data.Trs
import Tct.Trs.Data.RuleSelector
import Tct.Trs.Data.Problem
import qualified Tct.Trs.Data.Rewriting as R


data DecomposeBound
  = Add
  | RelativeAdd
  | RelativeMul
  | RelativeComp
  deriving (Eq,Show)

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
isApplicableRModuloS rProb sProb Add = tCommutative
  where
    tCommutative       = note (isCommutative 10 cps)  " the commutation criterion is not fulfilled"

    (rRules, sRules)   = (allComponents rProb, allComponents sProb)
    (rRules', sRules') = (ruleList rRules, ruleList sRules)
    rews               = R.rewrites (rRules' ++ sRules')
    reducts l          = iterate rews $ rews (R.rewrite rRules' l)
    reductOf r         = any (any (R.isVariantOf r))
    cps                = R.toPairs $ R.forwardPairs rRules' sRules'
    isCommutative n    = all (\(l,r) -> r `reductOf` take n (reducts l))
isApplicableRModuloS _ _ _ = Nothing

data DecomposeStaticProcessor = DecomposeStaticProc ExpressionSelector DecomposeBound
  deriving Show

data DecomposeStaticProof = DecomposeStaticProof 
  { proofBound       :: DecomposeBound
  , proofSelectedTrs :: Trs
  , proofSelectedDPs :: Trs
  , proofSubProblems :: (Problem, Problem)}
  deriving Show

instance PP.Pretty DecomposeStaticProof where
  pretty _ = PP.empty


instance T.Processor DecomposeStaticProcessor where
  type ProofObject DecomposeStaticProcessor = ApplicationProof DecomposeStaticProof
  type Problem DecomposeStaticProcessor = Problem
  type Forking DecomposeStaticProcessor = T.Pair
  solve p@(DecomposeStaticProc rs compfn) prob = return . T.resultToTree p prob $ 
    maybe decomposeStatic (T.Fail . Inapplicable) maybeApplicable
    where
      decomposeStatic =
        if progress proof
          then T.Success (T.Pair (rProb,sProb)) (Applicable proof) undefined
          else T.Fail (Applicable proof)
      maybeApplicable = isApplicableRandS prob compfn <|> isApplicableRModuloS rProb sProb compfn
      (dps,trs) = rules $ BigAnd [ rsSelect rs prob, selectForcedRules prob compfn]
      (rProb, sProb) = mkprob prob compfn dps trs
      proof = DecomposeStaticProof
        { proofBound       = compfn
        , proofSelectedTrs = trs
        , proofSelectedDPs = dps
        , proofSubProblems = (rProb, sProb) }

progress :: DecomposeStaticProof -> Bool
progress proof =
  case proofBound proof of
    Add -> not (isEmpty (allComponents rProb)) && not (isEmpty (allComponents sProb))
    _   -> not (isTrivial rProb) && not (isTrivial sProb)
    where  (rProb, sProb) = proofSubProblems proof

mkprob :: Problem -> DecomposeBound -> Trs -> Trs -> (Problem, Problem)
mkprob prob compfn dps trs = (rProb, sProb)
  where 
    rDps = dps `intersect` strictDPs prob
    rTrs = trs `intersect` strictTrs prob
    sDps = strictDPs prob `difference` rDps
    sTrs = strictTrs prob `difference` rTrs
        
    rProb = prob 
      { strictDPs = rDps
      , strictTrs = rTrs
      , weakTrs   = sTrs `union` weakTrs prob
      , weakDPs   = sDps `union` weakDPs prob }
            
    sProb = case compfn of
      Add -> prob 
        { strictTrs  = sTrs
        , strictDPs  = sDps
        , weakTrs    = rTrs `union` weakTrs prob
        , weakDPs    = rDps `union` weakDPs prob }
      _ -> prob 
        { strictTrs  = sTrs
        , strictDPs  = sDps }

