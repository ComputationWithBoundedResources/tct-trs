-- | This module provides the /Decompose/ processor.
{-# LANGUAGE RecordWildCards #-}
module Tct.Trs.Method.Decompose
  ( decomposeDeclaration
  , decompose
  , decompose'

  -- * processor interface
  , Decompose
  , DecomposeBound (..)
  , decomposeProc
  , decomposeProc'
  , combineBy
  , decomposeBy
  ) where


import           Control.Applicative
import           Data.Typeable

import qualified Data.Rewriting.Rule         as R (Rule)
import qualified Data.Rewriting.Term         as R (isVariantOf)

import qualified Tct.Core.Common.Parser      as P
import qualified Tct.Core.Common.Pretty      as PP
import           Tct.Core.Common.SemiRing
import qualified Tct.Core.Common.Xml         as Xml
import qualified Tct.Core.Data               as T

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem        as Prob
import qualified Tct.Trs.Data.Rewriting      as R
import           Tct.Trs.Data.RuleSelector
import qualified Tct.Trs.Data.Trs            as Trs


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

mkProbs :: (Show f, Show v, Ord f, Ord v) => Problem f v -> DecomposeBound -> Trs f v -> Trs f v -> (Problem f v, Problem f v)
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

    sProb = Prob.sanitise $ 
      if isAdditive compfn 
        then prob
          { Prob.strictTrs  = sTrs
          , Prob.strictDPs  = sDps
          , Prob.weakTrs    = rTrs `Trs.union` Prob.weakTrs prob
          , Prob.weakDPs    = rDps `Trs.union` Prob.weakDPs prob }
        else prob 
          { Prob.strictTrs  = sTrs
          , Prob.strictDPs  = sDps }

    isAdditive c = c == Add || c == RelativeAdd



--- * processor ------------------------------------------------------------------------------------------------------

data Decompose = Decompose 
  { onSelection :: ExpressionSelector F V
  , withBound   :: DecomposeBound }
  deriving Show

data DecomposeProof
  = DecomposeProof
    { bound_       :: DecomposeBound
    , selectedTrs_ :: Trs F V
    , selectedDPs_ :: Trs F V
    , rProb_       :: TrsProblem
    , sProb_       :: TrsProblem }
  | DecomposeFail
    deriving Show

progress :: DecomposeProof -> Bool
progress DecomposeProof{..} =
  case bound_ of
    Add -> not $ Trs.null (Prob.allComponents rProb_) || Trs.null (Prob.allComponents sProb_)
    _   -> not $ Prob.isTrivial rProb_ || Prob.isTrivial sProb_
progress DecomposeFail = False  

instance T.Processor Decompose where
  type ProofObject Decompose = ApplicationProof DecomposeProof
  type I Decompose           = TrsProblem
  type O Decompose           = TrsProblem
  type Forking Decompose     = T.Pair

  solve p@Decompose{..} prob = return . T.resultToTree p prob $
    maybe decomposition (T.Fail . Inapplicable) maybeApplicable
    where
      decomposition
        | progress proof = T.Success (T.Pair (rProb,sProb)) (Applicable proof) (cert (fromBound withBound))
        | otherwise      = T.Fail (Applicable DecomposeFail)
      maybeApplicable = isApplicableRandS prob withBound <|> isApplicableRModuloS rProb sProb withBound

      (dps,trs) = rules $ BigAnd [ rsSelect onSelection prob, selectForcedRules prob withBound]
      (rProb, sProb) = mkProbs prob withBound dps trs
      proof = DecomposeProof
        { bound_       = withBound
        , selectedTrs_ = trs
        , selectedDPs_ = dps
        , rProb_       = rProb
        , sProb_       = sProb }
      fromBound Add          = add
      fromBound RelativeAdd  = add
      fromBound RelativeMul  = mul
      fromBound RelativeComp = T.compose
      cert f (T.Pair (c1,c2)) = T.timeUBCert (T.timeUB c1 `f` T.timeUB c2)


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty DecomposeProof where
  pretty DecomposeProof{..} = PP.vcat
    [ PP.text "We analyse the complexity of following sub-problems (R) and (S)."
    , case bound_ of
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
    , PP.indent 2 $ PP.pretty (rProb_)
    , PP.empty
    , PP.text "Problem (S)"
    , PP.indent 2 $ PP.pretty (sProb_) ]
  pretty DecomposeFail = PP.text "Decomposition failed."

instance Xml.Xml DecomposeProof where
  toXml _ = Xml.elt "decompose" []


--- * instances ------------------------------------------------------------------------------------------------------

decomposeProcessor :: ExpressionSelector F V -> DecomposeBound -> Decompose
decomposeProcessor rs bd = Decompose { onSelection=rs, withBound=bd }

desc :: [String]
desc =
  [ "This transformation implements techniques for splitting the complexity problem"
  , "into two complexity problems (R) and (S) so that the complexity of the input problem"
  , "can be estimated by the complexity of the transformed problem."
  , "The processor closely follows the ideas presented in"
  , "/Complexity Bounds From Relative Termination Proofs/"
  , "(<http://www.imn.htwk-leipzig.de/~waldmann/talk/06/rpt/rel/main.pdf>)" ]

bndArg :: T.Argument 'T.Optional DecomposeBound
bndArg = boundArg `T.optional` RelativeAdd

selArg :: T.Argument 'T.Optional (ExpressionSelector F V)
selArg = selectorArg `T.optional` selAnyOf selStricts

decomposeProcDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional (ExpressionSelector F V)
   , T.Argument 'T.Optional DecomposeBound ]
   T.:-> Decompose )
decomposeProcDeclaration = T.declare "decompose" desc (selArg, bndArg) decomposeProcessor

decomposeProc :: ExpressionSelector F V -> DecomposeBound -> (Decompose -> Decompose) -> TrsStrategy
decomposeProc sel b f = T.Proc . f $ T.declFun decomposeProcDeclaration sel b

decomposeProc' :: (Decompose -> Decompose) -> TrsStrategy
decomposeProc' f = T.Proc . f $ T.deflFun decomposeProcDeclaration

decomposeDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional (ExpressionSelector F V)
   , T.Argument 'T.Optional DecomposeBound ] 
   T.:-> TrsStrategy)
decomposeDeclaration = T.declare "decompose" desc (selArg, bndArg) (\x y -> T.Proc (decomposeProcessor x y ))

decomposeBy :: ExpressionSelector F V -> Decompose -> Decompose
decomposeBy sel p = p{ onSelection=sel }

combineBy :: DecomposeBound -> Decompose -> Decompose
combineBy bnd p = p{ withBound=bnd }


decompose :: ExpressionSelector F V -> DecomposeBound -> TrsStrategy
decompose = T.declFun decomposeDeclaration

decompose' :: TrsStrategy
decompose' = T.deflFun decomposeDeclaration


boundArg :: T.Argument 'T.Required DecomposeBound
boundArg = T.arg { T.argName = "allow", T.argDomain = "<bound>"} `T.withHelp` help
  where
    help =
      [ "This argument type determines"
      , "how the complexity certificate should be obtained from subproblems (R) and (S)."
      , "Consequently, this argument also determines the shape of (S)."
      , "<bound> is one of " ++ show [Add, RelativeAdd, RelativeMul, RelativeComp] ]

instance T.SParsable i i DecomposeBound where
  parseS = P.choice
    [ P.symbol (show Add) >> return Add
    , P.symbol (show RelativeAdd) >> return RelativeAdd
    , P.symbol (show RelativeMul) >> return RelativeMul
    , P.symbol (show RelativeComp) >> return RelativeComp ]

