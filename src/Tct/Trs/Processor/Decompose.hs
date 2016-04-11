-- | This module provides the /Decompose/ processor.
--
-- [1] http://www.imn.htwk-leipzig.de/~waldmann/talk/06/rpt/rel/main.pdf>
-- [2] A.~Stump, N.~Hirokawa, A Rewriting Approach to Automata-Based Parsing
{-# LANGUAGE RecordWildCards #-}
module Tct.Trs.Processor.Decompose
  ( DecomposeBound(..)

  , decomposeDeclaration
  , decompose
  , decompose'

  , decomposeCPDeclaration
  , decomposeCP
  , decomposeCP'
  ) where


import           Control.Applicative
import           Control.Monad.Trans           (lift)

import qualified Data.Rewriting.Rule           as R (Rule)
import qualified Data.Rewriting.Term           as R (isVariantOf)

import qualified Tct.Core.Common.Pretty        as PP
import           Tct.Core.Common.SemiRing
import qualified Tct.Core.Common.Xml           as Xml
import qualified Tct.Core.Data                 as T
import           Tct.Core.Processor.Assumption (assumeWith)

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import           Tct.Trs.Data.ComplexityPair   as CP
import qualified Tct.Trs.Data.DependencyGraph  as DG
import qualified Tct.Trs.Data.Problem          as Prob
import qualified Tct.Trs.Data.Rewriting        as R
import           Tct.Trs.Data.RuleSelector
import qualified Tct.Trs.Data.Rules            as RS

import qualified Tct.Trs.Processor.ComplexityPair as CP


data DecomposeBound
  = Add
  | RelativeAdd
  | RelativeMul
  | RelativeComp
  deriving (Eq, Show, Bounded, Enum)


-- checks condition on R and S
isApplicableRandS :: (Ord f, Ord v) => Problem f v -> DecomposeBound -> Maybe String
isApplicableRandS prob compfn = case compfn of
  Add          -> Prob.isDCProblem' prob <|> RS.isLinear' trs <|> RS.isNonErasing' trs
  RelativeAdd  -> Nothing
  RelativeMul  -> Prob.isDCProblem' prob <|> RS.isNonSizeIncreasing' trs
  RelativeComp -> Prob.isDCProblem' prob <|> RS.isNonDuplicating' trs
  where trs = Prob.allComponents prob

-- for Add and RelativeComp rules in rProb have to be non-size increasing
selectForcedRules :: (Ord f, Ord v) => Problem f v -> DecomposeBound -> SelectorExpression f v
selectForcedRules prob compfn = BigAnd $ [ SelectDP r | r <- forcedDps ] ++ [ SelectTrs r | r <- forcedTrs ]
  where
    (forcedDps, forcedTrs) = case compfn of
      RelativeComp -> (fsi Prob.dpComponents, fsi Prob.trsComponents)
      Add          -> (fsi Prob.dpComponents, fsi Prob.trsComponents)
      _            -> ([],[])
      where fsi f = [ rule | rule <- RS.toList (f prob), not (R.isNonSizeIncreasing rule) ]

-- for Add rProb and sProb commute
isApplicableRModuloS :: (Ord f, Ord v) => Problem f v -> Problem f v -> DecomposeBound -> Maybe String
isApplicableRModuloS rProb sProb Add = Prob.note (not $ isCommutative rRules sRules) "commutative criterion not fulfilled"
  where (rRules, sRules)   = (RS.toList $ Prob.allComponents rProb, RS.toList $ Prob.allComponents sProb)
isApplicableRModuloS _ _ _ = Nothing

isCommutative :: (Ord f, Ord v) => [R.Rule f v] -> [R.Rule f v] -> Bool
isCommutative rRules' sRules' = isCommutative' 5 cps
  where
    rews             = R.rewrites (rRules' ++ sRules')
    reducts l        = iterate rews $ rews (R.rewrite rRules' l)
    reductOf r       = any (any (R.isVariantOf r))
    cps              = R.toPairs $ R.forwardPairs rRules' sRules'
    isCommutative' n = all (\(l,r) -> r `reductOf` take n (reducts l))

mkProbs :: (Fun f, Show f, Show v, Ord f, Ord v) => Problem f v -> DecomposeBound -> Rules f v -> Rules f v -> (Problem f v, Problem f v)
mkProbs prob compfn dps trs = (rProb, sProb)
  where
    rDps = dps `RS.intersect` Prob.strictDPs prob
    rTrs = trs `RS.intersect` Prob.strictTrs prob
    sDps = Prob.strictDPs prob `RS.difference` rDps
    sTrs = Prob.strictTrs prob `RS.difference` rTrs

    rProb = prob
      { Prob.strictDPs = rDps
      , Prob.strictTrs = rTrs
      , Prob.weakDPs   = Prob.weakDPs prob `RS.union` sDps
      , Prob.weakTrs   = Prob.weakTrs prob `RS.union` sTrs
      , Prob.dpGraph   = DG.setWeak sDps (Prob.dpGraph prob) }

    sProb = Prob.sanitiseDPGraph $
      if isAdditive compfn
        then prob
          { Prob.strictDPs  = sDps
          , Prob.strictTrs  = sTrs
          , Prob.weakDPs    = Prob.weakDPs prob `RS.union` rDps
          , Prob.weakTrs    = Prob.weakTrs prob `RS.union` rTrs }
        else prob
          { Prob.strictTrs  = sTrs
          , Prob.strictDPs  = sDps }

    isAdditive c = c == Add || c == RelativeAdd


data DecomposeProof
  = DecomposeProof
    { bound_       :: DecomposeBound
    , selectedTrs_ :: Rules F V
    , selectedDPs_ :: Rules F V
    , rProb_       :: Trs
    , sProb_       :: Trs }
  | DecomposeCPProof
    { bound_   :: DecomposeBound
    , sProb_   :: Trs
    , cp_      :: ComplexityPair
    , cpproof_ :: ComplexityPairProof
    , cpcert_  :: T.Certificate }
  | DecomposeFail
  deriving Show

progress :: DecomposeProof -> Bool
progress DecomposeProof{..} =
  case bound_ of
    Add -> not $ RS.null (Prob.allComponents rProb_) || RS.null (Prob.allComponents sProb_)
    _   -> not $ Prob.isTrivial rProb_ || Prob.isTrivial sProb_
progress DecomposeCPProof{..} =
  not $ RS.null (CP.removableDPs cpproof_) && RS.null (CP.removableTrs cpproof_)
progress DecomposeFail = False

certfn :: DecomposeBound -> T.Pair T.Certificate -> T.Certificate
certfn bnd (T.Pair (rCert,sCert)) = case bnd of
  Add          -> T.timeUBCert $ rUb `add` sUb
  RelativeAdd  -> T.timeUBCert $ rUb `add` sUb
  RelativeMul  -> T.timeUBCert $ rUb `mul` sUb
  RelativeComp -> T.timeUBCert $ rUb `mul` (sUb `T.compose` (T.Poly (Just 1) `add` rUb))
  where (rUb, sUb) = (T.timeUB rCert, T.timeUB sCert)


--- * decompose static -----------------------------------------------------------------------------------------------

data Decompose = Decompose
  { onSelection :: ExpressionSelector F V
  , withBound   :: DecomposeBound }
  deriving Show

instance T.Processor Decompose where
  type ProofObject Decompose = ApplicationProof DecomposeProof
  type In  Decompose         = Trs
  type Out Decompose         = Trs
  type Forking Decompose     = T.Pair

  execute Decompose{..} prob =
    maybe decomposition (\s -> T.abortWith (Inapplicable s :: ApplicationProof DecomposeProof)) maybeApplicable
    where
      decomposition
        | progress proof = T.succeedWith (Applicable proof) (certfn withBound) (T.Pair (rProb,sProb))
        | otherwise      = T.abortWith (Applicable DecomposeFail)
      maybeApplicable = isApplicableRandS prob withBound <|> isApplicableRModuloS rProb sProb withBound

      (dps,trs) = rules $ BigAnd [ rsSelect onSelection prob, selectForcedRules prob withBound]
      (rProb, sProb) = mkProbs prob withBound dps trs
      proof = DecomposeProof
        { bound_       = withBound
        , selectedTrs_ = trs
        , selectedDPs_ = dps
        , rProb_       = rProb
        , sProb_       = sProb }


--- * decompose dynamic ----------------------------------------------------------------------------------------------

data DecomposeCP = DecomposeCP
  { onSelectionCP_ :: ExpressionSelector F V
  , withBoundCP_   :: DecomposeBound
  , withCP_        :: ComplexityPair }
  deriving Show

instance T.Processor DecomposeCP where
  type ProofObject DecomposeCP = ApplicationProof DecomposeProof
  type In  DecomposeCP         = Trs
  type Out DecomposeCP         = Trs
  type Forking DecomposeCP     = T.Pair

  execute DecomposeCP{..} prob = do
    app <- runApplicationT $ do
      test (isApplicableRandS prob withBoundCP_)
      let
        rs = RuleSelector
          { rsName   = "first alternative for decompose on " ++ rsName (onSelectionCP_)
          , rsSelect = \pr -> (BigAnd [rsSelect (selAnyOf selStricts) pr, rsSelect onSelectionCP_ pr, selectForcedRules pr withBoundCP_]) }
      ComplexityPair cp <- return withCP_

      cpproof <- lift $ CP.solveComplexityPair cp rs prob
      case cpproof of
        Left s -> return $ T.NoProgress (T.SomeReason s)
        Right cpp -> do
          let
            (rProb, sProb) = mkProbs prob withBoundCP_ (CP.removableDPs cpp) (CP.removableTrs cpp)
            rProof = assumeWith (T.timeUBCert zero) (CP.result cpp)
            proof = DecomposeCPProof
              { bound_       = withBoundCP_
              , sProb_       = sProb
              , cp_          = withCP_
              , cpproof_     = cpp
              , cpcert_      = T.certificate rProof }
          test (isApplicableRModuloS rProb sProb withBoundCP_)
          if not (progress proof)
            then return $ T.NoProgress (T.SomeReason $ Applicable proof)
            else return $ T.Progress (Applicable proof) (certfn withBoundCP_) (T.Pair (rProof, T.Open sProb))

    case app of
      Applicable ret -> return ret
      Inapplicable s -> T.abortWith (Inapplicable s :: ApplicationProof DecomposeProof)
      Closed         -> T.abortWith (Inapplicable "already closed" :: ApplicationProof DecomposeProof)
    where
      test = maybe (return ()) (ApplicationT . return . Inapplicable)


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty DecomposeProof where
  pretty proof = case proof of
    DecomposeProof{..} -> PP.vcat
      [ PP.text "We analyse the complexity of following sub-problems (R) and (S)."
      , ppbnd bound_
      , PP.empty
      , PP.text "Problem (R)"
      , PP.indent 2 $ PP.pretty (rProb_)
      , PP.empty
      , PP.text "Problem (S)"
      , PP.indent 2 $ PP.pretty (sProb_) ]
    DecomposeCPProof{..} -> PP.vcat
      [ PP.text $ "We first use the processor " ++ show cp_ ++ " to orient following rules strictly:"
      , PP.indent 2 . PP.pretty $ CP.removableDPs cpproof_
      , PP.indent 2 . PP.pretty $ CP.removableTrs cpproof_
      , PP.text ("The Processor induces the complexity certificate ") PP.<> PP.pretty cpcert_
      , PP.empty
      , ppbnd bound_
      , PP.text "Problem (S)"
      , PP.indent 2 $ PP.pretty (sProb_) ]
    DecomposeFail -> PP.text "Decomposition failed."
    where
      ppbnd bnd = case bnd of
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

instance Xml.Xml DecomposeProof where
  toXml _ = Xml.elt "decompose" []


--- * instances ------------------------------------------------------------------------------------------------------

boundArg :: T.Argument 'T.Required DecomposeBound
boundArg = T.flag "allow"
  [ "This argument type determines"
  , "how the complexity certificate should be obtained from subproblems (R) and (S)."
  , "Consequently, this argument also determines the shape of (S)." ]

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

decomposeProcessor :: ExpressionSelector F V -> DecomposeBound -> Decompose
decomposeProcessor rs bd = Decompose { onSelection=rs, withBound=bd }

decomposeDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional (ExpressionSelector F V)
   , T.Argument 'T.Optional DecomposeBound ]
   T.:-> TrsStrategy)
decomposeDeclaration = T.declare "decompose" desc (selArg, bndArg) (\x y -> T.Apply (decomposeProcessor x y ))

decompose' :: ExpressionSelector F V -> DecomposeBound -> TrsStrategy
decompose' = T.declFun decomposeDeclaration

decompose :: TrsStrategy
decompose = T.deflFun decomposeDeclaration

decomposeCPProcessor :: ExpressionSelector F V -> DecomposeBound -> ComplexityPair -> DecomposeCP
decomposeCPProcessor rs bd cp = DecomposeCP { onSelectionCP_ = rs, withBoundCP_ = bd, withCP_ = cp }

decomposeCPDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional (ExpressionSelector F V)
   , T.Argument 'T.Optional DecomposeBound
   , T.Argument 'T.Required ComplexityPair ]
   T.:-> TrsStrategy)
decomposeCPDeclaration = T.declare "decomposeCP" desc (selArg, bndArg, CP.complexityPairArg) (\x y z -> T.Apply (decomposeCPProcessor x y z))

decomposeCP :: ComplexityPair -> TrsStrategy
decomposeCP = T.deflFun decomposeCPDeclaration

decomposeCP' :: ExpressionSelector F V -> DecomposeBound -> ComplexityPair -> TrsStrategy
decomposeCP' = T.declFun decomposeCPDeclaration

