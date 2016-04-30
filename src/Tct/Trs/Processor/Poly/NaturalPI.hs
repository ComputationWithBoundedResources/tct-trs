{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Trs.Processor.Poly.NaturalPI
  (
  -- * Declaration
    polyDeclaration
  , poly
  , poly'
  , Shape (..)
  , Restrict (..)
  , UsableArgs (..)
  , UsableRules (..)

  -- * Complexity Pair
  , polyCPDeclaration
  , polyCP
  , polyCP'

  ) where


import qualified Data.List                           as L
import qualified Data.Map.Strict                     as M
import           Data.Maybe                          (fromMaybe)
import           Data.Monoid                         ((<>))
import qualified Data.Set                            as S

import qualified Data.Rewriting.Rule                 as R (Rule (..))
import qualified Data.Rewriting.Term                 as R

import           Tct.Core.Common.Error               (throwError)
import qualified Tct.Core.Common.Pretty              as PP
import qualified Tct.Core.Common.Xml                 as Xml
import qualified Tct.Core.Data                       as T
import           Tct.Core.Parse                      ()

import qualified Tct.Common.Polynomial               as P
import           Tct.Common.PolynomialInterpretation (Shape)
import qualified Tct.Common.PolynomialInterpretation as PI
import           Tct.Common.ProofCombinators
import           Tct.Common.Ring
import           Tct.Common.SMT                      ((.=>), (.>), (.>=))
import qualified Tct.Common.SMT                      as SMT

import           Tct.Trs.Data
import           Tct.Trs.Data.Arguments              (UsableArgs (..), UsableRules (..), Restrict (..))
import qualified Tct.Trs.Data.Arguments              as Arg
import qualified Tct.Trs.Data.ComplexityPair         as CP
import qualified Tct.Trs.Data.Problem                as Prob
import qualified Tct.Trs.Data.ProblemKind            as Prob
import qualified Tct.Trs.Data.RuleSelector           as RS
import qualified Tct.Trs.Data.Signature              as Sig
import qualified Tct.Trs.Data.Rules as RS
import qualified Tct.Trs.Encoding.Interpretation     as I
import qualified Tct.Trs.Encoding.UsableRules        as UREnc



data NaturalPI = NaturalPI
  { shape    :: PI.Shape
  , restrict :: Arg.Restrict -- TODO: MS: combine with Shape
  , uargs    :: Arg.UsableArgs
  , urules   :: Arg.UsableRules
  , selector :: Maybe (ExpressionSelector F V)
  } deriving Show

type Kind           = PI.Kind F

data PolyOrder c = PolyOrder
  { kind_ :: Kind
  , pint_ :: I.InterpretationProof (P.Polynomial c PI.SomeIndeterminate) (P.Polynomial c V)
  } deriving Show

type NaturalPIProof = OrientationProof (PolyOrder Int)

instance T.Processor NaturalPI where
  type ProofObject NaturalPI = ApplicationProof NaturalPIProof
  type In  NaturalPI         = Trs
  type Out NaturalPI         = Trs
  type Forking NaturalPI     = T.Optional T.Id

  execute p prob
    | Prob.isTrivial prob = T.abortWith (Closed :: ApplicationProof NaturalPIProof)
    | otherwise           = entscheide p prob

certification :: PolyOrder Int -> T.Optional T.Id T.Certificate -> T.Certificate
certification order cert = case cert of
  T.Null         -> T.timeUBCert bound
  T.Opt (T.Id c) -> T.updateTimeUBCert c (`add` bound)
  where bound = PI.bound (kind_ order) (PI.PolyInter . I.interpretations . I.inter_ $ pint_ order)

instance I.AbstractInterpretation NaturalPI where
  type (A NaturalPI) = P.PView (PI.CoefficientVar F) PI.SomeIndeterminate
  type (B NaturalPI) = P.Polynomial (SMT.IExpr Int) PI.SomeIndeterminate
  type (C NaturalPI) = P.Polynomial (SMT.IExpr Int) V

  encode _ = P.fromViewWithM enc where
    enc c
      | PI.restrict c = SMT.snvarM'
      | otherwise     = SMT.nvarM'

  setMonotone _ fpoly is  = SMT.bigAnd $ k `fmap` is
    where k i = P.getCoefficient fpoly [(toEnum i,1)] .> zero

  setInFilter _ fpoly inFilter = afpoly (P.toView fpoly)
    where
      afpoly po = SMT.bigAnd [ c .> zero .=> (afmono mo) | (c, mo) <- po ]
      afmono mo = SMT.bigAnd [ inFilter (fromEnum vi) | (vi,_) <- mo ]

  interpret _ = interpretf

  addConstant _ f v = f `add`  P.constant v
  gte _ p1 p2       = SMT.bigAnd [ c .>= SMT.zero | c <- P.coefficients $ p1 `sub` p2 ]

interpretf :: (Show c, Show fun, SemiRing c, Eq c, Ord fun, Ord var) => I.Interpretation fun (PI.SomePolynomial c) -> R.Term fun var -> P.Polynomial c var
interpretf ebsi = I.interpretTerm interpretFun interpretVar
  where
    interpretFun f = P.substituteVariables (I.interpretations ebsi `k` f) . M.fromList . zip PI.indeterminates
      where k m g = error ("NaturalPI.interpretf: " ++ show g) `fromMaybe` M.lookup g m
    interpretVar v = P.variable v



entscheide :: NaturalPI -> Trs -> T.TctM (T.Return NaturalPI)
entscheide p prob = do
  res :: SMT.Result (I.InterpretationProof () (), I.Interpretation F (PI.SomePolynomial Int), Maybe (UREnc.UsableSymbols F))
    <- SMT.smtSolveSt (SMT.smtSolveTctM prob) $ do
      encoding <- I.orient p prob absi shift (uargs p == Arg.UArgs) (urules p == Arg.URules)
      return $ SMT.decode encoding
  case res of
    SMT.Sat a -> let order = mkOrder a in
      T.succeedWith
        (Applicable $ Order order)
        (certification order)
        (I.newProblem prob (pint_ order))

    SMT.Error s -> throwError (userError s)
    _           -> T.abortWith "Incompatible"

  where

    sig   = Prob.signature prob
    kind  = case Prob.startTerms prob of
      Prob.AllTerms{}                       -> PI.Unrestricted (shape p)
      Prob.BasicTerms{Prob.constructors=cs} -> PI.ConstructorBased (shape p) $ if Arg.useRestrict (restrict p) then Sig.constructors sig else cs

    absi  = I.Interpretation $ M.mapWithKey (curry $ PI.mkInterpretation kind) (Sig.toMap sig)
    shift = maybe I.All I.Shift (selector p)

    mkOrder (proof, inter, ufuns) = PolyOrder
      { kind_ = kind
      , pint_ = proof
        { I.inter_     = inter
        , I.ufuns_     = UREnc.runUsableSymbols `fmap` ufuns
        , I.strictDPs_ = sDPs
        , I.strictTrs_ = sTrs
        , I.weakDPs_   = wDPs
        , I.weakTrs_   = wTrs }}
      where

          (sDPs,wDPs) = L.partition isStrict (rs $ Prob.dpComponents prob)
          (sTrs,wTrs) = L.partition isStrict (rs $ Prob.trsComponents prob)
          isStrict (r,(lpoly,rpoly)) = r `RS.member` Prob.strictComponents prob && P.constantValue (lpoly `sub` rpoly) > 0

          rs trs =
            [ (r, (interpretf inter lhs, interpretf inter rhs))
            | r@(R.Rule lhs rhs) <- RS.toList trs
            , isUsable ufuns r]

          isUsable Nothing _ = True
          isUsable (Just fs) (R.Rule lhs _) = either (const False) (`S.member` UREnc.runUsableSymbols fs) (R.root lhs)


--- * instances ------------------------------------------------------------------------------------------------------

description :: [String]
description =  [ "This processor tries to find a polynomial interpretation and shifts strict oriented rules to the weak components." ]

selectorArg :: (Ord f, Ord v) => T.Argument 'T.Required (ExpressionSelector f v)
selectorArg = RS.selectorArg
  `T.withName` "shift"
  `T.withHelp` [ "This argument specifies which rules to orient strictly and shift to the weak components." ]


--- ** strategy ------------------------------------------------------------------------------------------------------

polyStrategy :: PI.Shape -> Arg.Restrict -> Arg.UsableArgs -> Arg.UsableRules -> Maybe (ExpressionSelector F V) ->TrsStrategy
polyStrategy sh li ua ur sl = T.Apply $ NaturalPI
  { shape    = sh
  , restrict = li
  , uargs    = ua
  , urules   = ur
  , selector = sl }

polyDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional PI.Shape
   , T.Argument 'T.Optional Arg.Restrict
   , T.Argument 'T.Optional Arg.UsableArgs
   , T.Argument 'T.Optional Arg.UsableRules
   , T.Argument 'T.Optional (Maybe (ExpressionSelector F V)) ]
   T.:-> TrsStrategy )
polyDeclaration = T.declare "poly" description args polyStrategy where
  args =
    ( PI.shapeArg `T.optional` PI.Linear
    , Arg.restrict `T.optional` Arg.Restrict
    , Arg.usableArgs `T.optional` Arg.UArgs
    , Arg.usableRules `T.optional` Arg.URules
    , T.some selectorArg `T.optional` Just (RS.selAnyOf RS.selStricts) )

poly :: TrsStrategy
poly = T.deflFun polyDeclaration

poly' :: PI.Shape -> Arg.Restrict -> Arg.UsableArgs -> Arg.UsableRules -> Maybe (ExpressionSelector F V) -> TrsStrategy
poly' = T.declFun polyDeclaration


--- ** complexity pair -----------------------------------------------------------------------------------------------

instance IsComplexityPair NaturalPI where
  solveComplexityPair p sel prob = do
  pt <- T.evaluate (T.Apply p{selector=Just sel}) (T.Open prob)
  return $ if T.isFailing pt
    then Left $ "application of cp failed"
    else case T.open pt of
      [nprob] -> Right $ CP.ComplexityPairProof
        { CP.result = pt
        , CP.removableDPs = Prob.strictDPs prob `RS.difference` Prob.strictDPs nprob
        , CP.removableTrs = Prob.strictTrs prob `RS.difference` Prob.strictTrs nprob }
      _ -> error "Tct.RS.Method.Poly.NaturalPI.solveComplexityPair: the impossible happened"

polyProcessorCP :: PI.Shape -> Arg.Restrict -> Arg.UsableArgs -> Arg.UsableRules -> ComplexityPair
polyProcessorCP sh li ua ur = CP.toComplexityPair $ NaturalPI
  { shape    = sh
  , restrict = li
  , uargs    = ua
  , urules   = ur
  , selector = Nothing }

polyCPDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional PI.Shape
   , T.Argument 'T.Optional Arg.Restrict
   , T.Argument 'T.Optional Arg.UsableArgs
   , T.Argument 'T.Optional Arg.UsableRules ]
   T.:-> ComplexityPair )
polyCPDeclaration = T.declare "polyCP" description argsCP polyProcessorCP
  where
    argsCP =
      ( PI.shapeArg `T.optional` PI.Linear
      , Arg.restrict `T.optional` Arg.Restrict
      , Arg.usableArgs `T.optional` Arg.UArgs
      , Arg.usableRules `T.optional` Arg.URules )

polyCP :: ComplexityPair
polyCP = T.deflFun polyCPDeclaration

polyCP' :: PI.Shape -> Arg.Restrict -> Arg.UsableArgs -> Arg.UsableRules -> ComplexityPair
polyCP' = T.declFun polyCPDeclaration


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty (PolyOrder Int) where
  pretty order = PP.vcat
    [ PP.text "We apply a polynomial interpretation of kind " <> PP.pretty (kind_ order) <> PP.char ':'
    , PP.pretty $ PP.pretty (pint_ order) ]

instance Xml.Xml (PolyOrder Int) where
  toXml order = I.xmlProof (pint_ order) xtype where
    xtype   = Xml.elt "type" [Xml.elt "polynomial" [xdomain, xdegree]]
    xdegree = Xml.elt "degree" [Xml.int $ PI.degree . PI.PolyInter . I.interpretations . I.inter_ $ pint_ order]
    xdomain = Xml.elt "domain" [Xml.elt "naturals" []]
  toCeTA = Xml.toXml

