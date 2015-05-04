{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Trs.Method.Poly.NaturalPI
  (
  -- * Declaration
    polyDeclaration
  , poly
  , poly'
  , Shape (..)
  , UsableArgs (..)
  , UsableRules (..)
  , Greedy (..)

  -- * Processor Interface
  , polyProcDeclaration
  , polyProc

  -- * Complexity Pair
  -- , polyCPDeclaration
  ) where


import           Control.Monad.Trans                 (liftIO)
import qualified Data.List                           as L
import qualified Data.Map.Strict                     as M
import           Data.Monoid                         ((<>))
import qualified Data.Set                            as S
import qualified Data.Traversable                    as F

import qualified Data.Rewriting.Rule                 as R (Rule (..))
import qualified Data.Rewriting.Term                 as R

import qualified Tct.Core.Common.Pretty              as PP
import qualified Tct.Core.Common.Xml                 as Xml
import qualified Tct.Core.Data                       as T
import           Tct.Core.Data.Declaration.Parse     ()

import qualified Tct.Common.Polynomial               as P
import           Tct.Common.PolynomialInterpretation (Shape)
import qualified Tct.Common.PolynomialInterpretation as PI
import           Tct.Common.ProofCombinators
import           Tct.Common.Ring
import           Tct.Common.SMT                      ((.==>), (.>), (.>=))
import qualified Tct.Common.SMT                      as SMT

import           Tct.Trs.Data
import           Tct.Trs.Data.Arguments              (Greedy (..), UsableArgs (..), UsableRules (..))
import qualified Tct.Trs.Data.Arguments              as Arg
-- import qualified Tct.Trs.Data.ComplexityPair         as CP
import qualified Tct.Trs.Data.Problem                as Prob
import qualified Tct.Trs.Data.ProblemKind            as Prob
import qualified Tct.Trs.Data.RuleSelector           as RS
import qualified Tct.Trs.Data.Signature              as Sig
import qualified Tct.Trs.Data.Trs                    as Trs
import qualified Tct.Trs.Encoding.Interpretation     as I
import qualified Tct.Trs.Encoding.UsableRules        as UREnc


data NaturalPI = NaturalPI
  { shape    :: PI.Shape
  , uargs    :: Arg.UsableArgs
  , urules   :: Arg.UsableRules
  , selector :: Maybe (ExpressionSelector F V)
  , greedy   :: Arg.Greedy
  } deriving Show

type Kind           = PI.Kind F

data PolyOrder c = PolyOrder
  { kind_ :: Kind
  , pint_ :: I.InterpretationProof (P.Polynomial c PI.SomeIndeterminate) (P.Polynomial c V)
  } deriving Show

type NaturalPIProof = OrientationProof (PolyOrder Int)

instance T.Processor NaturalPI where
  type ProofObject NaturalPI = ApplicationProof NaturalPIProof
  type I NaturalPI           = TrsProblem
  type O NaturalPI           = TrsProblem
  type Forking NaturalPI     = T.Optional T.Id

  solve p prob
    | Prob.isTrivial prob = return . T.resultToTree p prob $ T.Fail Closed
    | otherwise           = entscheide p prob

certification :: PolyOrder Int -> T.Optional T.Id T.Certificate -> T.Certificate
certification order cert = case cert of
  T.Null         -> T.timeUBCert bound
  T.Opt (T.Id c) -> T.updateTimeUBCert c (`add` bound)
  where bound = PI.bound (kind_ order) (PI.PolyInter . I.interpretations . I.inter_ $ pint_ order)

instance I.AbstractInterpretation NaturalPI where
  type (A NaturalPI) = P.PView (PI.CoefficientVar F) PI.SomeIndeterminate
  type (B NaturalPI) = P.Polynomial SMT.IExpr PI.SomeIndeterminate
  type (C NaturalPI) = P.Polynomial SMT.IExpr V 

  encode _ = P.fromViewWithM enc where
    enc c
      | PI.restrict c = SMT.snvarM'
      | otherwise     = SMT.nvarM'

  setMonotone _ fpoly is  = SMT.bigAnd $ k `fmap` is
    where k i = P.getCoefficient fpoly [(toEnum i,1)] .> zero

  setInFilter _ fpoly inFilter = afpoly (P.toView fpoly)
    where
      afpoly po = SMT.bigAnd [ c .> zero .==> (afmono mo) | (c, mo) <- po ]
      afmono mo = SMT.bigAnd [ inFilter (fromEnum vi) | (vi,_) <- mo ]

  interpret _ = interpretf

  addConstant _ f v = f `add`  P.constant v
  gte _ p1 p2       = SMT.bigAnd [ c .>= SMT.zero | c <- P.coefficients $ p1 `sub` p2 ]

interpretf :: (Show c, Show fun, SemiRing c, Eq c, Ord fun, Ord var) => I.Interpretation fun (PI.SomePolynomial c) -> R.Term fun var -> P.Polynomial c var
interpretf ebsi = I.interpretTerm interpretFun interpretVar
  where
    interpretFun f = P.substituteVariables (I.interpretations ebsi M.! f) . M.fromList . zip PI.indeterminates
    interpretVar v = P.variable v

entscheide :: NaturalPI -> TrsProblem -> T.TctM (T.Return (T.ProofTree TrsProblem))
entscheide p prob = do
  let
    orientM                   = I.orient p prob absi shift (uargs p == Arg.UArgs) (urules p == Arg.URules)
    (ret, encoding)           = SMT.runSolverM orientM SMT.initialState
    (apint,decoding,forceAny) = ret
    aorder = PolyOrder
      { kind_ = kind
      , pint_ = apint }

  toResult `fmap` entscheide1 p aorder encoding decoding forceAny prob 
  where
    toResult pt = if T.progress pt then T.Continue pt else T.Abort pt

    sig   = Prob.signature prob
    kind  =
      if Prob.isRCProblem prob
        then PI.ConstructorBased (shape p) (Prob.constructors (Prob.startTerms prob) `S.union` Sig.symbols (Sig.filter Prob.isCompoundf sig))
        else PI.Unrestricted (shape p)
    absi  = I.Interpretation $ M.mapWithKey (curry $ PI.mkInterpretation kind) (Sig.toMap sig)
    shift = maybe I.All I.Shift (selector p)

entscheide1 :: 
  NaturalPI 
  -> PolyOrder c 
  -> SMT.SolverState SMT.Expr
  -> (I.Interpretation F (PI.SomePolynomial SMT.IExpr), Maybe (UREnc.UsableEncoder F))
  -> I.ForceAny
  -> Problem F V 
  -> T.TctM (T.ProofTree (Problem F V))
entscheide1 p aorder encoding decoding forceAny prob
  | Prob.isTrivial prob = return . I.toTree p prob $ T.Fail (Applicable Incompatible)
  | otherwise           = do
    res :: SMT.Result (I.Interpretation F (PI.SomePolynomial Int), Maybe (UREnc.UsableSymbols F))
      <- liftIO $ SMT.solve SMT.minismt (encoding `assertx` forceAny srules) (SMT.decode decoding)
    case res of
      SMT.Sat a
        | Arg.useGreedy (greedy p) -> fmap T.flatten $ again `F.mapM` pt
        | otherwise                -> return pt

        where 
          pt    = I.toTree p prob $ T.Success (I.newProblem prob (pint_ order)) (Applicable $ Order order) (certification order)
          order = mkOrder a

      _ -> return $ I.toTree p prob $ T.Fail (Applicable Incompatible)
      where
        again = entscheide1 p aorder encoding decoding forceAny
        
        assertx st e = st {SMT.asserts = e: SMT.asserts st}
        srules = Trs.toList $ Prob.strictComponents prob 

        mkOrder (inter, ufuns) = aorder { pint_ = mkInter (pint_ aorder) inter ufuns }
        mkInter aproof inter ufuns = aproof
          { I.inter_     = inter
          , I.ufuns_     = maybe S.empty UREnc.runUsableSymbols ufuns
          , I.strictDPs_ = sDPs
          , I.strictTrs_ = sTrs
          , I.weakDPs_   = wDPs
          , I.weakTrs_   = wTrs }
          where

          (sDPs,wDPs) = L.partition isStrict (rs $ Prob.dpComponents prob)
          (sTrs,wTrs) = L.partition isStrict (rs $ Prob.trsComponents prob)
          isStrict (r,(lpoly,rpoly)) = r `Trs.member` Prob.strictComponents prob && P.constantValue (lpoly `sub` rpoly) > 0
          rs trs =
            [ (r, (interpretf inter lhs, interpretf inter rhs))
            | r@(R.Rule lhs rhs) <- Trs.toList trs
            , isUsable ufuns r ]

          isUsable Nothing _                = True
          isUsable (Just fs) (R.Rule lhs _) = either (const False) (`S.member` UREnc.runUsableSymbols fs) (R.root lhs)
    

--- * instances ------------------------------------------------------------------------------------------------------

description :: [String]
description =  [ "This processor tries to find a polynomial interpretation and shifts strict oriented rules to the weak components." ]

selectorArg :: T.Argument 'T.Required (Maybe (ExpressionSelector f v))
selectorArg = T.some RS.selectorArg 
  `T.withName` "shift"
  `T.withHelp`
    [ "This argument specifies which rules to orient strictly and shift to the weak components." ]

comp5 :: (s -> t) -> (t1 -> t2 -> t3 -> t4 -> t5 -> s) -> t1 -> t2 -> t3 -> t4 -> t5 -> t
comp5 f g a b c d e = f $ g a b c d e




polyProcessor :: PI.Shape -> Arg.UsableArgs -> Arg.UsableRules -> Maybe (ExpressionSelector F V) -> Arg.Greedy -> NaturalPI
polyProcessor sh ua ur sl gr = NaturalPI
  { shape    = sh
  , uargs    = ua
  , urules   = ur
  , selector = sl 
  , greedy   = gr }

instance Arg.HasKind NaturalPI where
  type (Kind NaturalPI) = PI.Shape
  withKind p a = p { shape = a }  

instance Arg.HasUsableArgs NaturalPI where
  withUsableArgs p a = p { uargs = a }  

instance Arg.HasUsableRules NaturalPI where
  withUsableRules p a = p { urules = a }  

instance Arg.HasSelection NaturalPI where
  withSelection p a = p { selector = Just a }  

instance Arg.HasGreedy NaturalPI where
  withGreedy p a = p { greedy = a }  


args ::
  ( T.Argument 'T.Optional PI.Shape
  , T.Argument 'T.Optional Arg.UsableArgs
  , T.Argument 'T.Optional Arg.UsableRules
  , T.Argument 'T.Optional (Maybe (ExpressionSelector F V))
  , T.Argument 'T.Optional Arg.Greedy)
args = 
  ( PI.shapeArg `T.optional` PI.Linear 
  , Arg.usableArgs `T.optional` Arg.UArgs
  , Arg.usableRules `T.optional` Arg.URules
  , selectorArg `T.optional` Just (RS.selAnyOf RS.selStricts)
  , Arg.greedy `T.optional` Arg.Greedy )

--- ** processor -----------------------------------------------------------------------------------------------------

polyProcDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional PI.Shape 
   , T.Argument 'T.Optional Arg.UsableArgs
   , T.Argument 'T.Optional Arg.UsableRules 
   , T.Argument 'T.Optional (Maybe (ExpressionSelector F V)) 
   , T.Argument 'T.Optional Arg.Greedy ]
   T.:-> NaturalPI)
polyProcDeclaration = T.declare "poly" description args polyProcessor

polyProc :: NaturalPI
polyProc = T.deflFun polyProcDeclaration


--- ** strategy ------------------------------------------------------------------------------------------------------


polyDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional PI.Shape 
   , T.Argument 'T.Optional Arg.UsableArgs
   , T.Argument 'T.Optional Arg.UsableRules 
   , T.Argument 'T.Optional (Maybe (ExpressionSelector F V)) 
   , T.Argument 'T.Optional Arg.Greedy ]
   T.:-> TrsStrategy )
polyDeclaration = T.declare "poly" description args (T.Proc `comp5` polyProcessor)


poly :: TrsStrategy
poly = T.deflFun polyDeclaration

poly' :: PI.Shape -> Arg.UsableArgs -> Arg.UsableRules -> Maybe (ExpressionSelector F V) -> Arg.Greedy -> TrsStrategy
poly' = T.declFun polyDeclaration


--- ** complexity pair -----------------------------------------------------------------------------------------------

-- instance IsComplexityPair NaturalPI where
--   solveComplexityPair p sel prob = do
--     -- MS: TODO: generalise solve function returning prooftree+compleixtypairProof
--     ret <- T.evaluate (T.Proc p{selector=Just sel}) prob
--     return $ error "not yet implemented"
--
-- polyCPDeclaration :: T.Declaration (
--   '[ T.Argument 'T.Optional PI.Shape 
--    , T.Argument 'T.Optional Arg.UsableArgs
--    , T.Argument 'T.Optional Arg.UsableRules 
--    , T.Argument 'T.Optional (Maybe (ExpressionSelector F V)) 
--    , T.Argument 'T.Optional Arg.Greedy ]
--    T.:-> ComplexityPair )
-- polyCPDeclaration = T.declare "poly" description args (CP.toComplexityPair `comp5` polyProcessor)


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty (PolyOrder Int) where
  pretty order = PP.vcat
    [ PP.text "We apply a polynomial interpretation of kind " <> PP.pretty (kind_ order) <> PP.char ':'
    , PP.pretty $ I.prettyProof (pint_ order) ]

instance Xml.Xml (PolyOrder Int) where
  toXml order = I.xmlProof (pint_ order) xtype where
    xtype   = Xml.elt "type" [Xml.elt "polynomial" [xdomain, xdegree]]
    xdegree = Xml.elt "degree" [Xml.int $ PI.degree . PI.PolyInter . I.interpretations . I.inter_ $ pint_ order]
    xdomain = Xml.elt "domain" [Xml.elt "naturals" []]
  toCeTA = Xml.toXml

