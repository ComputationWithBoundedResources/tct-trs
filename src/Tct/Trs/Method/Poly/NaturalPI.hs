{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Trs.Method.Poly.NaturalPI
  (
  -- * Declaration
  poly
  , poly'
  , polyDeclaration
  -- * Strategies
  , stronglyLinear
  , linear
  , quadratic
  , mixed

  -- * Processor
  -- , polyDeclarationCP
  ) where


import Control.Monad (when)
import Control.Monad.Error                           (throwError, MonadError)
import Control.Monad.Trans                           (liftIO, MonadIO)
import qualified Data.List                           as L
import qualified Data.Map.Strict                     as M
import           Data.Monoid ((<>))
import qualified Data.Set                            as S

import qualified Data.Rewriting.Rule                 as R (Rule (..))
import qualified Data.Rewriting.Term                 as R

import qualified Tct.Core.Common.Pretty              as PP
import qualified Tct.Core.Common.Xml                 as Xml
import qualified Tct.Core.Data                       as T
import           Tct.Core.Data.Declaration.Parse     ()

import qualified Tct.Common.Polynomial               as P
import qualified Tct.Common.PolynomialInterpretation as PI
import           Tct.Common.ProofCombinators
import           Tct.Common.Ring
import           Tct.Common.SMT                     ((.==>), (.>), (.>=))
import qualified Tct.Common.SMT                     as SMT

import           Tct.Trs.Data
import           Tct.Trs.Data.Arguments
-- import           Tct.Trs.Data.ComplexityPair
import qualified Tct.Trs.Data.Problem                as Prob
import qualified Tct.Trs.Data.ProblemKind            as Prob
import qualified Tct.Trs.Data.RuleSelector           as Trs
import qualified Tct.Trs.Data.Signature              as Sig
import qualified Tct.Trs.Data.Trs                    as Trs
import qualified Tct.Trs.Encoding.UsablePositions    as UPEnc
import qualified Tct.Trs.Encoding.UsableRules        as UREnc
import qualified Tct.Trs.Encoding.Interpretation as I





data NaturalPI = NaturalPI
  { shape    :: PI.Shape
  , uargs    :: Bool
  , urules   :: Bool
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
  type Problem NaturalPI     = TrsProblem
  type Forking NaturalPI     = T.Optional T.Id

  solve p prob
    | Prob.isTrivial prob = return . T.resultToTree p prob $ T.Fail Closed
    | otherwise           = do
        res <- entscheide p prob
        case res of
          -- SMT.Sat order -> toProof $ T.Success (newProblem prob order) (Applicable $ Order order) (certification order)
          SMT.Sat order 
            | progressing nprob -> toProof $ T.Success nprob (Applicable $ Order order) (certification order)
            -- MS: sanity check: if satisfiable we should have progress
            | otherwise         -> throwError $ userError "naturalpi: sat but no progresss :/"
            where nprob = newProblem prob order
          _             -> toProof $ T.Fail (Applicable Incompatible)
        where 
          toProof = return . T.resultToTree p prob
          progressing T.Null               = True
          progressing (T.Opt (T.Id nprob)) = Prob.progressUsingSize prob nprob

newProblem :: TrsProblem -> PolyOrder Int -> T.Optional T.Id TrsProblem
newProblem prob order = case I.shift_ (pint_ order) of
  I.All     -> T.Null
  I.Shift _ -> T.Opt . T.Id $ prob
    { Prob.strictDPs = Prob.strictDPs prob `Trs.difference` sDPs
    , Prob.strictTrs = Prob.strictTrs prob `Trs.difference` sTrs
    , Prob.weakDPs   = Prob.weakDPs prob `Trs.union` sDPs
    , Prob.weakTrs   = Prob.weakTrs prob `Trs.union` sTrs }
  where
    rules = Trs.fromList . fst . unzip
    sDPs = rules (I.strictDPs_ $ pint_ order)
    sTrs = rules (I.strictTrs_ $ pint_ order)

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

--entscheide :: (MonadError e m, MonadIO m) => NaturalPI -> TrsProblem -> m (SMT.Result (PolyOrder Int))
entscheide :: NaturalPI -> Problem F V -> T.TctM (SMT.Result (PolyOrder Int))
entscheide p prob = do
  mto <- (maybe [] (\i -> ["-t", show i]) . T.remainingTime) `fmap` T.askStatus prob
  res :: SMT.Result (I.Interpretation F (PI.SomePolynomial Int), UPEnc.UsablePositions F, Maybe (UREnc.UsableSymbols F))
    -- <- liftIO $ SMT.solveStM SMT.minismt $ SMT.decode `fmap` I.orient p prob absi shift (uargs p) (urules p)
    <- liftIO $ SMT.solveStM (SMT.minismt' $ ["-m", "-v2", "-neg"] ++ mto) $ SMT.decode `fmap` I.orient p prob absi shift (uargs p) (urules p)
  
  return $ mkOrder `fmap` res
  where
    shift = maybe I.All I.Shift (selector p)
    sig   = Prob.signature prob
    absi  = I.Interpretation $ M.mapWithKey (curry $ PI.mkInterpretation kind) (Sig.toMap sig)
    kind  =
      if Prob.isRCProblem prob
        then PI.ConstructorBased (shape p) (Prob.constructors (Prob.startTerms prob) `S.union` Sig.symbols (Sig.filter Prob.isCompoundf sig))
        else PI.Unrestricted (shape p)
    
    mkOrder (inter, uposs, ufuns) = PolyOrder
      { kind_      = kind
      , pint_    = pinter }
      where
      pinter = I.InterpretationProof 
        { I.sig_       = sig
        , I.inter_     = inter
        , I.uargs_     = uposs
        , I.ufuns_     = maybe S.empty UREnc.runUsableSymbols ufuns
        , I.shift_     = shift
        , I.strictDPs_ = sDPs
        , I.strictTrs_ = sTrs
        , I.weakDPs_   = wDPs
        , I.weakTrs_   = wTrs }

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

polyProc :: PI.Shape -> Bool -> Bool -> Maybe (ExpressionSelector F V) -> NaturalPI
polyProc sh ua ur sl = NaturalPI
  { shape    = sh
  , uargs    = ua
  , urules   = ur
  , selector = sl }

polyProcDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional PI.Shape 
   , T.Argument 'T.Optional Bool 
   , T.Argument 'T.Optional Bool 
   , T.Argument 'T.Optional (Maybe (ExpressionSelector F V)) ]
   T.:-> NaturalPI)
polyProcDeclaration = T.declare "poly" description (shArg, uaArg `T.optional` True,  urArg `T.optional` True, slArg) polyProc 


polyProcDeclaration2 = T.declare 
  "poly" 
  (T.declHelp polyProcDeclaration) 
  -- (T.declArgs polyProcDeclaration)
  (shArg, uaArg `T.optional` True,  urArg `T.optional` True, slArg) 
  (T.Proc `comp4` T.declFun polyProcDeclaration)

-- polyDeclaration :: T.Declaration (
--   '[ T.Argument 'T.Optional PI.Shape 
--    , T.Argument 'T.Optional Bool 
--    , T.Argument 'T.Optional Bool 
--    , T.Argument 'T.Optional (Maybe (ExpressionSelector F V)) ]
--    T.:-> T.Strategy TrsProblem)
-- polyDeclaration = T.declare 
--   "poly" 
--   (T.declHelp polyProcDeclaration)
--   (T.declArgs polyProcDeclaration)
--   (\a1 a2 a3 a4 -> T.Proc $ polyProc a1 a2 a3 a4)
polyDeclaration = undefined
--
--
-- polyProc :: PI.Shape -> Bool -> Bool -> Maybe (ExpressionSelector F V) -> NaturalPI
-- polyProc sh ua ur sl = NaturalPI
--   { shape    = sh
--   , uargs    = ua
--   , urules   = ur
--   , selector = sl }
--
--
--
-- lift4 f p = T.declare (T.declName p)  (T.declHelp p) (T.declArgs p) (f `comp4` T.declFun p)
comp4 f g a b c d = f $ g a b c d 


polyStrategy :: PI.Shape -> Bool -> Bool -> Maybe (ExpressionSelector F V) -> T.Strategy TrsProblem
polyStrategy sh ua ur sl = T.Proc $ NaturalPI
  { shape    = sh
  , uargs    = ua
  , urules   = ur
  , selector = sl }

description :: [String]
description =  [ "This processor tries to find a polynomial interpretation and shifts strict oriented rules to the weak components." ]

shArg :: T.Argument 'T.Optional PI.Shape
shArg = PI.shapeArg `T.optional` PI.Linear

slArg :: T.Argument 'T.Optional (Maybe (ExpressionSelector f v))
slArg = T.some Trs.selectorArg 
  `T.withName` "shift"
  `T.withHelp`
    [ "This argument specifies which rules to orient strictly and shift to the weak components." ]
  `T.optional` Nothing

-- polyDeclaration :: T.Declaration (
--   '[ T.Argument 'T.Optional PI.Shape 
--    , T.Argument 'T.Optional Bool 
--    , T.Argument 'T.Optional Bool 
--    , T.Argument 'T.Optional (Maybe (ExpressionSelector F V)) ]
--    T.:-> T.Strategy TrsProblem)
-- polyDeclaration = T.declare "poly" description (shArg, uaArg `T.optional` True,  urArg `T.optional` True, slArg) polyStrategy where

poly :: T.Strategy TrsProblem
poly = undefined -- T.deflFun polyDeclaration

poly' :: PI.Shape -> Bool -> Bool -> Maybe (ExpressionSelector F V) -> T.Strategy TrsProblem
poly' = undefined -- T.declFun polyDeclaration

-- TODO: MS: better interface
-- can we do without exposing the processor type a builder a -> Strategy with modifyers f a -> a?
stronglyLinear :: Bool -> Bool -> Maybe (ExpressionSelector F V) -> T.Strategy TrsProblem
stronglyLinear ua ur sl = T.Proc $ NaturalPI
  { shape    = PI.Linear
  , uargs    = ua
  , urules   = ur
  , selector = sl }

linear :: Bool -> Bool -> Maybe (ExpressionSelector F V) -> T.Strategy TrsProblem
linear ua ur sl = T.Proc $ NaturalPI
  { shape    = PI.Linear
  , uargs    = ua
  , urules   = ur
  , selector = sl }

quadratic :: Bool -> Bool -> Maybe (ExpressionSelector F V) -> T.Strategy TrsProblem
quadratic ua ur sl = T.Proc $ NaturalPI
  { shape    = PI.Quadratic
  , uargs    = ua
  , urules   = ur
  , selector = sl }

mixed :: Int -> Bool -> Bool -> Maybe (ExpressionSelector F V) -> T.Strategy TrsProblem
mixed i ua ur sl = T.Proc $ NaturalPI
  { shape    = PI.Mixed i
  , uargs    = ua
  , urules   = ur
  , selector = sl }


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



{-


instance IsComplexityPair PolyInterProcessor where
  solveComplexityPair p sel prob = do
    -- MS: TODO: generalise solve function returning prooftree+compleixtypairProof
    ret <- T.evaluate (T.Proc p{selector=Just sel}) prob
    return $ error "not yet implemented"

polyProc = PolyInterProc {}



--- * instances ------------------------------------------------------------------------------------------------------

description =  [ "This processor tries to find a polynomial interpretation and shifts strict oriented rules to the weak components." ]
shArg = PI.shapeArg `T.optional` PI.Linear

slArg = T.some Trs.selectorArg 
  `T.withName` "shift"
  `T.withHelp`
    [ "This argument specifies which rules to orient strictly and shift to the weak components." ]
  `T.optional` Nothing

polyDeclaration :: T.Declaration (
  '[ T.Argument 'T.Optional PI.Shape 
   , T.Argument 'T.Optional Bool 
   , T.Argument 'T.Optional Bool 
   , T.Argument 'T.Optional (Maybe (ExpressionSelector F V)) ]
   T.:-> T.Strategy TrsProblem)
polyDeclaration = T.declare "poly" description (shArg, uaArg `T.optional` True,  urArg `T.optional` True, slArg) poly where

polyDeclarationCP :: T.Declaration (
  '[ T.Argument 'T.Optional PI.Shape 
   , T.Argument 'T.Optional Bool 
   , T.Argument 'T.Optional Bool 
   , T.Argument 'T.Optional (Maybe (ExpressionSelector F V)) ]
   T.:-> ComplexityPair )
polyDeclarationCP = T.declare "poly" description (shArg, uaArg `T.optional` True,  urArg `T.optional` True, slArg)  (\a1 a2 a3 a4 -> ComplexityPair (PolyInterProc a1 a2 a3 a4))



poly :: PI.Shape -> Bool -> Bool -> Maybe (ExpressionSelector F V) -> T.Strategy TrsProblem
poly sh ua ur sl = T.Proc $ PolyInterProc
  { shape    = sh
  , uargs    = ua
  , urules   = ur
  , selector = sl }


-}
