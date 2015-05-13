{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Tct.Trs.Method.Weightgap
Description : Matrix interpretation over naturals
Copyright   : (c) since tct-trs
                  Martin Avanzini <martin.avanzini@uibk.ac.at>,
                  Andreas Kochesser <andreas.kochesser@uibk.ac.at>,
                  Georg Moser <georg.moser@uibk.ac.at>,
                  Michael Schaper <michael.schaper@uibk.ac.at>,
                  Maria Schett <maria.schett@uibk.ac.at>
              (c) since tct 2
                  Martin Avanzini <martin.avanzini@uibk.ac.at>,
                  Georg Moser <georg.moser@uibk.ac.at>,
                  Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     : see LICENSE
Maintainer  : andreas.kochesser@uibk.ac.at
Stability   : unstable
Portability : unportable

-}


module Tct.Trs.Method.Weightgap where

-- general imports
import           Control.Monad.Trans                        (liftIO)
import qualified Data.Foldable                              as F
import           Data.Maybe
import qualified Data.Map                                   as Map
import qualified Data.Set                                   as Set
import qualified Data.List                                  as List
import qualified Data.Traversable                           as F
import qualified Data.Typeable                              as DT
import qualified Data.Rewriting.Rule                        as RR (Rule (..))
import qualified Data.Rewriting.Term                        as RT

-- imports tct-common
import qualified Tct.Common.ProofCombinators                as PC
import qualified Tct.Core.Common.Pretty                     as PP
import           Tct.Common.SMT                             (one, zero, (.<=>), (.==), (.==>), (.>))
import qualified Tct.Common.SMT                             as SMT

-- imports tct-core
import qualified Tct.Core.Data                              as CD
import qualified Tct.Core.Common.Xml                        as Xml


-- imports tct-trs
import qualified Tct.Trs.Data.Arguments                     as Arg
import           Tct.Trs.Data.Arguments                     (UsableArgs (..), UsableRules (..), Greedy (..))
import qualified Tct.Trs.Method.Matrix.Matrix               as MX
import qualified Tct.Trs.Method.Matrix.MatrixInterpretation as MI
import qualified Tct.Trs.Method.Matrix.NaturalMI            as NMI
import qualified Tct.Trs.Data.RuleSelector                  as RS
import qualified Tct.Trs.Data.Problem                       as Prob
import qualified Tct.Trs.Data.ProblemKind                   as ProbK
import qualified Tct.Trs.Encoding.Interpretation            as I
import qualified Tct.Trs.Encoding.UsableRules               as UREnc
import qualified Tct.Trs.Encoding.UsablePositions           as UPEnc
import qualified Tct.Trs.Data.Signature                     as Sig
import qualified Tct.Trs.Data.Trs                           as TRS

data WeightGap = WeightGap { wgOn :: WgOn
                           , wgNMI :: NMI.NaturalMI}
                 deriving (Show)





data WgOn = WgOnTrs -- ^ Orient at least all non-DP rules.
          | WgOnAny -- ^ Orient some rule.
            deriving (Eq, DT.Typeable, Bounded, Enum)

instance Show WgOn where
  show WgOnTrs = "trs"
  show WgOnAny = "any"

data WeightGapProof =
  WeightGapProof { wgProof :: PC.OrientationProof (NMI.MatrixOrder Int)
                 , wgConstGrowth :: Maybe Bool
                 }
  deriving (Show)

data Orientation = OrientStrict (RR.Rule Prob.F Prob.V)
                 deriving (Eq, Ord, Show, DT.Typeable)


entscheide :: WeightGap -> Prob.TrsProblem -> CD.TctM (CD.Return (CD.ProofTree Prob.TrsProblem))
entscheide p prob = do
  mxo <- entscheideMxO (wgNMI p) aorder encoding (decoding,Nothing) prob
  return $ toResult $ mkProof mxo
  where
    (ret,encoding) = SMT.runSolverM (orientWG p prob) SMT.initialState
    (apint,mKind,decoding) = ret
    toResult pt = if CD.progress pt then CD.Continue pt else CD.Abort pt
    wgon = wgOn p
    aorder = NMI.MatrixOrder
      { NMI.kind_ = mKind
      , NMI.dim_ = NMI.miDimension $ wgNMI p
      , NMI.mint_ = apint}
    mkProof morder
      | TRS.null oriented = I.toTree p prob $ CD.Fail (PC.Applicable $ PC.Order tproof)
      | otherwise = I.toTree p prob $ CD.Success (I.newProblem prob mi) (PC.Applicable $ PC.Order tproof) (NMI.certification (wgNMI p) ord)
      where
        ord = case morder of
              PC.Order o -> o
              _ -> error "Trs.Method.Weightgap.entscheide: OrientationProof data is not a Order"
        mi = NMI.mint_ ord
        tproof = --PC.OrientationProof $
          WeightGapProof { wgProof = morder
                         , wgConstGrowth = Just $ TRS.null (Prob.strictTrs prob) || wgon == WgOnTrs}
        oriented =
          case morder of
           PC.Order _ -> (TRS.fromList . map fst $ I.strictTrs_ mi) `TRS.union` (TRS.fromList . map fst $ I.strictDPs_ mi)
           _            -> TRS.empty


entscheideMxO ::
  NMI.NaturalMI
  -> NMI.MatrixOrder c
  -> SMT.SolverState SMT.Expr
  -> (I.Interpretation Prob.F (MI.LinearInterpretation MI.SomeIndeterminate SMT.IExpr), Maybe (UREnc.UsableEncoder Prob.F))
  -> Prob.TrsProblem
  -> CD.TctM (PC.OrientationProof (NMI.MatrixOrder Int))
entscheideMxO p aorder encoding decoding prob
  | Prob.isTrivial prob = return PC.Incompatible
  | otherwise = do
    mto <- CD.remainingTime `fmap` CD.askStatus prob
    res :: SMT.Result (I.Interpretation Prob.F (MI.LinearInterpretation MI.SomeIndeterminate Int), Maybe (UREnc.UsableSymbols Prob.F))
      <- liftIO $ SMT.solve (SMT.minismt mto) encoding (SMT.decode decoding)
    case res of
      SMT.Sat a -> return $ PC.Order order
        where
          order = mkOrder a
      _         -> return PC.Incompatible
  where
    mkOrder (inter, ufuns) = aorder {NMI.mint_ = mkInter (NMI.mint_ aorder) inter ufuns }
    mkInter aproof inter ufuns = aproof
      { I.inter_     = inter
      , I.ufuns_     = maybe Set.empty UREnc.runUsableSymbols ufuns
      , I.strictDPs_ = sDPs
      , I.strictTrs_ = sTrs
      , I.weakDPs_   = wDPs
      , I.weakTrs_   = wTrs }
      where
        (sDPs,wDPs) = List.partition (\(r,i) -> r `TRS.member` Prob.strictComponents prob && uncurry NMI.isStrict i) (rs $ Prob.dpComponents prob)
        (sTrs,wTrs) = List.partition (\(r,i) -> r `TRS.member` Prob.strictComponents prob && uncurry NMI.isStrict i) (rs $ Prob.trsComponents prob)
        rs trs =
          [ (r, (NMI.interpretf (NMI.miDimension p) inter  lhs, NMI.interpretf (NMI.miDimension p) inter  rhs))
          | r@(RR.Rule lhs rhs) <- TRS.toList trs
          , isUsable ufuns r]

        isUsable Nothing _ = True
        isUsable (Just fs) (RR.Rule lhs _) = either (const False) (`Set.member` UREnc.runUsableSymbols fs) (RT.root lhs)


orientWGConstraints :: NMI.NaturalMI -> Map.Map (RR.Rule Prob.F Prob.V) SMT.IExpr -> I.Interpretation Prob.F (MI.LinearInterpretation MI.SomeIndeterminate SMT.IExpr) -> TRS.Trs Prob.F Prob.V -> SMT.Formula SMT.IFormula
orientWGConstraints nmi svars smtint sr = SMT.bigAnd [ ruleConstraint rl | rl  <- TRS.toList sr]
  where
    interpretTerm = I.interpret nmi
    ruleConstraint rl = wgConstraint `SMT.band` ((fromJust (Map.lookup rl svars) SMT..== SMT.one) SMT..==> orientConstraint)
      where
        li = I.interpret nmi smtint (RR.lhs rl)
        ri = interpretTerm smtint (RR.rhs rl)
        d = NMI.miDimension nmi
        geqVec (MX.Vector v1) (MX.Vector v2) = SMT.bigAnd $ zipWith (SMT..>=) v1 v2
        gtVec (MX.Vector (v1:vs1)) (MX.Vector (v2:vs2)) = (v1 SMT..> v2) `SMT.band` geqVec (MX.Vector vs1) (MX.Vector vs2)
        wgConstraint = SMT.bigAnd [ maybe SMT.bot
                                    (\lm -> geqVec (MX.mRow 1 lm) (MX.mRow 1 rm)) (Map.lookup v $ MI.coefficients li)
                                  | (v,rm) <- Map.toList $ MI.coefficients ri]
        orientConstraint = SMT.bigAnd [ maybe SMT.bot
                                        (\lm -> SMT.bigAnd [ geqVec (MX.mRow j lm) (MX.mRow j rm) | j <- [2..d]])
                                        (Map.lookup v $ MI.coefficients li)
                                      | (v,rm) <- Map.toList $ MI.coefficients ri]
                           `SMT.band` gtVec (MI.constant li) (MI.constant ri)

orientWG :: WeightGap -> Prob.TrsProblem -> SMT.SolverM (SMT.SolverState SMT.Expr) (I.InterpretationProof a b, MI.MatrixKind Prob.F, I.Interpretation Prob.F (MI.LinearInterpretation MI.SomeIndeterminate SMT.IExpr))
orientWG p prob = do
  smtint <- F.mapM (I.encode mp) absmi
  strictVarEncoder <- Map.fromList `fmap` F.mapM (\r -> SMT.nvarM' >>= \v -> return (r,v)) (TRS.toList allrules)

  let
    strict = (strictVarEncoder Map.!)
    orientSelected (TRS.SelectDP r)  = strict r .> zero
    orientSelected (TRS.SelectTrs r) = strict r .> zero
    orientSelected (TRS.BigAnd es)   = SMT.bigAnd (orientSelected `fmap` es)
    orientSelected (TRS.BigOr es)    = SMT.bigOr (orientSelected `fmap` es)

    (.>=.) = I.gte mp
    interpretf = I.interpret mp smtint
    weakOrderConstraints rls = SMT.bigAnd [ wOrder r | r <- TRS.toList rls ]
      where
        wOrder r = interpretf (RR.lhs r) .>=. interpretf (RR.rhs r)


  SMT.assert $ orientSelected se'
  SMT.assert $ orientWGConstraints (wgNMI p) strictVarEncoder smtint sr
  SMT.assert $ weakOrderConstraints wr
  SMT.assert $ NMI.slmiSafeRedpairConstraints (NMI.miDimension mp) ua smtint
  SMT.assert $ NMI.uargMonotoneConstraints ua smtint
  SMT.assertM $ NMI.kindConstraints mk smtint
  return (proof ua,mk,smtint)
    where
    mp = wgNMI p
    absmi = I.Interpretation $ Map.mapWithKey (curry $ MI.abstractInterpretation mk d) (Sig.toMap $ Prob.signature prob)
    d = NMI.miDimension mp
    se = (RS.rsSelect . fromJust . NMI.selector . wgNMI $ p) prob
    se' | wgOn p == WgOnTrs = RS.BigAnd $ se :[ RS.SelectTrs r | r <- TRS.toList strs]
        | otherwise = se

    miKnd | TRS.null strs || wgOn p == WgOnTrs = NMI.miKind mp
          | NMI.miKind mp == NMI.Unrestricted = NMI.Algebraic
          | otherwise                        = NMI.miKind mp

    deg | TRS.null strs || wgOn p == WgOnTrs = NMI.miDegree mp
        | otherwise = 1

    -- ua = case Prob.startTerms prob of
    --   Prob.BasicTerms {}
    --     | NMI.uargs mp == Arg.UArgs -> UPEnc.usableArgs (Prob.strategy prob) allrules
    --   _ -> UPEnc.fullWithSignature (Prob.signature prob)

    ua = UPEnc.usableArgsWhereApplicable prob False (NMI.uargs mp == Arg.UArgs)

    mk = NMI.kind mp st
      where
        st | TRS.null strs || wgOn p == WgOnTrs = Prob.startTerms prob
           | otherwise = toTA $ Prob.startTerms prob
        toTA (ProbK.BasicTerms defs cons) = ProbK.AllTerms $ Set.union defs cons
        toTA st'                          = st'

    sr = Prob.strictComponents prob
    wr = Prob.weakComponents prob
    strs = Prob.strictTrs prob
    allrules = Prob.allComponents prob

    proof uposs = I.InterpretationProof
                  { I.sig_ = Prob.signature prob
                  , I.inter_ = I.Interpretation Map.empty
                  , I.uargs_ = uposs
                  , I.ufuns_ = Set.empty
                  , I.shift_ = I.Shift . fromJust . NMI.selector . wgNMI $ p
                  , I.strictDPs_ = []
                  , I.strictTrs_ = []
                  , I.weakDPs_   = []
                  , I.weakTrs_   = [] }


--onSelectedRequire :: RS.SelectorExpression -> (Bool -> RR.Rule -> a) -> a


weightGapStrategy :: WgOn
                  -> Int -> Int -> NMI.NaturalMIKind -> Arg.UsableArgs -> Arg.UsableRules
                  -> Maybe (RS.ExpressionSelector Prob.F Prob.V)
                  -> Arg.Greedy
                  -> CD.Strategy Prob.TrsProblem Prob.TrsProblem
weightGapStrategy on dim deg miKind ua ur sl gr = CD.Proc
  WeightGap { wgOn = on
            , wgNMI = NMI.NaturalMI { NMI.miDimension = dim
                                    , NMI.miDegree    = deg
                                    , NMI.miKind      = miKind
                                    , NMI.uargs       = ua
                                    , NMI.urules      = ur
                                    , NMI.selector    = sl
                                    , NMI.greedy      = gr
                                    }
            }

argWgOn :: CD.Argument 'CD.Optional WgOn
argWgOn = CD.arg
  `CD.withName` "on"
  `CD.withDomain` fmap show [(minBound :: WgOn)..]
  `CD.withHelp`  [ "This flag determines which rule have to be strictly oriented by the the matrix interpretation for the weight gap principle. "
                 , "Here 'trs' refers to all strict non-dependency-pair rules of the considered problem, "
                 , "while 'any' only demands any rule at all to be strictly oriented. "
                 , "The default value is 'trs'."]
  `CD.optional` WgOnTrs


args ::
  ( CD.Argument 'CD.Optional WgOn
  , CD.Argument 'CD.Optional Int
  , CD.Argument 'CD.Optional Int
  , CD.Argument 'CD.Optional NMI.NaturalMIKind
  , CD.Argument 'CD.Optional Arg.UsableArgs
  , CD.Argument 'CD.Optional Arg.UsableRules
  , CD.Argument 'CD.Optional (Maybe (RS.ExpressionSelector Prob.F Prob.V))
  , CD.Argument 'CD.Optional Arg.Greedy )
args = let
  (argDim,argDeg,argMIKind,ua,ur,sel,gr)=NMI.args
  in (argWgOn, argDim,argDeg,argMIKind,ua,ur,sel,gr)


description :: [String]
description =  [ "Uses the weight gap principle to shift some strict rules to the weak part of the problem"]

weightGapDeclaration :: CD.Declaration (
  '[ CD.Argument 'CD.Optional WgOn
   , CD.Argument 'CD.Optional Int
   , CD.Argument 'CD.Optional Int
   , CD.Argument 'CD.Optional NMI.NaturalMIKind
   , CD.Argument 'CD.Optional Arg.UsableArgs
   , CD.Argument 'CD.Optional Arg.UsableRules
   , CD.Argument 'CD.Optional (Maybe (RS.ExpressionSelector Prob.F Prob.V))
   , CD.Argument 'CD.Optional Arg.Greedy
  ] CD.:-> CD.Strategy Prob.TrsProblem Prob.TrsProblem)
weightGapDeclaration = CD.declare "weightgap" description args weightGapStrategy

weightGap :: CD.Strategy Prob.TrsProblem Prob.TrsProblem
weightGap = CD.deflFun weightGapDeclaration

weightGap' :: WgOn -> Int -> Int -> NMI.NaturalMIKind -> Arg.UsableArgs -> Arg.UsableRules
               -> Maybe (RS.ExpressionSelector Prob.F Prob.V)
               -> Arg.Greedy
               -> CD.Strategy Prob.TrsProblem Prob.TrsProblem
weightGap' = CD.declFun weightGapDeclaration

instance CD.Processor WeightGap where
  type ProofObject WeightGap = PC.ApplicationProof (PC.OrientationProof WeightGapProof)
  type I WeightGap           = Prob.TrsProblem
  type O WeightGap           = Prob.TrsProblem
  type Forking WeightGap     = CD.Optional CD.Id

  solve p prob
    | Prob.isTrivial prob = return . CD.resultToTree p prob $ CD.Fail PC.Closed
    | otherwise           = entscheide p prob

instance PP.Pretty WeightGapProof where
  pretty (WeightGapProof p growth) =
    case p of
     PC.Order _ -> PP.paragraph ( show $ PP.text "The weightgap principle applies"
                                  PP.<+> PP.parens (PP.text "using the following"
                                                    PP.<+> PP.text intertitle))
                   PP.<$> PP.text ""
                   PP.<$> PP.pretty p
                   PP.<$> PP.text ""
                   PP.<$> PP.text "Further, it can be verified that all rules not oriented are covered by the weightgap condition."
     PC.Incompatible -> PP.text "the weightgap princliple does not apply"
    where
      intertitle = case growth of
        Just False -> "nonconstant growth matrix-interpretation"
        Just True  -> "constant growth matrix-interpretation"
        Nothing    -> "matrix-interpretation"

instance Xml.Xml WeightGapProof where
  toXml (WeightGapProof p growth) = Xml.elt "WeightGap toXml unsupported" []
