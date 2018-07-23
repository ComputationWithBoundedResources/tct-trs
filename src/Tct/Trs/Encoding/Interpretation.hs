{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Trs.Encoding.Interpretation
  where

import Data.Maybe (fromMaybe)
import           Control.Monad                      (liftM)
import qualified Data.Foldable                      as F
import qualified Data.Map.Strict                    as M
import           Data.Monoid                        ((<>))
import qualified Data.Traversable                   as F

import qualified Data.Rewriting.Rule                as R
import           Data.Rewriting.Term                (Term (..))

import qualified Tct.Core.Data as T
import qualified Tct.Core.Common.Pretty             as PP
import qualified Tct.Core.Common.Xml                as Xml

import           Tct.Common.SMT                     as SMT (zero, (.&&), (.=>), (.>))
import qualified Tct.Common.SMT                     as SMT

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem               as Prob
import qualified Tct.Trs.Data.RuleSelector          as RS
import qualified Tct.Trs.Data.Signature             as Sig
import qualified Tct.Trs.Data.Rules                 as RS
import qualified Tct.Trs.Encoding.ArgumentFiltering as AFEnc
import qualified Tct.Trs.Encoding.UsablePositions   as UPEnc
import qualified Tct.Trs.Encoding.UsableRules       as UREnc


-- | @interpret fun var term@ interprets @term@.
interpretTerm :: (fun -> [a] -> a) -> (var -> a) -> Term fun var -> a
interpretTerm ifun ivar (Fun f ts) = ifun f (interpretTerm ifun ivar `fmap` ts)
interpretTerm _    ivar (Var a)    = ivar a

newtype Interpretation f a = Interpretation { interpretations :: M.Map f a }
  deriving (Show, Functor, F.Foldable, F.Traversable)


instance (SMT.Decode m c a) => SMT.Decode m (Interpretation fun c) (Interpretation fun a) where
  decode (Interpretation m) = Interpretation `liftM` F.traverse SMT.decode m

-- instance (Applicative m, Monad m) => SMT.Decode m (UPEnc.UsablePositions f) (UPEnc.UsablePositions f) where
--   decode = return

instance (PP.Pretty f, PP.Pretty c)  => PP.Pretty (Interpretation f c) where
  pretty pint = PP.table [(PP.AlignRight, as), (PP.AlignLeft, bs), (PP.AlignLeft,cs)]
    where
      (as,bs,cs) = unzip3 $ map k (M.toList $ interpretations pint)
      k (f,p)    = (PP.text "p" <> PP.parens (PP.pretty f), PP.text " = ", PP.pretty p)

-- | Indicates wether strict oriented rules should be shifted to the weak components or wether all strict rules should be oriented strictly.
-- In the latter case the complexity problem is already solved.
-- @All = Just (selAny selStricts)@ but the encoding is cheaper
data Shift = Shift (ExpressionSelector F V) | All
  deriving Show

-- FIXME: MS: clean up proof construction; usable args returns empty if not set instead of all
data InterpretationProof a b = InterpretationProof
  { sig_       :: Signature F
  , inter_     :: Interpretation F a
  , uargs_     :: UPEnc.UsablePositions F
  , ufuns_     :: Maybe (Symbols F)
  , useURules_ :: Bool
  , shift_     :: Shift
  , strictDPs_ :: [(R.Rule F V, (b, b))]
  , strictTrs_ :: [(R.Rule F V, (b, b))]
  , weakDPs_   :: [(R.Rule F V, (b, b))]
  , weakTrs_   :: [(R.Rule F V, (b, b))]
  } deriving Show

instance Monad m => SMT.Decode m (InterpretationProof a b) (InterpretationProof a b) where
  decode = return

-- MS: formally this is not so nice as in tct2; some extra work would be necessary
-- on the other hand we now have an abstract orient function for interpretations
-- see Tct.RS.Method.Poly.NaturalPI for an example
class AbstractInterpretation i where
  type (A i) :: *
  type (B i) :: *
  type (C i) :: *

  encode      :: i -> A i -> SMT.SmtSolverSt Int (B i)

  setMonotone :: i -> B i -> [Int] -> SMT.Formula Int
  setInFilter :: i -> B i -> (Int -> SMT.Formula Int) -> SMT.Formula Int

  interpret   :: i -> Interpretation F (B i) -> R.Term F V -> C i

  addConstant :: i -> C i -> SMT.IExpr Int -> C i
  gte         :: i -> C i -> C i -> SMT.Formula Int

type ForceAny = [R.Rule F V] -> SMT.Formula Int


orient :: AbstractInterpretation i => i
  -> Trs
  -> Interpretation F (A i)
  -> Shift
  -> Bool -- TODO: MS: Use Types
  -> Bool
  -> SMT.SmtSolverSt Int (InterpretationProof () (), Interpretation F (B i), Maybe (UREnc.UsableEncoder F Int))
orient inter prob absi mselector useUP useUR = do
  SMT.setLogic SMT.QF_NIA

  -- encode abstract interpretation
  ebsi <- F.mapM (encode inter) absi

  let
    usablePositions = UPEnc.usableArgsWhereApplicable prob (Prob.isDTProblem prob) useUP
    monotoneConstraints =
      SMT.bigAnd [ setMonotone inter (interpretations ebsi `find` f) is | (f,is)  <- UPEnc.usablePositions usablePositions ]
        where find m f = error ("Interpretation.monotonConstraints: not found:" ++ show f) `fromMaybe` M.lookup f m

  -- encode usable rules modulo argument filtering
  usenc <- if allowUR then Just `liftM` UREnc.usableEncoder prob else return Nothing
  ifenc <- if allowAF then Just `liftM` AFEnc.inFilterEncoder prob else return Nothing

  let
    usable r = case usenc of
      Nothing -> SMT.top
      Just us -> UREnc.usable us r
    inFilter f i = case ifenc of
      Nothing -> SMT.top
      Just af -> AFEnc.inFilter af f i

    usableRulesConstraints
      | allowUR   = UREnc.validUsableRules trs usable inFilter
      | otherwise = SMT.top

    filteringConstraints
      | allowAF   = SMT.bigAnd $ k `M.mapWithKey` interpretations ebsi
      | otherwise = SMT.top
      where k f fi = setInFilter inter fi (inFilter f)

  -- encode strict vars
  strictVarEncoder <- M.fromList `fmap` F.mapM (\r -> SMT.nvarM' >>= \v -> return (r,v)) rules

  let
    find f = error "Interpretation.strictVar: not found" `fromMaybe` M.lookup f strictVarEncoder
    strict = find

    interpretf = interpret inter ebsi
    (.>=.) = gte inter
    (.+.)  = addConstant inter

    wOrderConstraints = SMT.bigAnd [ usable r .=> wOrder r | r <- wrules ]
      where wOrder r = interpretf (R.lhs r) .>=. interpretf (R.rhs r)
    sOrderConstraints = SMT.bigAnd [ usable r .=> sOrder r | r <- srules ]
      where sOrder r = interpretf (R.lhs r) .>=. (interpretf (R.rhs r) .+. strict r)

    forceAny rs
      | null rs   = SMT.bot
      | otherwise = SMT.bigOr [ usable r .&& strict r .> zero | r <- rs ]
    rulesConstraints = forceAny srules .&& forceSel
      where
        forceSel = case mselector of
          All       -> SMT.bigAnd [ usable r .=> strict r .> zero | r <- srules ]
          Shift sel -> orientSelected (RS.rsSelect sel prob)

    orientSelected (RS.SelectDP r)  = strict r .> zero
    orientSelected (RS.SelectTrs r) = strict r .> zero
    orientSelected (RS.BigAnd es)   = SMT.bigAnd (orientSelected `fmap` es)
    orientSelected (RS.BigOr es)    = SMT.bigOr (orientSelected `fmap` es)

  SMT.assert wOrderConstraints
  SMT.assert sOrderConstraints
  SMT.assert rulesConstraints
  SMT.assert monotoneConstraints
  SMT.assert usableRulesConstraints
  SMT.assert filteringConstraints

  return (proof usablePositions, ebsi, usenc)

  where
    trs    = Prob.allComponents prob
    rules  = RS.toList trs
    srules = RS.toList (Prob.strictComponents prob)
    wrules = RS.toList (Prob.weakComponents prob)

    allowUR = useUR && Prob.isRCProblem prob && Prob.isInnermostProblem prob
    allowAF = allowUR

    proof uposs = InterpretationProof
      { sig_       = Prob.signature prob
      , inter_     = Interpretation M.empty
      , uargs_     = uposs
      , ufuns_     = Nothing
      , useURules_ = allowUR
      , shift_     = mselector
      , strictDPs_ = []
      , strictTrs_ = []
      , weakDPs_   = []
      , weakTrs_   = [] }

-- toTree :: (T.Processor p, T.In p ~ T.Out p) => p -> T.In p -> T.Result p -> T.ProofTree (T.Out p)
-- toTree p prob (T.Fail po)                 = T.NoProgress (T.ProofNode p prob po) (T.Open prob)
-- toTree p prob (T.Success probs po certfn) = T.Progress (T.ProofNode p prob po) certfn (T.Open `fmap` probs)


newProblem :: Trs -> InterpretationProof a b -> T.Optional T.Id Trs
newProblem prob proof = case shift_ proof of
  All     -> T.Null
  Shift _ -> T.Opt . T.Id $ newProblem' prob proof

newProblem' :: Problem F V -> InterpretationProof a b -> Problem F V
newProblem' prob proof = Prob.sanitiseDPGraph $  prob
    { Prob.strictDPs = Prob.strictDPs prob `RS.difference` sDPs
    , Prob.strictTrs = Prob.strictTrs prob `RS.difference` sTrs
    , Prob.weakDPs   = Prob.weakDPs prob `RS.union` sDPs
    , Prob.weakTrs   = Prob.weakTrs prob `RS.union` sTrs }
  where
    rules = RS.fromList . fst . unzip
    sDPs = rules (strictDPs_ proof)
    sTrs = rules (strictTrs_ proof)


instance (PP.Pretty a, PP.Pretty b) => PP.Pretty (InterpretationProof a b) where
  pretty proof = PP.vcat
    [ if uargs_ proof /= UPEnc.fullWithSignature (sig_ proof)
        then PP.vcat
          [ PP.text "The following argument positions are considered usable:"
          , PP.indent 2 $ PP.pretty (uargs_ proof)
          , PP.empty ]
        else PP.empty
    , PP.text "Following symbols are considered usable:"
    , PP.indent 2 $ maybe (PP.text "all") PP.set' (ufuns_ proof)
    , PP.text "TcT has computed the following interpretation:"
    , PP.indent 2 (PP.pretty (inter_ proof))
    , PP.empty
    , PP.text "Following rules are strictly oriented:"
    , ppproof (PP.text " > ") (strictDPs_ proof ++ strictTrs_ proof)
    , PP.text ""
    , PP.text "Following rules are (at-least) weakly oriented:"
    , ppproof (PP.text " >= ") (weakDPs_ proof ++ weakTrs_ proof) ]
    where
      ppproof ppOrd rs = PP.table [(PP.AlignRight, as), (PP.AlignLeft, bs), (PP.AlignLeft, cs)]
        where
          (as,bs,cs) = unzip3 $ concatMap ppRule rs
          ppRule (R.Rule l r,(lhs,rhs)) =
            [ (PP.pretty l, PP.text " = ", PP.pretty lhs)
            , (PP.empty   , ppOrd        , PP.pretty rhs)
            , (PP.empty   , PP.text " = ", PP.pretty r)
            , (PP.empty   , PP.empty     , PP.empty) ]


xmlProof :: Xml.Xml a => InterpretationProof a b -> Xml.XmlContent -> Xml.XmlContent
xmlProof proof itype =
  Xml.elt "ruleShifting"
    [ orderingConstraintProof
    , Xml.elt "trs" [Xml.toXml $ RS.fromList trs]          -- strict part
    -- ceta complains if usableRules are set for non-innermost; even if all rules are given
    , if useURules_ proof
        then Xml.elt "usableRules" [Xml.toXml $ RS.fromList usr] -- usable part
        else Xml.empty
    -- akin to tct2 we allow interpretations to be the base case of our proof
    -- though ceTA requires to use ruleShifting; in this case we append the proof for the empty problem
    , case shift_ proof of
        -- Tct.Core.Processor.Empty.toXml Emptyproblem == </closed>, but toXml is not used in practice
        All     -> Xml.elt "complexityProof" [Xml.elt "rIsEmpty" []]
        Shift _ -> Xml.empty
    ]
    where
      orderingConstraintProof =
        Xml.elt "orderingConstraintProof"
          [ Xml.elt "redPair" [Xml.elt "interpretation" (itype :xinters)]]
      xinters = map xinter . M.toList . interpretations $ inter_ proof
      xinter (f,p) = Xml.elt "interpret"
        [ Xml.toXml f
        , Xml.elt "arity" [Xml.int $ sig_ proof `Sig.arity` f]
        , Xml.toXml p ]
        -- , Xml.elt "polynomial" [Xml.toXml p]]
      trs = map fst $ strictTrs_ proof ++ strictDPs_ proof
      usr = (trs ++) . map fst $ weakTrs_ proof ++ weakDPs_ proof

