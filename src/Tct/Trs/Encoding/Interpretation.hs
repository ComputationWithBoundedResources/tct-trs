{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Trs.Encoding.Interpretation
  where


import Data.Maybe (fromMaybe)
import qualified Data.Set as S (empty)
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

import           Tct.Common.SMT                     as SMT (zero, (.&&), (.==>), (.>))
import qualified Tct.Common.SMT                     as SMT

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem               as Prob
import qualified Tct.Trs.Data.RuleSelector          as RS
import qualified Tct.Trs.Data.Signature             as Sig
import qualified Tct.Trs.Data.Trs                   as Trs
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
data Shift = Shift (ExpressionSelector F V) | All
  deriving Show

data InterpretationProof a b = InterpretationProof
  { sig_       :: Signature F
  , inter_     :: Interpretation F a
  , uargs_     :: UPEnc.UsablePositions F
  , ufuns_     :: Symbols F
  , shift_     :: Shift
  , strictDPs_ :: [(R.Rule F V, (b, b))]
  , strictTrs_ :: [(R.Rule F V, (b, b))]
  , weakDPs_   :: [(R.Rule F V, (b, b))]
  , weakTrs_   :: [(R.Rule F V, (b, b))]
  } deriving Show

-- MS: formally this is not so nice as in tct2; some extra work would be necessary
-- on the other hand we now have an abstract orient function for interpretations
-- see Tct.Trs.Method.Poly.NaturalPI for an example
class AbstractInterpretation i where
  type (A i) :: *
  type (B i) :: *
  type (C i) :: *

  encode      :: i -> A i -> SMT.SolverStM SMT.Expr (B i)

  setMonotone :: i -> B i -> [Int] -> SMT.Expr
  setInFilter :: i -> B i -> (Int -> SMT.Expr) -> SMT.Expr

  interpret   :: i -> Interpretation F (B i) -> R.Term F V -> C i

  addConstant :: i -> C i -> SMT.IExpr -> C i
  gte         :: i -> C i -> C i -> SMT.Expr

type ForceAny = [R.Rule F V] -> SMT.Expr

orient :: AbstractInterpretation i => i
  -> TrsProblem
  -> Interpretation F (A i)
  -> Shift
  -> Bool -- TODO: MS: Use Types
  -> Bool
  -> SMT.SolverStM SMT.Expr (InterpretationProof a b , (Interpretation F (B i), Maybe (UREnc.UsableEncoder F)), ForceAny)
orient inter prob absi mselector useUP useUR = do
  SMT.setFormat "QF_NIA"

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

    wOrderConstraints = SMT.bigAnd [ usable r .==> wOrder r | r <- wrules ]
      where wOrder r = interpretf (R.lhs r) .>=. interpretf (R.rhs r)
    sOrderConstraints = SMT.bigAnd [ usable r .==> sOrder r | r <- srules ]
      where sOrder r = interpretf (R.lhs r) .>=. (interpretf (R.rhs r) .+. strict r)

    -- MS: TODO: the greedy component should work on the expression selector; so we could express eg selAnyOf $ selRules `inter` selStricts 
    forceAny rs
      | null rs   = SMT.bot
      | otherwise = SMT.bigOr [ usable r .&& strict r .> zero | r <- rs ]
    rulesConstraints = forceAny srules .&& forceSel
      where
        forceSel = case mselector of
          All       -> SMT.bigAnd [ usable r .==> strict r .> zero | r <- srules ]
          Shift sel -> orientSelected (RS.rsSelect sel prob)

    orientSelected (Trs.SelectDP r)  = strict r .> zero
    orientSelected (Trs.SelectTrs r) = strict r .> zero
    orientSelected (Trs.BigAnd es)   = SMT.bigAnd (orientSelected `fmap` es)
    orientSelected (Trs.BigOr es)    = SMT.bigOr (orientSelected `fmap` es)

  SMT.assert wOrderConstraints
  SMT.assert sOrderConstraints
  SMT.assert rulesConstraints
  SMT.assert monotoneConstraints
  SMT.assert usableRulesConstraints
  SMT.assert filteringConstraints

  return (proof usablePositions, (ebsi, usenc), forceAny)

  where
    trs    = Prob.allComponents prob
    rules  = Trs.toList trs
    srules = Trs.toList (Prob.strictComponents prob)
    wrules = Trs.toList (Prob.weakComponents prob)

    allowUR = useUR && Prob.isRCProblem prob && Prob.isInnermostProblem prob
    allowAF = allowUR

    proof uposs = InterpretationProof 
      { sig_       = Prob.signature prob
      , inter_     = Interpretation M.empty
      , uargs_     = uposs
      , ufuns_     = S.empty
      , shift_     = mselector
      , strictDPs_ = []
      , strictTrs_ = []
      , weakDPs_   = []
      , weakTrs_   = [] }

toTree :: (T.Processor p, T.I p ~ T.O p) => p -> T.I p -> T.Result p -> T.ProofTree (T.O p)
toTree p prob (T.Fail po)                 = T.NoProgress (T.ProofNode p prob po) (T.Open prob)
toTree p prob (T.Success probs po certfn) = T.Progress (T.ProofNode p prob po) certfn (T.Open `fmap` probs)

newProblem :: TrsProblem -> InterpretationProof a b -> T.Optional T.Id TrsProblem
newProblem prob proof = case shift_ proof of
  All     -> T.Null
  Shift _ -> T.Opt . T.Id . Prob.sanitiseDPGraph $  prob
    { Prob.strictDPs = Prob.strictDPs prob `Trs.difference` sDPs
    , Prob.strictTrs = Prob.strictTrs prob `Trs.difference` sTrs
    , Prob.weakDPs   = Prob.weakDPs prob `Trs.union` sDPs
    , Prob.weakTrs   = Prob.weakTrs prob `Trs.union` sTrs }
  where
    rules = Trs.fromList . fst . unzip
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
    , PP.indent 2 $ PP.set' (ufuns_ proof)
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

prettyProof :: (PP.Pretty a, PP.Pretty b) => InterpretationProof a b -> PP.Doc
prettyProof proof = PP.vcat
  [ if uargs_ proof /= UPEnc.fullWithSignature (sig_ proof)
      then PP.vcat
        [ PP.text "The following argument positions are considered usable:"
        , PP.indent 2 $ PP.pretty (uargs_ proof)
        , PP.empty ]
      else PP.empty
  , PP.text "Following symbols are considered usable:"
  , PP.indent 2 $ PP.set' (ufuns_ proof)
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
    , Xml.elt "trs" [Xml.toXml $ Trs.fromList trs]          -- strict part
    , Xml.elt "usableRules" [Xml.toXml $ Trs.fromList usr]] -- usable part
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


