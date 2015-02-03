module Tct.Trs.Data.Xml
  (
  -- * Translations to XML for termlib data types         
  ) where


import qualified Data.Rewriting.Term as R
import qualified Data.Rewriting.Rule as R

import Tct.Core.Common.Xml


import           Tct.Trs.Data.Signature (Signature)
import qualified Tct.Trs.Data.Signature as Sig
import           Tct.Trs.Data.Trs (Trs)
import qualified Tct.Trs.Data.Trs as Trs
import           Tct.Trs.Data.Problem (Problem, Strategy (..))
import qualified Tct.Trs.Data.Problem as Prob


{-var :: Xml v => v -> XmlContent-}
{-var v = elt "var" [toXml v]-}

{-instance Xml f => Xml (AFun f) where-}
  {-toXml (TrsFun f) = elt "name" [toXml  f]-}
  {-toXml (DpFun f)  = elt "sharp" [elt "name" [toXml f]]-}
  {-toXml (ComFun f) = elt "name" [text $ 'c':show f]-}

instance (Xml f, Xml v) => Xml (R.Term f v) where
  toXml (R.Fun f ts) = elt "funapp" $ toXml f :  [ elt "arg" [toXml t] | t <- ts ]
  toXml (R.Var v)    = toXml v

instance (Xml f, Xml v) => Xml (R.Rule f v) where
  toXml r = elt "rule" 
    [ elt "lhs" [toXml $ R.lhs r]
    , elt "rhs" [toXml $ R.rhs r] ]

instance (Xml f, Xml v) => Xml (Trs f v) where
  toXml rs = elt "rules" [ toXml r | r <- Trs.toList rs ]

instance Xml f => Xml (Signature f) where
  toXml sig = elt "signature" [ symb f i | (f,i) <- Sig.elems sig ]
    where symb f i = elt "symbol" [ toXml f, elt "arity" [text $ show i] ]

strategy :: Strategy -> XmlContent
strategy Innermost = elt "innermost" []
strategy Outermost = elt "outermost" []
strategy Full      = elt "full" []

startTerms :: (Xml f, Ord f) => Prob.StartTerms f -> Signature f -> XmlContent
startTerms (Prob.AllTerms fs) sig =
  elt "derivationalComplexity" [toXml $ Sig.restrictSignature sig fs]
startTerms (Prob.BasicTerms ds cs) sig =
  elt "runtimeComplexity" $ map toXml [Sig.restrictSignature sig cs, Sig.restrictSignature sig ds]

xmlProblem :: (Ord f, Ord v, Xml f, Xml v) => Problem f v -> XmlContent
xmlProblem prob = elt "problem"
  [ elt "strictTrs"         [toXml (Prob.strictTrs prob)]
  , elt "weakTrs"           [toXml (Prob.strictTrs prob)]
  , elt "strictDPs"         [toXml (Prob.strictTrs prob)]
  , elt "weakDPs"           [toXml (Prob.strictTrs prob)]
  -- ceta compatible
  , elt "trs"               [toXml (Prob.strictComponents prob)]
  , elt "strategy"          [strategy (Prob.strategy prob)]
  , elt "relativeRules"     [toXml (Prob.weakComponents prob)]
  , elt "complexityMeasure" [startTerms (Prob.startTerms prob) (Prob.signature prob)] ]

instance (Ord f, Ord v, Xml f, Xml v) => Xml (Prob.Problem f v) where
  toXml = xmlProblem

