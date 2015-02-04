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
import           Tct.Trs.Data.Problem (Strategy (..))
import qualified Tct.Trs.Data.Problem as Prob


instance (Xml f, Xml v) => Xml (R.Term f v) where
  toXml (R.Fun f ts) = elt "funapp" $ toXml f :  [ elt "arg" [toXml t] | t <- ts ]
  toXml (R.Var v)    = toXml v
  toCeTA = toXml

instance (Xml f, Xml v) => Xml (R.Rule f v) where
  toXml r = elt "rule" 
    [ elt "lhs" [toXml $ R.lhs r]
    , elt "rhs" [toXml $ R.rhs r] ]
  toCeTA = toXml

instance (Xml f, Xml v) => Xml (Trs f v) where
  toXml rs = elt "rules" [ toXml r | r <- Trs.toList rs ]
  toCeTA = toXml

instance Xml f => Xml (Signature f) where
  toXml sig = elt "signature" [ symb f i | (f,i) <- Sig.elems sig ]
    where symb f i = elt "symbol" [ toXml f, elt "arity" [text $ show i] ]
  toCeTA = toXml

instance Xml Strategy where
  toXml s = elt "strategy" $ (:[]) $ case s of
    Innermost -> elt "innermost" []
    Outermost -> elt "outermost" []
    Full      -> elt "full" []
  toCeTA s = elt "strategy" $ case s of
    Innermost -> [elt "innermost" []]
    Outermost -> [elt "outermost" []]
    Full      -> []


startTerms :: (Xml f, Ord f) => Prob.StartTerms f -> Signature f -> XmlContent
startTerms (Prob.AllTerms fs) sig =
  elt "derivationalComplexity" [toXml $ Sig.restrictSignature sig fs]
startTerms (Prob.BasicTerms ds cs) sig =
  elt "runtimeComplexity" $ map toXml [Sig.restrictSignature sig cs, Sig.restrictSignature sig ds]

-- MS: the ceta instance is not complete as it contains a tag <complexityClass> which depends on ProofTree
-- furthermore CeTA (2.2) only supports polynomial bounds; so we add the tag manually in the output
instance (Ord f, Ord v, Xml f, Xml v) => Xml (Prob.Problem f v) where
  toXml prob =
    elt "problem"
      [ elt "strictTrs"         [toXml (Prob.strictTrs prob)]
      , elt "weakTrs"           [toXml (Prob.strictTrs prob)]
      , elt "strictDPs"         [toXml (Prob.strictTrs prob)]
      , elt "weakDPs"           [toXml (Prob.strictTrs prob)] ]
  toCeTA prob = 
    elt "complexityInput" 
      [ elt "trsInput" 
          [ elt "trs" [toXml (Prob.strictComponents prob)]
          , toXml (Prob.strategy prob)
          , elt "relativeRules"     [toXml (Prob.weakComponents prob)] ]
      , elt "complexityMeasure" [startTerms (Prob.startTerms prob) (Prob.signature prob)] ]

