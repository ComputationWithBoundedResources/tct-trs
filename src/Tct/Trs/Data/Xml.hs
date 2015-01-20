module Tct.Trs.Data.Xml
  (
  -- * Translations to XML for termlib data types         
  var
  , fun
  , term
  , rule
  , rules
  , rulesL
  , signature
  , startTerms
  , strategy
  {-, complexityProblem-}
  {-, proofDocument-}
  ) where

import qualified Data.Map.Strict as M

import qualified Data.Rewriting.Term as R
import qualified Data.Rewriting.Rule as R

import Tct.Core.Common.Pretty (Pretty, pretty)
import Tct.Core.Common.Xml


import qualified Tct.Trs.Data.Trs as Trs
import           Tct.Trs.Data.Problem (Problem, AFun (..), Strategy (..), Signature, Trs, Rule)
import qualified Tct.Trs.Data.Problem as Prob

pptext :: Pretty a => a -> XmlContent
pptext = text . show . pretty

var :: Pretty v => v -> XmlContent
var v = elt "var" [pptext v]

fun :: Pretty f => AFun f -> XmlContent
fun (TrsFun f) = elt "name" [pptext  f]
fun (DpFun f)  = elt "sharp" [elt "name" [pptext f]]
fun (ComFun f) = elt "name" [text $ 'c':show f] -- TODO

term :: (Pretty f, Pretty v) => R.Term (AFun f) v -> XmlContent
term (R.Fun f ts) = elt "funapp" $ fun f :  [ elt "arg" [term t] | t <- ts ]
term (R.Var v)    = var v

rule :: (Pretty f, Pretty v) => R.Rule (AFun f) v -> XmlContent 
rule r = elt "rule" 
  [ elt "lhs" [term $ R.lhs r]
  , elt "rhs" [term $ R.rhs r] ]

rules :: Trs -> XmlContent
rules rs = elt "rules" [ rule r | r <- Trs.toList rs ]

rulesL :: [Rule] -> XmlContent
rulesL rs = elt "rules" [ rule r | r <- rs ]

signature :: Pretty f => M.Map (AFun f) Int -> XmlContent
signature sig = elt "signature" [ symb f i | (f,i) <- M.toList sig ]
  where symb f i = elt "symbol" [ fun f, elt "arity" [text $ show i] ]

strategy :: Strategy -> XmlContent
strategy Innermost = elt "innermost" []
strategy Outermost = elt "outermost" []
strategy Full      = elt "full" []

startTerms :: Prob.StartTerms -> Signature -> XmlContent
startTerms (Prob.AllTerms fs) sig =
  elt "derivationalComplexity" [signature $ Trs.restrictSignature sig fs]
startTerms (Prob.BasicTerms ds cs) sig =
  elt "runtimeComplexity" $ map signature [Trs.restrictSignature sig cs, Trs.restrictSignature sig ds]

xmlProblem :: Problem -> XmlContent
xmlProblem prob = elt "problem"
  [ elt "strictTrs"         [rules (Prob.strictTrs prob)]
  , elt "weakTrs"           [rules (Prob.strictTrs prob)]
  , elt "strictDPs"         [rules (Prob.strictTrs prob)]
  , elt "weakDPs"           [rules (Prob.strictTrs prob)]
  -- ceta compatible
  , elt "trs"               [rules (Prob.strictComponents prob)]
  , elt "strategy"          [strategy (Prob.strategy prob)]
  , elt "relativeRules"     [rules (Prob.weakComponents prob)]
  , elt "complexityMeasure" [startTerms (Prob.startTerms prob) (Prob.signature prob)] ]

instance Xml Prob.Problem where
  toXml = xmlProblem


