module Tct.Trs.Data.Xml
  (
  -- * Translations to XML for termlib data types         
  var
  , fun
  , term
  , rule
  , rules
  , signature
  , startTerms
  , strategy
  {-, complexityProblem-}
  {-, proofDocument-}
  ) where

import qualified Data.Map.Strict as M

import qualified Data.Rewriting.Term as R
import qualified Data.Rewriting.Rule as R

import Tct.Core.Common.Xml


import Tct.Trs.Data.Trs
import qualified Tct.Trs.Data.Problem as Prob

var :: Show v => v -> XmlContent
var v = elt "var" [text $ show v]

fun :: Show f => AFun f -> XmlContent
fun (TrsFun f) = elt "name" [text $ show f]
fun (DpFun f)  = elt "sharp" [elt "name" [text $ show f]]
fun (ComFun f) = elt "comm" [elt "name" [text $ show f]] -- TODO

term :: (Show f, Show v) => R.Term (AFun f) v -> XmlContent
term (R.Fun f ts) = elt "funapp" $ fun f :  [ elt "arg" [term t] | t <- ts ]
term (R.Var v)    = var v

rule :: (Show f, Show v) => R.Rule (AFun f) v -> XmlContent 
rule r = elt "rule" 
  [ elt "lhs" [term $ R.lhs r]
  , elt "rhs" [term $ R.rhs r] ]

rules :: Trs -> XmlContent
rules rs = elt "rules" [ rule r | r <- ruleList rs ]

signature :: Show f => M.Map (AFun f) Int -> XmlContent
signature sig = elt "signature" [ symb f i | (f,i) <- M.toList sig ]
  where symb f i = elt "symbol" [ fun f, elt "arity" [text $ show i] ]

strategy :: Prob.Strategy -> XmlContent
strategy Prob.Innermost = elt "innermost" []
strategy Prob.Outermost = elt "outermost" []
strategy Prob.Full      = elt "full" []

startTerms :: Prob.StartTerms -> Signature -> XmlContent
startTerms (Prob.AllTerms fs) sig =
  elt "derivationalComplexity" [signature $ restrictSignature sig fs]
startTerms (Prob.BasicTerms ds cs) sig =
  elt "runtimeComplexity" $ map signature [restrictSignature sig cs, restrictSignature sig ds]

  
{-complexityProblem :: Prob.Problem -> Proof.Answer -> XmlContent-}
{-complexityProblem prob ans = -}
  {-elt "complexityInput" [] [ elt "relation" [] $ -}
                             {-concat [ trs "strictTrs" Prob.strictTrs-}
                                    {-, trs "weakTrs" Prob.weakTrs-}
                                    {-, trs "strictDPs" Prob.strictDPs-}
                                    {-, trs "weakDPs" Prob.weakDPs]-}
                           {-, elt "complexityMeasure" [] [startTerms (Prob.startTerms prob) sig]-}
                           {-, elt "strategy" [] [strategy $ Prob.strategy prob]-}
                           {-, elt "answer" [] [answer ans]]-}
    {-where trs n f = -}
            {-case f prob of -}
              {-rs | Trs.isEmpty rs -> []-}
                 {-| otherwise -> [elt n [] [ rules rs sig vs ]]-}
          {-sig = Prob.signature prob-}
          {-vs  = Prob.variables prob-}

          
{-proofDocument :: Proof.ComplexityProof proof => Prob.Problem -> [(R.Rule, Bool)] -> proof -> Proof.Answer -> XmlDocument-}
{-proofDocument prob rulelist proof ans = -}
    {-toDocument $ elt "tctOutput" attribs [inpt, Proof.toXml proof, vers ]-}
        {-where-}
          {-attribs = []-}
          {-inpt = elt "input" [] [ elt "trs" [] [elt "rules" [] [ rule r Nothing sig vs | (r,False) <- rulelist ]]-}
                                {-, elt "strategy" [] [strategy $ Prob.strategy prob]                                              -}
                                {-, elt "relativeRules" [] [ elt "rules" [] [rule r Nothing sig vs | (r,True) <- rulelist ]]-}
                                {-, elt "complexityMeasure" [] [startTerms (Prob.startTerms prob) sig]-}
                                {-, elt "answer" [] [answer ans]]-}
          {-vers = elt "version" [] [text $ version]-}
          {-vs = Prob.variables prob-}
          {-sig = Prob.signature prob-}
               
  {--- Xml.Document prolog symtab el misc-}
  {---   where prolog = Xml.Prolog (Just xmlversion) [Xml.PI ("xml-stylesheet", style)] Nothing []-}
  {---           where xmlversion = Xml.XMLDecl "1.0" Nothing Nothing-}
  {---                 style = "type=\"text/xsl\" href=\"tctpfHTML.xsl\""-}
  {---         el = Xml.Elem (Xml.N "tctOutput") attribs [inpt, Proof.toXml proof, version ]-}
  {---           where attribs = [ (Xml.N "xmlns:xsi", Xml.AttValue [Left "http://www.w3.org/2001/XMLSchema-instance"])-}
  {---                           -- , (Xml.N "xsi", Xml.AttValue [Left "http://cl-informatik.uibk.ac.at/software/tct/include/tctpf.xsd"])-}
  {---                           ]-}
  {---                 inpt     = -}
  {---                 version  = elt "version" [] [text $ Version.version]-}
                  
  {---         misc = []-}
  {---         symtab = []-}

xmlProblem :: Prob.Problem -> XmlContent
xmlProblem prob = elt "problem"
  [ elt "strictTrs"         [rules (Prob.strictTrs prob)]
  , elt "weakTrs"           [rules (Prob.strictTrs prob)]
  , elt "strictDPs"         [rules (Prob.strictTrs prob)]
  , elt "weakDPs"           [rules (Prob.strictTrs prob)]
  -- ceta compatible
  , elt "trs"               [rules (Prob.allComponents prob)]
  , elt "strategy"          [strategy (Prob.strategy prob)]
  , elt "relativeRules"     [rules (Prob.weakComponents prob)]
  , elt "complexityMeasure" [startTerms (Prob.startTerms prob) (Prob.signature prob)] ]

instance Xml Prob.Problem where
  toXml = xmlProblem


