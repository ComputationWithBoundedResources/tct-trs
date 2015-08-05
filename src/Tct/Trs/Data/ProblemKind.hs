-- | This module provides flags for the problem type.
module Tct.Trs.Data.ProblemKind 
  (
    StartTerms (..)
  , isStartTerm
  , mapStartTerms
  , Strategy (..)
  ) where


import           Data.Monoid
import qualified Data.Set               as S

import qualified Data.Rewriting.Term    as R

import qualified Tct.Core.Common.Pretty as PP
import qualified Tct.Core.Common.Xml    as Xml

import           Tct.Trs.Data.Signature (Signature, Symbols, restrictSignature)


-- | Defineds the start terms.
data StartTerms f
  = AllTerms
    { alls         :: Symbols f }
  | BasicTerms
    { defineds     :: Symbols f
    , constructors :: Symbols f }
  deriving (Show, Eq)

-- | Checks wether a given term is a start term.
isStartTerm :: Ord f => StartTerms f -> R.Term f v -> Bool
isStartTerm (AllTerms fs) t = case t of
  (R.Var _)   -> True
  (R.Fun f _) -> f `S.member` fs
isStartTerm (BasicTerms ds cs) t = case t of
  (R.Var _)    -> True
  (R.Fun f ts) -> f `S.member` ds && all (`S.member` cs) (concatMap R.funs ts)


mapStartTerms :: Ord f' => (f -> f') -> StartTerms f -> StartTerms f'
mapStartTerms f (AllTerms fs)      = AllTerms (f `S.map` fs)
mapStartTerms f (BasicTerms ds cs) = BasicTerms (f `S.map` ds) (f `S.map` cs)

-- | Defineds the rewriting Strategy.
data Strategy = Innermost | Outermost | Full deriving (Show, Eq)


--- * proof data -----------------------------------------------------------------------------------------------------

instance PP.Pretty Strategy where
  pretty = PP.text . show

instance (Ord f, PP.Pretty f) => PP.Pretty (StartTerms f) where
  pretty st@AllTerms{}   = PP.text "all terms: " <> PP.set' (alls st)
  pretty st@BasicTerms{} = PP.text "basic terms: " <> PP.set' (defineds st) <> PP.char '/' <> PP.set' (constructors st)

instance Xml.Xml Strategy where
  toXml s = Xml.elt "strategy" $ (:[]) $ case s of
    Innermost -> Xml.elt "innermost" []
    Outermost -> Xml.elt "outermost" []
    Full      -> Xml.elt "full" []
  toCeTA s = case s of
    Innermost -> Xml.elt "strategy" [Xml.elt "innermost" []]
    Outermost -> Xml.elt "strategy" [Xml.elt "outermost" []]
    Full      -> Xml.empty

instance (Xml.Xml f, Ord f) => Xml.Xml (StartTerms f, Signature f) where
  toXml (st,sig) = case st of
    (AllTerms fs)      -> Xml.elt "derivationalComplexity" [Xml.toXml $ restrictSignature sig fs]
    (BasicTerms ds cs) -> Xml.elt "runtimeComplexity" $ map Xml.toXml [restrictSignature sig cs, restrictSignature sig ds]
  toCeTA = Xml.toXml

