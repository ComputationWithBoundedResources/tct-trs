{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Method.DP.UsableRules
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module provides the usable rules transformation.
--------------------------------------------------------------------------------   

module Tct.Method.DP.UsableRules 
       (
         usableRules 
         -- * Proof Object
       , URProof (..)
         -- * Processor
       , usableRulesProcessor
       , UR
         -- * Utilities 
       , mkUsableRules
       )
       where

import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ hiding (empty)

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Variable as V
import qualified Termlib.Problem as Prob
import qualified Termlib.Term as Term
import qualified Termlib.Rule as R
import Termlib.Rule (Rule (..))
import qualified Termlib.Trs as Trs
import Termlib.Trs (Trs)
import Termlib.Trs.PrettyPrint (pprintNamedTrs)
import Termlib.Utils hiding (block)
import qualified Tct.Utils.Xml as Xml
import qualified Tct.Utils.Xml.Encoding as XmlE

import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args as A
import Tct.Utils.Enum (enumeration')
import Tct.Utils.PPrint
import Tct.Method.DP.Utils 

-- | The Trs 'mkUsableRules prob trs' contains
-- all rules of 'trs' which are usable by 'prob'.
mkUsableRules :: Prob.Problem -> Trs -> Trs
mkUsableRules prob trs = trs `restrictTo` Set.unions [decendants f | f <- ds
                                                                   , Rule _ r <- Trs.rules $ Prob.dpComponents prob
                                                                   , f `Set.member` Term.functionSymbols r ]
  where trs' `restrictTo` roots = Trs.fromRules [ rule | rule <- Trs.rules trs', let Right f = Term.root (R.lhs rule) in f `Set.member` roots ]
        decendants f = reachable step [f] Set.empty
          where step f' = Set.fromList [ g | g <- ds
                                           , Rule l r <- Trs.rules trss
                                           , Term.root l == Right f'
                                           , g `Set.member` Term.functionSymbols r ]
        reachable _     []     visited                          = visited
        reachable nexts (f:fs) visited | f `Set.member` visited = reachable nexts fs visited
                                       | otherwise              = reachable nexts (fs' ++ fs) (Set.insert f visited)
                                            where fs' = Set.toList $ nexts f
                                                  
        ds = Set.toList $ Trs.definedSymbols trss
        trss = Prob.trsComponents prob


data UR = UR

data URProof = URProof { usableStrict :: Trs -- ^ Usable strict rules
                       , usableWeak   :: Trs -- ^ Usable weak rules
                       , signature    :: F.Signature
                       , variables    :: V.Variables
                       , progressed   :: Bool -- ^ This flag is 'True' iff some rules are not usable
                       }
               | Error DPError

instance PrettyPrintable URProof where 
  pprint p@URProof {} 
    | prog && null allUrs = text "No rule is usable, rules are removed from the input problem."
    | prog = 
        paragraph "We replace rewrite rules by usable rules:"
        $+$ text ""
        $+$ indent (ppTrs "Strict Usable Rules" (usableStrict p)
                    $+$ ppTrs "Weak Usable Rules" (usableWeak p))
    | otherwise       = text "All rules are usable."
        where ppTrs  = pprintNamedTrs (signature p) (variables p)
              allUrs = Trs.rules (usableStrict p) ++ Trs.rules (usableWeak p)
              prog = progressed p
  pprint (Error e)                    = pprint e

instance T.TransformationProof UR where
    answer = T.answerFromSubProof
    pprintTProof _ _ p _ = pprint p
    tproofToXml _ _ (Error e) = ("usableRules", [errorToXml e])
    tproofToXml _ _ p = 
        ("usablerules", 
         [
          Xml.elt "strict" [] [XmlE.rules (usableStrict p) sig vs]
          , Xml.elt "weak" [] [XmlE.rules (usableWeak p) sig vs]
         ])
            where 
              sig = signature p
              vs = variables p
instance T.Transformer UR where 
    name UR = "usablerules"
    description UR = [ "This processor restricts the strict- and weak-rules to usable rules with"
                     , "respect to the dependency pairs."]
    type ArgumentsOf UR = Unit
    type ProofOf UR = URProof 
    arguments UR = Unit
    transform _ prob | not (Prob.isDPProblem prob) = return $ T.NoProgress $ Error NonDPProblemGiven
                     | otherwise                 = return $ res
        where res | progr     = T.Progress ursproof (enumeration' [prob'])
                  | otherwise = T.NoProgress ursproof
              strs = Prob.strictTrs prob
              wtrs = Prob.weakTrs prob
              surs = mkUsableRules prob strs
              wurs = mkUsableRules prob wtrs
              progr = size wurs < size wtrs || size surs < size strs
                  where size = length . Trs.rules
              ursproof = URProof { usableStrict = surs
                                 , usableWeak  = wurs
                                 , signature   = Prob.signature prob
                                 , variables   = Prob.variables prob
                                 , progressed  = progr }
              prob' = prob { Prob.strictTrs = surs
                           , Prob.weakTrs   = wurs }


usableRulesProcessor :: T.Transformation UR P.AnyProcessor
usableRulesProcessor = T.Transformation UR

usableRules :: T.TheTransformer UR
usableRules = T.Transformation UR `T.withArgs` ()
