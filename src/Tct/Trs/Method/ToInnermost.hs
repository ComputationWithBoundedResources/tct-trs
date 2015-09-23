{-|
This module provides the /To Innermost/ Processor.

Masahiko Sakai , Kouji Okamoto , Toshiki Sakabe, 2003: "Innermost reductions find all normal forms on right-linear terminating overlay TRSs"

-}

module Tct.Trs.Method.ToInnermost
  ( toInnermost
  , toInnermostDeclaration
) where

import           Control.Applicative          ((<|>))

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators (ApplicationProof(..))
import           Tct.Trs.Data                (TrsProblem, TrsStrategy)

import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.Trs             as Trs


data ToInnermost = ToInnermost deriving Show

data ToInnermostProof
  =   ToInnermostSuccess
    | IsAlreadyInnermost
    deriving Show

-- the processor fails if the problem was already innermost, i.e., no
-- progress is to be expected the processor is inapplicable, iff the
-- trs is not rightlinear, not overlay or contains weak components
instance T.Processor ToInnermost where
  type ProofObject ToInnermost = ApplicationProof ToInnermostProof
  type I ToInnermost           = TrsProblem
  type O ToInnermost           = TrsProblem
  solve p prob = return . T.resultToTree p prob $
    maybe ti (T.Fail . Inapplicable) maybeApplicable
    where
       ti
          -- no progress if prob is already innermost
          | Prob.isInnermostProblem prob = T.Fail (Applicable IsAlreadyInnermost)
          | otherwise                    = T.Success (T.toId (Prob.toInnermost prob)) (Applicable ToInnermostSuccess) T.fromId
       maybeApplicable =
         Trs.isRightLinear' (Prob.allComponents prob)
         <|>
         Trs.isOverlay' (Prob.allComponents prob)
         <|>
         Prob.noWeakComponents' prob


-- * instances
-------------------------------------------------------------------

description :: [String]
description =
  ["Switches to innermost rewriting for overlay and right linear input."]

toInnermostDeclaration :: T.Declaration ('[] T.:-> TrsStrategy)
toInnermostDeclaration = T.declare "toInnermost" description () (T.Proc ToInnermost)

toInnermost :: TrsStrategy
toInnermost = T.declFun toInnermostDeclaration

-- * proof data
-------------------------------------------------------------------

instance PP.Pretty ToInnermostProof where
  pretty ToInnermostSuccess = PP.text "switch to innermost, as the system is overlay and right linear and does not contain weak rules"
  pretty IsAlreadyInnermost = PP.text "the problem is already innermost"

instance Xml.Xml ToInnermostProof where
  toXml _ = Xml.elt "toInnermost" []
