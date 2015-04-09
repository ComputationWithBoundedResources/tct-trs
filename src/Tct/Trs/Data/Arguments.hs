-- | This interface provides common declaration arguments.
module Tct.Trs.Data.Arguments where

import qualified Tct.Core.Data             as T

import           Tct.Trs.Data.Problem      (F, V)
import           Tct.Trs.Data.RuleSelector (ExpressionSelector)

class HasSelection p where
  withSelection :: p -> ExpressionSelector F V -> p

uaArg :: T.Argument 'T.Required Bool
uaArg = T.bool 
  `T.withName` "uargs"
  `T.withHelp` 
    [ "This argument specifies whether usable arguments are computed (if applicable)"
    , "in order to relax the monotonicity constraints on the interpretation."]

urArg :: T.Argument 'T.Required Bool
urArg = T.bool
  `T.withName` "urules"
  `T.withHelp`
    [ "This argument specifies whether usable rules modulo argument filtering is applied"
    , "in order to decrease the number of rules that have to be orient. "]


