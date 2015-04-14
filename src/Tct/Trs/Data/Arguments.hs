-- | This interface provides common declaration arguments.
module Tct.Trs.Data.Arguments where


import           Data.Typeable

import qualified Tct.Core.Common.Parser    as P
import qualified Tct.Core.Data             as T

import           Tct.Trs.Data.Problem      (F, V)
import           Tct.Trs.Data.RuleSelector (ExpressionSelector)


class HasSelection p where
  withSelection :: p -> ExpressionSelector F V -> p

data UsableArgs = UArgs | NoUargs
  deriving (Bounded, Enum, Eq, Typeable)

instance Show UsableArgs where
  show UArgs   = "uargs"
  show NoUargs = "nouargs"

instance T.SParsable prob UsableArgs where
  parseS = P.enum

class HasUsableArgs p where
  withUsableArgs :: p -> UsableArgs -> p

data UsableRules = URules | NoURules
  deriving (Bounded, Enum, Eq, Typeable)

instance Show UsableRules where
  show URules   = "urules"
  show NoURules = "nourules"

instance T.SParsable prob UsableRules where
  parseS = P.enum

class HasUsableRules p where
  withUsableRules :: p -> UsableRules -> p

-- uaArg :: T.Argument 'T.Required UsableArgs
-- uaArg = T.arg
--   `T.withName` "uargs"
--   `T.withHelp`
--     [ "This argument specifies whether usable arguments are computed (if applicable)"
--     , "in order to relax the monotonicity constraints on the interpretation."]
--   `T.withDomain` fmap show [(minBound :: UsableArgs)..]
--
-- urArg :: T.Argument 'T.Required UsableRules
-- urArg = T.arg
--   `T.withName` "urules"
--   `T.withHelp`
--     [ "This argument specifies whether usable rules modulo argument filtering is applied"
--     , "in order to decrease the number of rules that have to be orient. "]
--   `T.withDomain` fmap show [(minBound :: UsableRules)..]

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

