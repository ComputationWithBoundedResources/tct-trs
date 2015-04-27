-- | This interface provides common declaration arguments.
module Tct.Trs.Data.Arguments 
  (
  HasSelection (..)

  , HasUsableArgs (..)
  , UsableArgs (..)
  , usableArgs
  , useUsableArgs

  , HasUsableRules (..)
  , UsableRules (..)
  , usableRules
  , useUsableRules

  , HasGreedy (..)
  , Greedy (..)
  , greedy
  , useGreedy

  , HasKind (..)
  ) where


import           Data.Typeable

import qualified Tct.Core.Common.Parser    as P
import qualified Tct.Core.Data             as T

import           Tct.Trs.Data.Problem      (F, V)
import           Tct.Trs.Data.RuleSelector (ExpressionSelector)


class HasSelection p where
  withSelection :: p -> ExpressionSelector F V -> p

data UsableArgs = UArgs | NoUargs
  deriving (Bounded, Enum, Eq, Typeable, Show)

instance T.SParsable prob UsableArgs where
  parseS = P.enum

class HasUsableArgs p where
  withUsableArgs :: p -> UsableArgs -> p

usableArgs :: T.Argument 'T.Required UsableArgs
usableArgs = T.arg
  `T.withName` "uargs"
  `T.withHelp`
    [ "This argument specifies whether usable arguments are computed (if applicable)"
    , "in order to relax the monotonicity constraints on the interpretation."]
  `T.withDomain` fmap show [(minBound :: UsableArgs)..]

useUsableArgs :: UsableArgs -> Bool
useUsableArgs = (UArgs==)

data UsableRules = URules | NoURules
  deriving (Bounded, Enum, Eq, Typeable, Show)

instance T.SParsable prob UsableRules where
  parseS = P.enum

class HasUsableRules p where
  withUsableRules :: p -> UsableRules -> p

usableRules :: T.Argument 'T.Required UsableRules
usableRules = T.arg
  `T.withName` "urules"
  `T.withHelp`
    [ "This argument specifies whether usable rules modulo argument filtering is applied"
    , "in order to decrease the number of rules that have to be orient. "]
  `T.withDomain` fmap show [(minBound :: UsableRules)..]

useUsableRules :: UsableRules -> Bool
useUsableRules = (URules==)

data Greedy = Greedy | NoGreedy
  deriving (Bounded, Enum, Eq, Typeable, Show)

instance T.SParsable prob Greedy where
  parseS = P.enum

class HasGreedy p where
  withGreedy :: p -> Greedy -> p

greedy :: T.Argument 'T.Required Greedy
greedy = T.arg
  `T.withName` "greedy"
  `T.withHelp`
    [ "This argument specifies whether to be greedy." ]
  `T.withDomain` fmap show [(minBound :: UsableRules)..]

useGreedy :: Greedy -> Bool
useGreedy = (Greedy==)

class HasKind p where
  type (Kind p)
  withKind :: p -> Kind p -> p

