-- | This interface provides common arguments.
module Tct.Trs.Data.Arguments
  (
  HasSelection (..)

  -- * Usable Arguments
  , HasUsableArgs (..)
  , UsableArgs (..)
  , usableArgs
  , useUsableArgs

  -- * Usable Rules
  , HasUsableRules (..)
  , UsableRules (..)
  , usableRules
  , useUsableRules

  -- * Restrict
  , Restrict (..)
  , restrict
  , useRestrict

  -- * Kind
  , HasKind (..)
  ) where


import qualified Tct.Core.Data             as T

import           Tct.Trs.Data


class HasSelection p where
  withSelection :: p -> ExpressionSelector F V -> p

data UsableArgs = UArgs | NoUArgs
  deriving (Bounded, Enum, Eq, Show)

class HasUsableArgs p where
  withUsableArgs :: p -> UsableArgs -> p

usableArgs :: T.Argument 'T.Required UsableArgs
usableArgs = T.flag "uargs"
    [ "This argument specifies whether usable arguments are computed (if applicable)"
    , "in order to relax the monotonicity constraints on the interpretation."]

useUsableArgs :: UsableArgs -> Bool
useUsableArgs = (UArgs==)


data UsableRules = URules | NoURules
  deriving (Bounded, Enum, Eq, Show)

class HasUsableRules p where
  withUsableRules :: p -> UsableRules -> p

usableRules :: T.Argument 'T.Required UsableRules
usableRules = T.flag "urules"
    [ "This argument specifies whether usable rules modulo argument filtering is applied"
    , "in order to decrease the number of rules that have to be orient. "]

useUsableRules :: UsableRules -> Bool
useUsableRules = (URules==)


data Restrict = Restrict | NoRestrict
  deriving (Bounded, Enum, Eq, Show)

restrict :: T.Argument 'T.Required Restrict
restrict = T.flag "restrict"
    [ "This argument specifies whether the abstract interpretation of non-start coefficients should be restricted." ]

useRestrict :: Restrict -> Bool
useRestrict = (Restrict==)


class HasKind p where
  type (Kind p)
  withKind :: p -> Kind p -> p

