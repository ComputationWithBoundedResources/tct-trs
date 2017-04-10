-- | This module provides the type function symbols and variables.
module Tct.Trs.Data.Symbol
  ( Fun (..)
  , AFun (..)
  , F , fun
  , V , var
  , unF, unV
  ) where


import qualified Data.ByteString.Char8  as BS

import qualified Tct.Core.Common.Pretty as PP
import qualified Tct.Core.Common.Xml    as Xml


-- | Abstract function interface.
class Fun f where
  markFun       :: f -> f
  compoundFun   :: Int -> f
  isMarkedFun   :: f -> Bool
  isCompoundFun :: f -> Bool


--- * instance -------------------------------------------------------------------------------------------------------

-- | Annotated function symbol.
data AFun f
  = TrsFun f
  | DpFun f
  | ComFun Int
  deriving (Eq, Ord, Show)

newtype F = F (AFun BS.ByteString)
  deriving (Eq, Ord, Show)

fun  :: String -> F
fun = F . TrsFun . BS.pack

newtype V = V BS.ByteString
  deriving (Eq, Ord, Show)

var  :: String -> V
var = V . BS.pack

instance Fun F where
  markFun (F (TrsFun f))       = F (DpFun f)
  markFun _                    = error "Tct.Trs.Data.Problem.markFun: not a trs symbol"

  compoundFun                  = F . ComFun

  isMarkedFun (F (DpFun _)) = True
  isMarkedFun _             = False

  isCompoundFun (F (ComFun _)) = True
  isCompoundFun _              = False

-- Hack to get amortised running. FIXME: need to optimize amortised analysis to not
-- use strings, but rather F, V, ...
unF :: F -> String
unF (F (TrsFun bs)) = BS.unpack bs

unV :: V -> String
unV (V bs) = BS.unpack bs


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty V where
  pretty (V v) = PP.text (BS.unpack v)

instance Xml.Xml V where
  toXml (V v) = Xml.elt "var" [Xml.text (BS.unpack v)]
  toCeTA      = Xml.toXml

-- instance PP.Pretty BS.ByteString where
--   pretty = PP.text . BS.unpack

-- instance Xml.Xml BS.ByteString where
--   toXml  = Xml.text . BS.unpack
--   toCeTA = Xml.text . BS.unpack

instance PP.Pretty F where
  pretty (F (TrsFun f)) = PP.text (BS.unpack f)
  pretty (F (DpFun f))  = PP.text (BS.unpack f) PP.<> PP.char '#'
  pretty (F (ComFun i)) = PP.pretty "c_" PP.<> PP.int i

instance Xml.Xml F where
  toXml (F (TrsFun f)) = Xml.elt "name" [Xml.text $ BS.unpack  f]
  toXml (F (DpFun f))  = Xml.elt "sharp" [Xml.elt "name" [Xml.text $ BS.unpack f]]
  toXml (F (ComFun f)) = Xml.elt "name" [Xml.text $ 'c':show f]
  toCeTA = Xml.toXml

