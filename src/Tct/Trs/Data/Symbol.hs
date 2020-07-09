-- | This module provides the type function symbols and variables.
module Tct.Trs.Data.Symbol
  ( Fun(..)
  , AFun(..)
  , F
  , fun
  , V
  , var
  , mainFunction
  )
where


import qualified Data.ByteString.Char8         as BS

import qualified Tct.Core.Common.Pretty        as PP
import qualified Tct.Core.Common.Xml           as Xml

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
  deriving (Eq, Ord, Show, Read)

newtype F = F (AFun BS.ByteString)
  deriving (Eq, Ord, Show, Read)

fun :: String -> F
fun = F . TrsFun . BS.pack

mainFunction :: F
mainFunction = fun "main"

newtype V = V BS.ByteString
  deriving (Eq, Ord)

instance Show V where
  show (V x) = show x

var :: String -> V
var = V . BS.pack

instance Read V where
  readsPrec _ str =
    let str' = filter (/= '"') str
        x    = BS.pack $ if take 2 str' == "V " then drop 2 str' else str'
    in  [(V x, [])]

instance Fun F where
  markFun (F (TrsFun f)) = F (DpFun f)
  markFun _ = error "Tct.Trs.Data.Problem.markFun: not a trs symbol"

  compoundFun = F . ComFun

  isMarkedFun (F (DpFun _)) = True
  isMarkedFun _             = False

  isCompoundFun (F (ComFun _)) = True
  isCompoundFun _              = False


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty V where
  pretty (V v) = PP.text (BS.unpack v)

instance Xml.Xml V where
  toXml (V v) = Xml.elt "var" [Xml.text (BS.unpack v)]
  toCeTA = Xml.toXml

-- instance PP.Pretty BS.ByteString where
--   pretty = PP.text . BS.unpack

-- instance Xml.Xml BS.ByteString where
--   toXml  = Xml.text . BS.unpack
--   toCeTA = Xml.text . BS.unpack

instance PP.Pretty F where
  pretty (F (TrsFun f)) = PP.text (BS.unpack f)
  pretty (F (DpFun  f)) = PP.text (BS.unpack f) PP.<> PP.char '#'
  pretty (F (ComFun i)) = PP.pretty "c_" PP.<> PP.int i

instance Xml.Xml F where
  toXml (F (TrsFun f)) = Xml.elt "name" [Xml.text $ BS.unpack f]
  toXml (F (DpFun f)) =
    Xml.elt "sharp" [Xml.elt "name" [Xml.text $ BS.unpack f]]
  toXml (F (ComFun f)) = Xml.elt "name" [Xml.text $ 'c' : show f]
  toCeTA = Xml.toXml
