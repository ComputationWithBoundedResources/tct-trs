module Tct.Trs.Data.Signature
  ( Signature
  , toMap
  , fromMap
  , onSignature
  , alter
  , Symbols
  , arity
  , symbols
  , elems
  , filter
  , restrictSignature
  ) where

import qualified Tct.Core.Common.Pretty as PP
import qualified Tct.Core.Common.Xml    as Xml


import qualified Data.Map.Strict        as M
import           Data.Maybe             (fromMaybe)
import qualified Data.Set               as S
import           Prelude                hiding (filter)


newtype Signature f = Signature (M.Map f Int)
  deriving (Eq, Ord, Show)

-- | Returns a signature from a map.
toMap :: Signature f -> M.Map f Int
toMap (Signature m) = m

-- | Returns a signature from a map.
fromMap :: M.Map f Int -> Signature f
fromMap = Signature

onSignature :: (M.Map f Int -> M.Map f2 Int) -> Signature f -> Signature f2
onSignature f = fromMap . f . toMap

alter :: Ord f => (Maybe Int -> Maybe Int) -> f -> Signature f -> Signature f
alter f k = onSignature (M.alter f k)

type Symbols f = S.Set f

-- | Returns the arity of a symbol.
arity :: (Ord f, Show f) => Signature f ->  f -> Int
arity sig f = err `fromMaybe` M.lookup f (toMap sig)
  where err = error $ "Signature: not found " ++ show f

-- | Returns a set of symbols.
symbols :: Signature f -> Symbols f
symbols = M.keysSet . toMap

-- | Returns function symbols together with their arity.
elems :: Signature f -> [(f, Int)]
elems = M.assocs . toMap

-- | Filter function symbols.
filter :: (f -> Bool) -> Signature f -> Signature f
filter g = onSignature (M.filterWithKey k)
  where k f _ = g f

-- | Restrict the signature wrt. to a set of symbols.
restrictSignature :: Ord f => Signature f -> Symbols f -> Signature f
restrictSignature sig fs = onSignature (M.filterWithKey k) sig
  where k f _ = f `S.member` fs


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty f => PP.Pretty (f, Int) where
  pretty (f,i) = PP.tupled [PP.pretty f, PP.int i]

instance Xml.Xml f => Xml.Xml (Signature f) where
  toXml sig = Xml.elt "signature" [ symb f i | (f,i) <- elems sig ]
    where symb f i = Xml.elt "symbol" [ Xml.toXml f, Xml.elt "arity" [Xml.int i] ]
  toCeTA = Xml.toXml

