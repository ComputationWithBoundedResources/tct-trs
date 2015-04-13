module Tct.Trs.Data.Signature
  ( Signature
  , toMap
  , fromMap
  , onSignature
  , alter
  , Symbols
  , arity
  , positions
  , symbols
  , elems
  , filter
  , partition
  , restrictSignature
  ) where


import qualified Tct.Core.Common.Pretty as PP
import qualified Tct.Core.Common.Xml    as Xml


import qualified Data.Map.Strict        as M
import           Data.Maybe             (fromMaybe)
import qualified Data.Set               as S
import           Prelude                hiding (filter)


-- TODO: MS:
-- functionsymbol should have arity, otherwise ambigious
-- maybe a set for constructor and defined symbols?

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
arity :: Ord f => Signature f ->  f -> Int
arity sig f = err `fromMaybe` M.lookup f (toMap sig)
  where err = error "Signature: symbol not found "

-- | Returns the positions of a symbol. By convention [1..arity f].
positions :: Ord f => Signature f ->  f -> [Int]
positions sig f = err `fromMaybe` (M.lookup f (toMap sig) >>= \ar -> return [1..ar])
  where err = error "Signature: symbol not found"

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

-- | Partition function symbols.
partition :: (f -> Bool) -> Signature f -> (Signature f, Signature f)
partition g = both fromMap . M.partitionWithKey k . toMap
  where 
    k f _        = g f
    both f (a,b) = (f a, f b)

-- | Restrict the signature wrt. to a set of symbols.
restrictSignature :: Ord f => Signature f -> Symbols f -> Signature f
restrictSignature sig fs = onSignature (M.filterWithKey k) sig
  where k f _ = f `S.member` fs


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty f => PP.Pretty (Signature f) where
  pretty = PP.set . map k . elems
    where k (f,i) = PP.tupled [PP.pretty f, PP.int i]

instance Xml.Xml f => Xml.Xml (Signature f) where
  toXml sig = Xml.elt "signature" [ symb f i | (f,i) <- elems sig ]
    where symb f i = Xml.elt "symbol" [ Xml.toXml f, Xml.elt "arity" [Xml.int i] ]
  toCeTA = Xml.toXml

