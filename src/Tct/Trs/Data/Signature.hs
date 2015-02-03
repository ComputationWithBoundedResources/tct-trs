module Tct.Trs.Data.Signature
  ( Signature
  , toMap
  , fromMap
  , Symbols
  , arity
  , symbols
  , elems
  , onSignature
  , filter
  , restrictSignature
  ) where


import qualified Data.Map.Strict as M
import           Data.Maybe      (fromMaybe)
import qualified Data.Set        as S
import           Prelude         hiding (filter)


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

