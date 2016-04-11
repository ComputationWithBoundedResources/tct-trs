-- | This module provides term rewriting signatures. This module is intended to be imported qualified.
module Tct.Trs.Data.Signature
  ( Signature
  , Symbols
  , toMap
  , mkSignature

  -- * queries
  , symbols
  , elems
  , arity
  , positions
  , defineds
  , isDefined
  , constructors
  , isConstructor

  -- * updates
  , setArity
  , union
  , map
  , filter
  , partition
  , restrictSignature
  , restrictToSignature
  ) where


import qualified Data.Map.Strict        as M
import           Data.Maybe             (fromMaybe)
import qualified Data.Set               as S
import           Prelude                hiding (filter, map)

import qualified Tct.Core.Common.Pretty as PP
import qualified Tct.Core.Common.Xml    as Xml


-- MS: The arity of a function symbol is stored as an attibute in the signature.
-- This is diffent than distinguishing DP/Compound symbols. Wich are encoded in the symbol itself.
-- Maybe the arity should also be encoded; in Combination with a class HasArity?

type Symbols f = S.Set f

-- | The signature type. Assumes an ordering on the symbols @f@; viz. the informations necessary to distinguish
-- function symbols (eg. dependencyPair) are encoded in @f@.
-- Following properties hold for all build and update functions.
--
-- prop> symbols sig == defineds_ sig `S.union` constructors_ sig
-- prop> defineds_ sig `S.intersection` constructors_ sig == S.empty
data Signature f = Signature
  { signature_    :: M.Map f Int
  , defineds_     :: Symbols f
  , constructors_ :: Symbols f }
  deriving (Eq, Ord, Show)

-- | Returns a map associating function symbols to its arity.
toMap :: Signature f -> M.Map f Int
toMap = signature_

-- | Returns a Signature given a pair of (defined symbols, constructor symbols).
-- Returns an error if the symbol sets are not distinct.
mkSignature :: Ord f => (M.Map f Int, M.Map f Int) -> Signature f
mkSignature (ds,cs) = Signature
  { signature_    = M.unionWith err ds cs
  , defineds_     = M.keysSet ds
  , constructors_ = M.keysSet cs }
  where err _ _ = error "Tct.Trs.Data.Signature.mkSignature: symbol already defined."


--- * queries --------------------------------------------------------------------------------------------------------

-- | Returns the set of symbols.
symbols :: Signature f -> Symbols f
symbols = M.keysSet . signature_

-- | Returns the defined symbols
defineds :: Signature f -> Symbols f
defineds = defineds_

-- TODO: MS: flip arguments
-- | Checks wether the given symbol is a defined symbol.
isDefined :: Ord f => f -> Signature f -> Bool
isDefined f = S.member f . defineds

-- | Returns the constructor symbols.
constructors :: Signature f -> Symbols f
constructors = constructors_

-- TODO: MS:flip arguments
-- | Checks wether the given symbol is a constructor symbol.
isConstructor :: Ord f => f -> Signature f -> Bool
isConstructor f = S.member f . constructors

-- | Returns function symbols together with their arity.
elems :: Signature f -> [(f, Int)]
elems = M.assocs . toMap

-- | Returns the arity of a symbol.
arity :: Ord f => Signature f ->  f -> Int
arity sig f = err `fromMaybe` M.lookup f (signature_ sig)
  where err = error "Signature: symbol not found "

-- | Returns the positions of a symbol. By convention we start with index @1@.
--
-- positions sig f = [1..arity sig f].
positions :: Ord f => Signature f ->  f -> [Int]
positions sig f = err `fromMaybe` (M.lookup f (signature_ sig) >>= \ar -> return [1..ar])
  where err = error "Signature: symbol not found"


--- * update ---------------------------------------------------------------------------------------------------------

-- | Modifies the arity of a Symbol.
setArity :: Ord f => Int -> f -> Signature f -> Signature f
setArity i f sig = sig { signature_ = M.alter k f (signature_ sig) }
  where k = maybe (error "Tct.Trs.Data.Signature.setArity: undefined symbol.") (const $ Just i)

-- | Maps over the symbols.
--
-- prop> f `S.elems` (defineds sig) <=> (k f) `S.elems` (defineds $ map k sig)
map :: Ord f2 => (f1 -> f2) -> Signature f1 -> Signature f2
map f sig = Signature
  { signature_    = M.mapKeys f (signature_ sig)
  , defineds_     = S.map f (defineds_ sig)
  , constructors_ = S.map f (constructors_ sig) }

-- | Computes the union of two singatures. Throws an error if @f1 == f2@ and @arity f1 /= arity f2@, for any @f1@ in
-- the first signature and @f2@ in the second signature.
--
-- prop> defineds sig3 == defineds sig1 `S.union` defineds sig2
-- prop> constructors sig3 `S.subset` (constructors sig1 `S.union` constructors sig3)
union :: Ord f => Signature f -> Signature f -> Signature f
union sig1 sig2 = Signature
  { signature_    = M.unionWith err1 (signature_ sig1) (signature_ sig2)
  , defineds_     = ds
  , constructors_ = cs `S.difference` ds }
  where
    ds = defineds_ sig1 `S.union` defineds_ sig2
    cs = constructors_ sig1 `S.union` constructors_ sig2
    err1 ar1 ar2 = if ar1 == ar2 then ar1 else error "Tct.Trs.Data.Signature.union: same symbol with different arities"

-- | Filter function symbols.
filter :: (f -> Bool) -> Signature f -> Signature f
filter g sig = Signature
  { signature_    = M.filterWithKey (\f _ -> g f) (signature_ sig)
  , defineds_     = S.filter g (defineds_ sig)
  , constructors_ = S.filter g (constructors_ sig) }

-- | Partition function symbols.
partition :: (f -> Bool) -> Signature f -> (Signature f, Signature f)
partition g sig = (filter g sig, filter (not . g) sig)

-- | Restrict the signature wrt. to a set of symbols.
restrictSignature :: Ord f => Signature f -> Symbols f -> Signature f
restrictSignature sig fs = filter (`S.member` fs) sig

-- | Restrict a set of symbols to the signature.
restrictToSignature :: Ord f => Signature f -> Symbols f -> Symbols f
restrictToSignature sig fs = symbols sig `S.intersection` fs


--- * proofdata ------------------------------------------------------------------------------------------------------

instance (Ord f, PP.Pretty f) => PP.Pretty (Signature f) where
  pretty sig = PP.set (k `fmap` ds) PP.<+> PP.char '/' PP.<+> PP.set (k `fmap` cs)
    where
      ds = elems $ restrictSignature sig (defineds sig)
      cs = elems $ restrictSignature sig (constructors sig)
      k (f,i) = PP.pretty f PP.<> PP.char '/' PP.<> PP.int i

instance Xml.Xml f => Xml.Xml (Signature f) where
  toXml sig = Xml.elt "signature" [ symb f i | (f,i) <- elems sig ]
    where symb f i = Xml.elt "symbol" [ Xml.toXml f, Xml.elt "arity" [Xml.int i] ]
  toCeTA = Xml.toXml

