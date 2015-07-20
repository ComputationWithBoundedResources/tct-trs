{-# LANGUAGE ScopedTypeVariables #-}
{- |
Module      :  Tct.Trs.Encoding.SafeMapping
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>,
               Georg Moser <georg.moser@uibk.ac.at>,
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable

This module implements safe mapping, together with a a SAT encoding.
By convention, n-ary function symbols admit argument positions '[1..n]'.
-}

module Tct.Trs.Encoding.SafeMapping where

import qualified Data.Traversable as F
import qualified Data.IntSet            as IS
import qualified Data.Map.Strict        as M
import qualified Data.Set               as S

import qualified Data.Rewriting.Term    as R

import qualified Tct.Common.SMT as SMT

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Signature as Sig


newtype SafeMapping f = SafeMapping (Signature f, M.Map f IS.IntSet)
  deriving Show

newtype SafePosition f = SP (f, Int)
  deriving (Eq, Ord, Show)


empty :: Ord f => Signature f -> SafeMapping f
empty sig = SafeMapping (sig, m)
  where m = M.fromList [ (c, IS.fromList (Sig.positions sig c)) | c <- S.toList $ Sig.constructors sig]

isSafe :: Ord f => SafeMapping f -> f -> Int -> Bool
isSafe (SafeMapping (_,m)) sym i =
  case M.lookup sym m of
    Just safePositions -> IS.member i safePositions
    Nothing            -> False

safeArgumentPositions :: Ord f => f -> SafeMapping f -> [Int]
safeArgumentPositions sym (SafeMapping (_,m)) =
  case M.lookup sym m of
    Just safePositions -> IS.toAscList safePositions
    Nothing            -> []

partitionArguments :: Ord f => R.Term f v -> SafeMapping f -> ([R.Term f v],[R.Term f v])
partitionArguments (R.Fun f ts) sm = (reverse s, reverse n)
  where
    sp    = safeArgumentPositions f sm
    (s,n) = foldr k ([],[]) (zip [1..] ts)
      where k (i,ti) (s',n') = if i `elem` sp then (ti:s',n') else (s',ti:n')
partitionArguments _ _ = error "Encoding.SafeMapping.partitionArguments: variable given"

-- newtype SafeMappingEncoder f = SafeMappingEncoder
--   (M.Map f SMT.Expr)  -- ^ maps functions symbol to variables

-- isSafeP :: (Eq l) => f -> Int -> PropFormula l
-- isSafeP sym i = propAtom $ SP (sym,i)

setSafe :: Ord f => f -> Int -> SafeMapping f -> SafeMapping f
setSafe sym i (SafeMapping (sig,m)) = SafeMapping (sig, M.alter k sym m)
  where
    k (Just s) = Just $ IS.insert i s
    k Nothing  = Just $ IS.singleton i

setSafes :: Ord f => f -> [Int] -> SafeMapping f -> SafeMapping f
setSafes sym is sm = foldr (setSafe sym) sm is


-- validSafeMapping :: [f] -> Signature f -> SMT.SolverStM SMT.Expr (SafeMappingEncoder f, SMT.Expr)
-- validSafeMapping constructors sig = do
--   m <- F.mapM (const SMT.bvarM') (Sig.toMap sig)
--   return (SafeMappingEncoder m, SMT.bigAnd m)

-- instance Ord f => SMT.Decode SMT.Environment (SafeMappingEncoder f) (SafeMapping f) where
--   decode = undefined
    -- m1 :: M.Map f <- SMT.decode (SMT.Property (fromMaybe False) m)
    -- return . UsableSymbols $ fs `S.union` m1

-- SMT.bigAnd [ isSafeP con i | con <- constructors, i <- argumentPositions sig con]


{-
  (
    -- * Safe Mappings
    SafeMapping
  , empty
    -- | The empty safe argument filtering.
  , isSafe
    -- | Predicate that checks wether the given argument position
    -- of the given symbol is safe.

  , setSafe
    -- | Set ith argument position of given symbol safe.

  , setSafes
    -- | List version of 'setSafe'.

  , safeArgumentPositions
    -- | Returns the list of safe argument positions.

    -- * Sat Encoding
  , validSafeMapping
    -- | Add this constraint for a valid SAT encoding.
  , isSafeP
    -- | The Formula 'isSafeP f i' reflects
    -- that the ith argument position of 'f' is safe.
  )
where

import qualified Data.Map as Map
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Termlib.Rule (Rule(..))
import Termlib.Trs (Trs, rules)
import Termlib.Variable (Variables)
import Termlib.Term
import qualified Termlib.Variable as V

import Data.IntSet (IntSet)
import Data.Typeable
import Qlogic.SatSolver
import Qlogic.Boolean
import Qlogic.PropositionalFormula
import Data.List (sort)
import Termlib.Utils (PrettyPrintable(..))
import Termlib.FunctionSymbol
import Prelude hiding ((||),(&&),not)
import Text.PrettyPrint.HughesPJ hiding (empty)

newtype SafeMapping = SM (Signature, Map.Map Symbol IntSet) deriving Show

newtype SafePosition = SP (Symbol, Int) deriving (Eq, Ord, Typeable, Show)

instance PropAtom SafePosition

empty :: Signature -> Set.Set Symbol -> SafeMapping
empty sig constructors = SM (sig, Map.fromList $ [ (c, IntSet.fromList (argumentPositions sig c))
                                                   | c <- Set.toList constructors] )

isSafe :: SafeMapping -> Symbol -> Int -> Bool
isSafe (SM (_,m)) sym i  =
  case Map.lookup sym m of
    Just safePositions -> IntSet.member i safePositions
    Nothing ->  False

safeArgumentPositions :: Symbol -> SafeMapping -> [Int]
safeArgumentPositions sym (SM (_,m)) = case Map.lookup sym m of
                                         Just safePositions -> sort $ IntSet.toList $ safePositions
                                         Nothing -> []

partitionArguments :: Term -> SafeMapping -> ([Term],[Term])
partitionArguments (Fun f ts) sm = (reverse s, reverse n)
    where sp = safeArgumentPositions f sm
          (s,n) = foldl (\ (s',n') (i,ti) -> if i `elem` sp then (ti:s',n') else (s',ti:n')) ([],[]) (zip [1..] ts)
partitionArguments _ _ = error "Encoding.SafeMapping.partitionArguments: variable given"

isSafeP :: (Eq l) => Symbol -> Int -> PropFormula l
isSafeP sym i = propAtom $ SP (sym,i)

setSafe :: Symbol -> Int -> SafeMapping -> SafeMapping
setSafe sym i (SM (sig,m)) = SM (sig, Map.alter alter sym m)
  where alter (Just s) = Just $ IntSet.insert i s
        alter Nothing = Just $ IntSet.singleton i

setSafes :: Symbol -> [Int] -> SafeMapping -> SafeMapping
setSafes sym is sm = foldl (\ sm' i -> setSafe sym i sm') sm is


instance Decoder SafeMapping SafePosition where
  add (SP (f, i)) = setSafe f i

validSafeMapping :: Eq l => [Symbol] -> Signature -> PropFormula l
validSafeMapping constructors sig = bigAnd [ isSafeP con i | con <- constructors, i <- argumentPositions sig con]

instance PrettyPrintable SafeMapping where
  pprint sm@(SM (sig, _)) = fsep $ punctuate (text ",") [ pp sym | sym <- Set.toList $ symbols sig]
    where pp sym = text "safe" <> parens (pprint (sym, sig)) <+> text "="
                   <+> (braces . fsep . punctuate (text ",") $ [ text $ show i | i <- safeArgumentPositions sym sm])


instance PrettyPrintable (Trs, Signature, Variables, SafeMapping) where
  pprint (trs, sig, var, sm) = braces $ pprs (rules trs)
      where pprs []          = text ""
            pprs [r]         = ppr r
            pprs rs          = vcat $ [com <+> ppr r | (com,r) <- zip (text " " : repeat (text ",")) rs]

            ppr (Rule l r)   = fsep [ppt l, text "->", ppt r]

            ppt (Var x)      = text $ V.variableName x var
            ppt (Fun f [])   = pprint (f,sig) <> parens ( text "" )
            ppt t@(Fun f _)  = pprint (f,sig) <> parens ( ppa nrm <> text ";" `sa` ppa sf )
                where (sf,nrm) = partitionArguments t sm
                      sa | length sf == 0 = (<>)
                         | otherwise      = (<+>)
            ppa ts           = sep $ punctuate (text ",") [ppt t_i | t_i <- ts]
-}
