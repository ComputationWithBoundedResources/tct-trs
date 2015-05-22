-- | This module implements usable argument positions.
-- By convention, n-ary function symbols admit argument positions '[1..n]'.
module Tct.Trs.Encoding.UsablePositions
  (
  -- * Usable Argument Positions
  UsablePositions
  , usableArgs
  , usableArgsWhereApplicable
  , usablePositions
  , fullWithSignature
  ) where


import qualified Data.IntSet              as IS
import qualified Data.List                as L
import qualified Data.Map.Strict          as M
import           Data.Monoid
import qualified Data.Set                 as S

import qualified Data.Rewriting.Rule      as R
import qualified Data.Rewriting.Term      as R

import qualified Tct.Core.Common.Pretty   as PP
import qualified Tct.Core.Common.Xml      as Xml

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem     as Prob
import qualified Tct.Trs.Data.ProblemKind as Prob
import qualified Tct.Trs.Data.Rewriting   as R (isUnifiable)
import qualified Tct.Trs.Data.Signature   as Sig
import qualified Tct.Trs.Data.Symbol      as Symb
import qualified Tct.Trs.Data.Trs         as Trs


-- | Maps function symbols to a set of (usable) argument positions.
newtype UsablePositions f = UP (M.Map f IS.IntSet) deriving (Eq, Show)


-- | Returns the list of usable argument positions.
usablePositionsOf:: Ord f => UsablePositions f -> f -> [Int]
usablePositionsOf (UP m) sym =
  case M.lookup sym m of
    Just poss -> IS.toAscList poss
    Nothing   -> []

-- | Empty usable positions.
empty :: UsablePositions f
empty = UP M.empty

-- | Constructs usable argument for a single function symbol.
singleton :: f -> [Int] -> UsablePositions f
singleton sym is = UP $ M.singleton sym (IS.fromList is)

-- | Union on usable argument positions.
union :: Ord f => UsablePositions f -> UsablePositions f -> UsablePositions f
(UP u1) `union` (UP u2) = UP $ M.unionWith IS.union u1 u2

-- | List version of 'union'.
unions :: Ord f => [UsablePositions f] -> UsablePositions f
unions = foldl union empty

-- emptyWithSignature :: Ord f => Signature f -> UsablePositions f
-- emptyWithSignature sig = unions $ map (\(f,_) -> singleton f []) $ Sig.elems sig

fullWithSignature :: Ord f => Signature f -> UsablePositions f
fullWithSignature sig = unions $ map (\(f,ar) -> singleton f [1..ar]) $ Sig.elems sig

restrictToSignature :: Ord f => Signature f -> UsablePositions f -> UsablePositions f
restrictToSignature sig (UP ua) = UP $ M.filterWithKey (\f _ -> f `S.member` fs) ua
  where fs = Sig.symbols sig

-- | Predicate that returns true if the ith argument position is usable.
-- Defaults to 'False'.
isUsable :: Ord f => f -> Int -> UsablePositions f -> Bool
isUsable sym i (UP m) = maybe False (IS.member i) (M.lookup sym m)


--- * construction ---------------------------------------------------------------------------------------------------

-- | Constructs the usable argument positions of a given TRS,
-- with respect to a given strategy.
usableArgs :: (Ord f, Ord v) => Prob.Strategy -> Trs f v -> UsablePositions f
usableArgs = usableArgsCap

usableArgsCap :: (Ord f, Ord v) => Prob.Strategy -> Trs f v -> UsablePositions f
usableArgsCap Prob.Innermost trs = usableReplacementMap trs empty
usableArgsCap _ trs              = fix (usableReplacementMap trs) empty
  where
    fix f up
      | res == up = up
      | otherwise = fix f res
      where res = f up

usableReplacementMap :: (Ord f, Ord v) => Trs f v -> UsablePositions f -> UsablePositions f
usableReplacementMap trs up = unions [ snd $ uArgs l r | R.Rule l r <- rules]
  where
    rules = Trs.toList trs
    uArgs l t@(R.Var _)    = (not (isBlockedProperSubtermOf t l), empty)
    uArgs l t@(R.Fun f ts) = (not (isBlockedProperSubtermOf t l) && (subtermUsable || hasRedex)
                             , unions $ new : [ uargs | (_,_,uargs) <- uArgs'] )
      where
        uArgs' = [ let (usable,uargs) = uArgs l ti in (i,usable,uargs)  | (i, ti) <- zip [1 :: Int ..] ts]
        subtermUsable = any (\ (_,usable,_) -> usable) uArgs'
        hasRedex = any (R.isUnifiable t . R.lhs) rules
        new = singleton f [i | (i, usable, _) <- uArgs', usable]
    isBlockedProperSubtermOf s t = any (isBlockedProperSubtermOf s . snd) uSubs || any (isSubtermOf s . snd) nonSubs
      where
        (uSubs, nonSubs) = L.partition (\ (i, _) -> isUsable f i up ) $ zip [1 :: Int ..] $ immediateSubterms t
        f                =
          case R.root t of
            Left  _  -> error "Tct.Encoding.UsablePositions.isBlockedProperSubtermOf: root t called for a variable t"
            Right f' -> f'
    isSubtermOf t s = t `elem` R.subterms s
    immediateSubterms (R.Var _)    = []
    immediateSubterms (R.Fun _ ts) = ts


-- | Returns an approximation of the usable positions of a problem.
-- The resulting mapping does not necessarily contain all function symbols. Used togehter with 'isUsable'.
usableArgsWhereApplicable :: Ord v => Problem F v
  -> Bool  -- ^ map non-compound symbols to the empty set
  -> Bool  -- ^ approximate usable positions using CAP variant
  -> UsablePositions F
usableArgsWhereApplicable prob onlyCompound useUA = case (onlyCompound, useUA, Prob.startTerms prob) of
  (True, True, _)               -> restrictToSignature compSig (usableArgs str trs)
  (True, _,    _)               -> fullWithSignature compSig
  (_,    _,    Prob.AllTerms{}) -> fullWithSignature sig
  (_,    ua,   _)               -> if ua then usableArgs str trs else fullWithSignature sig
  where
    trs     = Prob.allComponents prob
    str     = Prob.strategy prob
    sig     = Prob.signature prob
    compSig = Sig.filter Symb.isCompoundFun sig

-- | Returns the usable positions as list.
usablePositions :: UsablePositions f -> [(f, [Int])]
usablePositions (UP m) = M.toList (M.map IS.toList m)


--- * proofdata ------------------------------------------------------------------------------------------------------

instance (Ord f, PP.Pretty f) => PP.Pretty (UsablePositions f) where
  pretty up@(UP m)
    | null syms = PP.text "none"
    | otherwise = PP.vsep $ PP.punctuate (PP.char ',') (ppsym `fmap` syms)
    where
      syms      = M.keys $ M.filter (not  . IS.null) m
      ppsym sym = PP.text "uargs" <> PP.parens (PP.pretty sym) <> PP.text " = " <> PP.set' (usablePositionsOf up sym)

instance Xml.Xml f => Xml.Xml (UsablePositions f) where
  toXml (UP m) =
    Xml.elt "usablePositions"
      [ Xml.elt "usable" $
        Xml.elt "name" [Xml.toXml f] :
        {-, Xml.elt "arity" [Xml.int $ F.arity sig $ invEnum f] ]-}
        [ Xml.elt "position" [Xml.int i] | i <- IS.toList is]
      | (f,is) <- M.toList m ]

