{-# LANGUAGE ScopedTypeVariables #-}
-- | This module implements safe mapping.
-- By convention, n-ary function symbols admit argument positions '[1..n]'.
module Tct.Trs.Encoding.SafeMapping where


import qualified Data.IntSet            as IS
import qualified Data.Map.Strict        as M
import qualified Data.Set               as S

import qualified Data.Rewriting.Rule    as R

import qualified Tct.Core.Common.Pretty as PP

import           Tct.Trs.Data
import           Tct.Trs.Data.Trs as Trs (toList)
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
partitionArguments (R.Fun f ts) sm = foldr k ([],[]) (zip [1..] ts)
  where
    k (i,ti) (s',n') = if i `elem` sp then (ti:s',n') else (s',ti:n')
    sp               = safeArgumentPositions f sm
partitionArguments _ _ = error "Encoding.SafeMapping.partitionArguments: variable given"

setSafe :: Ord f => f -> Int -> SafeMapping f -> SafeMapping f
setSafe sym i (SafeMapping (sig,m)) = SafeMapping (sig, M.alter k sym m)
  where
    k (Just s) = Just $ IS.insert i s
    k Nothing  = Just $ IS.singleton i

setSafes :: Ord f => f -> [Int] -> SafeMapping f -> SafeMapping f
setSafes sym is sm = foldr (setSafe sym) sm is


--- * proofdata ------------------------------------------------------------------------------------------------------

instance (Ord f, PP.Pretty f) => PP.Pretty (SafeMapping f) where
  pretty sm@(SafeMapping (sig, _)) = PP.hsep $ PP.punctuate (PP.text ",") [ pp sym | sym <- S.toList $ Sig.symbols sig]
    where pp sym = PP.text "safe" PP.<> PP.parens (PP.pretty sym) PP.<+> PP.text "=" PP.<+> PP.set' (safeArgumentPositions sym sm)

type SafeTrs f v = (Trs f v, SafeMapping f)

prettySafeTrs :: (Ord f, PP.Pretty f, PP.Pretty v) => SafeMapping f -> Trs f v -> PP.Doc
prettySafeTrs sm = PP.vcat . fmap ppr . Trs.toList
  where
    ppr (R.Rule l r)   = PP.hsep [ppt l, PP.text "->", ppt r]

    ppt v@(R.Var _)    = PP.pretty v
    ppt t@(R.Fun _ []) = PP.pretty t
    ppt t@(R.Fun f _)  = PP.pretty f PP.<> PP.parens ( ppa nrm PP.<> PP.semi `sa` ppa sf )
      where 
        (sf,nrm) = partitionArguments t sm
        sa       = if null sf then (PP.<>) else (PP.<+>)
    ppa ts = PP.hsep $ PP.punctuate PP.comma [ppt t_i | t_i <- ts]

