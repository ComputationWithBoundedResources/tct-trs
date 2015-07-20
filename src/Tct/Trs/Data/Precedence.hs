module Tct.Trs.Data.Precedence
  ( Order (..)
  , Precedence (..)
  , precedence
  , empty
  , insert
  , eclasses
  , recursionDepth
  , ranks
  ) where


import qualified Control.Monad.State.Strict as St
import           Data.List                  (find)
import qualified Data.Map                   as M
import           Data.Maybe                 (fromMaybe)
import qualified Data.Set                   as S

import qualified Tct.Core.Common.Pretty     as PP

import           Tct.Trs.Data.Signature     (Signature, Symbols, symbols)


data Order b = b :>: b | b :~: b
  deriving (Show, Eq, Ord)

newtype Precedence f = Precedence (Signature f, [Order f]) deriving Show

instance PP.Pretty f => PP.Pretty (Precedence f) where
  pretty (Precedence (_, [])) = PP.text "empty"
  pretty (Precedence (_,l))   = PP.hsep $ PP.punctuate (PP.text ",") [pp e | e <- l]  where
    pp (f :>: g) =  PP.pretty f PP.<+> PP.text ">" PP.<+> PP.pretty g
    pp (f :~: g) =  PP.pretty f PP.<+> PP.text "~" PP.<+> PP.pretty g

precedence :: Signature f -> [Order f] -> Precedence f
precedence = curry Precedence

empty :: Signature f -> Precedence f
empty sig = precedence sig []

insert :: Order f -> Precedence f -> Precedence f
insert e (Precedence (sig, l)) = Precedence (sig, e : l)

eclasses :: Ord f => Precedence f -> [Symbols f]
eclasses (Precedence (_, l)) = foldr ins [] l
  where
    ins (g :~: h) [] = [S.fromList [g,h]]
    ins  eq@(g :~: h) (ec:ecs)
      | g `S.member` ec = h `S.insert` ec : ecs
      | h `S.member` ec = g `S.insert` ec : ecs
      | otherwise       = ec : ins eq ecs
    ins _ ecs                 = ecs

recursionDepth :: Ord f => Symbols f -> Precedence f -> M.Map f Int
recursionDepth recursives prec@(Precedence (sig, l)) = St.execState (mapM_ recdepthM syms) M.empty
    where
      ecss = eclasses prec

      eclassOf f = S.singleton f `fromMaybe` find (\ cs -> f `S.member` cs) ecss

      syms = S.toList $ symbols sig

      below f = S.toList $ S.unions [ eclassOf h | f' :>: h <- l , f == f' ]

      recdepthM f = do
        m <- St.get
        case M.lookup f m of
          Just rd -> return rd
          Nothing -> do
            rds <- mapM recdepthM (below f)
            let rd | f `S.member` recursives = 1 + maximum (0:rds)
                   | otherwise               = maximum (0:rds)
            St.modify (M.insert f rd)
            return rd

-- | ranks of function symbols in precedence, starting at '1'
ranks :: Ord f => Precedence f -> M.Map f Int
ranks prec@(Precedence(sig,_)) = recursionDepth (symbols sig) prec

