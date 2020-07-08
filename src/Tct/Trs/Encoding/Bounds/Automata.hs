{-# LANGUAGE FlexibleContexts #-}

----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Processor.Bounds.Automata
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>,
--                Georg Moser <georg.moser@uibk.ac.at>,
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>,
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable
--
-- This module implements automata functionality as employed by
-- the bounds processor.
-----------------------------------------------------------------------------------

module Tct.Trs.Encoding.Bounds.Automata where

import           Control.Monad.State.Class (MonadState (..))
import qualified Control.Monad.State.Lazy  as St
import           Data.IntMap               (IntMap)
import qualified Data.IntMap               as IM
import           Data.List                 (nub)
import           Data.Map                  (Map)
import qualified Data.Map                  as M
import           Data.Maybe                (fromMaybe)
import           Data.Set                  (Set)
import qualified Data.Set                  as S

import qualified Data.Rewriting.Term       as R


-- TODO: move utility functions
type MemoAction k a = St.State (M.Map k a)

memo :: Ord k => k -> MemoAction k a a -> MemoAction k a a
memo k  m = do
  s <- St.get
  case M.lookup k s of
    Just old -> return old
    Nothing  -> do { new <- m;
                    St.modify (M.insert k new);
                    return new}


runMemoAction :: (Ord k) => MemoAction k a b -> b
runMemoAction ma = fst $ St.runState ma M.empty

liftMemo :: (Ord k) => (k -> a) -> k -> MemoAction k a a
liftMemo f k = memo k (return $ f k)


ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM b t e = do g <- b
               if g then t else e


listProduct :: [[a]] -> [[a]]
listProduct []             = [[]]
listProduct (xs:xss) = foldl f [] xs
  where f a x = map (\ xs' -> x:xs') (listProduct xss) ++ a

snub :: Ord a => [a] -> [a]
snub = S.toList . S.fromList

data Strictness = StrictRule | WeakRule


-- | This datatype represents the /enrichment/ employed.
data Enrichment =
  Match -- ^ Matchbounds.
  | Roof -- ^ Roofbounds.
  | Top -- ^ Topbounds.
  deriving (Enum, Bounded, Eq)

instance Show Enrichment where
    show Match = "match"
    show Roof  = "roof"
    show Top   = "top"

data WeakBoundedness = WeakMayExceedBound | WeakMayNotExceedBound

-- TODO:MA: which types should be strict?
newtype Symbol = Symbol Int deriving (Eq, Ord, Show, Enum, Read)
type Label     = Int
type LSym      = (Symbol,Label)
type State     = Int


data LTerm
  = F LSym [LTerm]
  | S State
  deriving (Eq, Ord, Read, Show)


data Rule
  = Collapse LSym [State] State
  | Epsilon State State
  deriving (Eq, Ord, Show)


-- TODO:MA: sym -> ... in beiden automaten
type FwdAutomaton = IntMap (IntMap (Map [State] (Set State)))
-- sym -> l -> args -> qs   <=> forall q \in qs. sym_l(args) -> q \in A

type BwdAutomaton = IntMap (IntMap (IntMap (Set [State])))
-- sym -> q -> l -> argss <=> forall args \in argss. sym_l(args) -> q \in A

data Automaton = Automaton
  { fwd                :: FwdAutomaton
  , bwd                :: BwdAutomaton
  , epsilonTransitions :: Set (State,State)
  , fresh              :: State
  , maxlabel           :: Label
  , finalStates        :: [State] }
  deriving (Eq, Show)

size :: LTerm -> Int
size (F _ ts) = 1 + sum (map size ts)
size (S _)    = 0

isEpsilonRule :: Rule -> Bool
isEpsilonRule Epsilon{}  = True
isEpsilonRule Collapse{} = False

lift :: Symbol -> Label -> LSym
lift = (,)

base :: LSym -> Symbol
base = fst

height :: LSym -> Label
height = snd

baseTerm :: LTerm -> R.Term Symbol v
baseTerm (F f ts) = R.Fun (base f) $ map baseTerm ts
baseTerm (S _)    = error "Cannot convert a labeled term with Tree automaton states back to a normal term"

toRules :: Automaton -> [Rule]
toRules a = [Collapse (toEnum f,l) args q | (f,m1) <- IM.toList $ fwd a
                                           , (l,m2) <- IM.toList m1
                                           , (args, qs) <- M.toList m2
                                           , q <- S.toList qs]
            ++ [Epsilon p q | (p,q) <- S.toList (epsilonTransitions a)]

states :: Automaton -> [State]
states = nub . concatMap statesRl . toRules where
  statesRl (Epsilon p q)     = [p,q]
  statesRl (Collapse _ as q) = q : as

fromRules :: [State] -> [Rule] -> Automaton
fromRules fss = foldl (flip insert) empty {finalStates = fss, fresh = maximum (0:fss) + 1}

empty :: Automaton
empty = Automaton IM.empty IM.empty S.empty 0 0 []

freshState :: Automaton -> (State, Automaton)
freshState a = (fr, Automaton (fwd a) (bwd a) (epsilonTransitions a) (fr  + 1) (maxlabel a) (finalStates a))
    where fr = fresh a

freshStates :: Int -> Automaton -> ([State], Automaton)
freshStates 0 a = ([], a)
freshStates i a = case freshStates (i - 1) a' of (qs, a'') -> (q:qs,a'')
  where (q, a') = freshState a


fwdInsert :: LSym -> [State] -> State -> FwdAutomaton -> FwdAutomaton
fwdInsert (f,l) qs q = IM.alter alter1 (fromEnum f)
        where default3 = S.singleton q
              default2 = M.singleton qs default3
              default1 = IM.singleton l default2
              alter1 = Just . maybe default1 (IM.alter alter2 l)
              alter2 = Just . maybe default2 (M.alter alter3 qs)
              alter3 = Just . maybe default3 (S.insert q)


bwdInsert :: LSym -> [State] -> State -> BwdAutomaton -> BwdAutomaton
bwdInsert (f,l) qs q = IM.alter alter1 (fromEnum f)
    where default3 = S.singleton qs
          default2 = IM.singleton l default3
          default1 = IM.singleton q default2
          alter1 = Just . maybe default1 (IM.alter alter2 q)
          alter2 = Just . maybe default2 (IM.alter alter3 l)
          alter3 = Just . maybe default3 (S.insert qs)


-- MA:TODO verifizieren dass fresh immer "frisch" ist
insert :: Rule -> Automaton -> Automaton
insert (Collapse sym args q) (Automaton f b e fr l iss) = Automaton (fwdInsert sym args q f) (bwdInsert sym args q b) e (maximum $ [fr, q + 1] ++ [a + 1 | a <- args]) (max l $ height sym) iss
insert (Epsilon p q) (Automaton f b e fr l iss) = Automaton f' b' (S.insert (p,q) e) (maximum [fr, p + 1, q + 1]) l iss
  where
    f' = IM.map (IM.map $ M.map addForwardRight) f
    addForwardRight ps = if p `S.member` ps then S.insert q ps else ps
    b' = IM.map addBackwardRight b
    addBackwardRight mp = case IM.lookup p mp of
                           Just mp' -> addBackwardRight2 mp' mp
                           Nothing  -> mp
    addBackwardRight2 = IM.insertWith addBackwardRight3 q
    addBackwardRight3 = IM.unionWith S.union

    -- f'' = IM.map (IM.map addForwardLeft) f'
    --     addForwardLeft mp = foldr addForwardLeft2 mp (M.keys mp)
    --     addForwardLeft2 k mp = S.fold (addForwardLeft3 k) mp (modifiedArgs k)
    --     addForwardLeft3 k k' mp = M.insertWith S.union k' (fromJust $ M.lookup k mp) mp
    --     b'' = IM.map (IM.map $ IM.map $ S.unions . S.toList . S.map modifiedArgs) b'
    --     modifiedArgs []                  = S.singleton []
    --     modifiedArgs (q':qs) | q == q'   = let subresult = modifiedArgs qs in S.map ((:) p) subresult `S.union` S.map ((:) q) subresult
    --                          | otherwise = S.map ((:) q') $ modifiedArgs qs
    -- fwd = IM.map (IM.map fixFwd) f
    --   where
    --     fixFwd m = M.fromList [ (args',concatMapS clState rs) | (args,rs) <- M.toList m, args' <- clArgs args]

    -- bwd = IM.map fixBwd b
    --   where
    --     fixBwd m1 = IM.alter fixQ q m2
    --       where
    --         m2 = IM.map fixArgs m1
    --         fixQ Nothing = IM.lookup p m2
    --         fixQ (Just mq) =
    --           case IM.lookup p m2 of
    --            Nothing -> Just mq
    --            Just mp -> Just (mp `union` mq)
    --         union = IM.unionWith S.union

    --     fixArgs = IM.map (S.fromList . concatMap clArgs . S.toList)

    -- concatMapS f = S.fromList . concatMap f . S.toList
    -- clState r = if r == p then [r,q] else [r]
    -- clArgs []  = return []
    -- clArgs (a:as) = do
    --   a' <- clState a
    --   as' <- clArgs as
    --   return (a':as)


mkFreshState :: MonadState Automaton m => m State
mkFreshState = do a <- St.get
                  let (qi,a') = freshState a
                  St.put a'
                  return qi

mkInsertRule :: MonadState Automaton m => Rule -> m ()
mkInsertRule r = St.modify (insert r)


step :: Automaton -> LSym -> [State] -> Set State
-- q \in (step A f_l qs) <=> f_l(qs) -> q
step a (f,l) qs = fromMaybe S.empty look
 where look = do m1 <- IM.lookup (fromEnum f) (fwd a)
                 m2 <- IM.lookup l m1
                 M.lookup qs m2


bstep :: Automaton -> LSym -> State -> Set [State]
-- qs \in bstep f_l q <=> f_l(qs) -> q
bstep a (f,l) q = fromMaybe S.empty look
    where look = do m1 <- IM.lookup (fromEnum f) (bwd a)
                    m2 <- IM.lookup q m1
                    IM.lookup l m2


bstepUL :: Automaton -> Symbol -> State -> [(Label,Set [State])]
-- (l,[...,qs,...]) \in bstep f q <=> f_l(qs) -> q
bstepUL a f q = fromMaybe [] look
    where look = do m1 <- IM.lookup (fromEnum f) (bwd a)
                    m2 <- IM.lookup q m1
                    return $ IM.toList m2


rulesDefiningUL :: Automaton -> Symbol -> [(Label,[State], Set State)]
-- (l,qs,[...,q,...]) \in rulesDefining f <=> f_l(qs) -> q
rulesDefiningUL a f = fromMaybe [] look
 where look = do m1 <- IM.lookup (fromEnum f) (fwd a)
                 return [(l,qs,rs) | (l, m2) <- IM.toList m1
                                   , (qs,rs) <- M.toList m2]


rulesDefining :: Automaton -> LSym -> [([State], Set State)]
-- (qs,[...,q,...]) \in rulesDefining f_l <=> f_l(qs) -> q
rulesDefining a (f,l) = fromMaybe [] look
 where look = do m1 <- IM.lookup (fromEnum f) (fwd a)
                 m2 <- IM.lookup l m1
                 return $ M.toList m2

symbols :: Automaton -> Set LSym
symbols a = IM.foldrWithKey f S.empty (fwd a)
  where f fn m s = S.fromList [(toEnum fn,l) | l <- IM.keys m] `S.union` s

