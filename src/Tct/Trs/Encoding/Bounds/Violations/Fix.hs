----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Processor.Bounds.Violations.Fix
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
--
-- This module implements fixing of compatibility violations, as employed in
-- the bound processor.
----------------------------------------------------------------------------------


{-# LANGUAGE FlexibleContexts #-}
module Tct.Trs.Encoding.Bounds.Violations.Fix where

import Control.Monad (foldM)
import Control.Monad.State.Lazy (StateT(..))
import Data.Set (Set)
import Prelude hiding (fail)
import qualified Control.Monad.State.Lazy as State
import qualified Control.Monad.Trans as Trans
import qualified Data.List as List
import qualified Data.Set as Set

import Tct.Trs.Encoding.Bounds.Automata


type MemoReachable = MemoAction LTerm (Set State)

reachableStates :: Automaton -> LTerm -> MemoReachable (Set State)
reachableStates _ (S q)    = return $ Set.singleton q
reachableStates a  t = memo t $ reachableStates' t
    where reachableStates' (F f ts) = do qss <- mapM (reachableStates a) ts
                                         let rewrites args = all (\ (qs, arg) -> Set.member arg qs) $ zip qss args
                                         return $ Set.unions [ ps | (args,ps) <- rulesDefining a f, rewrites args ]
          reachableStates' (S q)    = return $ Set.singleton q


data Problem
  = Reach (LTerm) State
  | Add (Rule)
  deriving (Eq, Ord)

type Constraint = Set (Set Problem)

oneOf :: [Constraint] -> Constraint
oneOf = Set.unions

requireAll :: [Problem] -> Constraint
requireAll = Set.singleton . Set.fromList

qed :: Constraint
qed = oneOf [requireAll []]

fail :: Constraint
fail = oneOf []

isBot :: Constraint -> Bool
isBot = Set.null


isReducibleProblem :: Problem -> Bool
isReducibleProblem (Reach _ _) = True
isReducibleProblem (Add _) = False

isReducibleConstraint :: Constraint -> Bool
isReducibleConstraint = not . Set.null . Set.filter (not . Set.null . Set.filter isReducibleProblem)

replaceProblem :: Problem -> Constraint -> Constraint -> Constraint
replaceProblem p newpss pss = otherDisjuncts `Set.union` newDisjuncts
  where fittingDisjunct = Set.findMin $ Set.filter (Set.member p) pss
        otherDisjuncts  = Set.delete fittingDisjunct pss
        newDisjuncts    = Set.map (Set.union (Set.delete p fittingDisjunct)) newpss


type ReductionRule = Problem -> StateT Automaton MemoReachable Constraint

rule1 :: ReductionRule
rule1 (Reach t q) = do a <- State.get
                       qs <- Trans.lift $ reachableStates a t
                       return $ if Set.member q qs then qed else fail
rule1 _          = return fail

rule2 :: ReductionRule
rule2 (Reach (S p) q) | p == q    = return qed
                      | otherwise = return $ requireAll [Add $ Epsilon p q]
rule2 _          = return fail

rule3 :: ReductionRule
rule3 (Reach (F f ts) q) =
    do a <- State.get
       qss <- Trans.lift $ mapM (reachableStates a) ts
       let isApplicable args = all (\ (ai,qs) -> Set.member ai qs || Set.null qs) $ zip args qss
           argss = filter isApplicable $ Set.toList $ bstep a f q
       return $ oneOf $ map mkConstraint argss
    where mkConstraint args = requireAll $ zipWith Reach ts args
rule3  _                 = return fail

rule4 :: ReductionRule
rule4 (Reach (F f ts) q) =
    do a <- State.get
       qss <- Trans.lift $ mapM (reachableStates a) ts
       (revargs,problems) <- foldM mk ([],[]) $ zip ts qss
       return $ requireAll $ (Add $ Collapse f (reverse revargs) q) : problems -- MA:TODO verify 
    where mk (args,probs) (ti, qs) | Set.null qs = do qi <- mkFreshState
                                                      return (qi : args, Reach ti qi : probs)
                                   | otherwise   = return (selectSt qs : args, probs)
          selectSt = Set.findMax
rule4 _ = return fail


type DisjunctSelector = Constraint -> StateT Automaton MemoReachable [Problem]
type ProblemSelector = Constraint -> StateT Automaton MemoReachable Problem
type ProblemCutter = Constraint -> StateT Automaton MemoReachable Constraint


applyRule :: ProblemSelector -> ProblemCutter -> Constraint -> StateT Automaton MemoReachable Constraint
applyRule selProb cutProb pss = do p <- selProb pss
                                   newpss <- applyFirst p [rule1, rule2, rule3, rule4]
                                   let pss' = replaceProblem p newpss pss
                                   cutProb pss'
    where applyFirst p []     = return $ requireAll [p]
          applyFirst p (r:rs) = r p >>= \ res -> if isBot res then applyFirst p rs else return res


realise :: [Problem] -> StateT Automaton MemoReachable ()
realise = mapM_ handleProblem
    where  handleProblem (Reach _ _) = error "Bounds.Violation.realise: Argument Reach not allowed in handleProblem."
           handleProblem (Add r)     = State.modify $ insert r

reduceConstraint :: DisjunctSelector -> ProblemSelector -> ProblemCutter -> Constraint -> StateT Automaton MemoReachable ()
reduceConstraint selDis selProb cutProb pss | isReducibleConstraint pss = do newpss <- applyRule selProb cutProb pss
                                                                             reduceConstraint selDis selProb cutProb newpss
                                            | otherwise                 = selDis pss >>= realise

isViolation :: (LTerm, State) -> StateT Automaton MemoReachable Bool
isViolation (S p, q) = do a <- State.get
                          return $ a /= insert (Epsilon p q) a
isViolation (t, q) =
    do a <- State.get
       qs <- Trans.lift $ reachableStates a t
       return $ not $ Set.member q qs

-- deterministic rule insertion

-- f(g(1,a)) auf leeren automaten
-- fuegt hinzu als preprocessing hinzu :
--  a -> fresh1 ; g(1,fresh1) -> fresh2 ...

simplify :: LTerm -> State.State Automaton LTerm
simplify (S q) = return $ S q
simplify (F f_l ts) =
    do ts' <- mapM simplify ts
       case mkArgs ts' of
         Nothing   -> return $ F f_l ts'
         Just args -> do a <- State.get
                         case Set.toList $ step a f_l args of
                           []  -> return $ F f_l ts'
                           [q] -> return $ S q
                           _   -> return $ F f_l ts'
    where mkArgs = foldr f (Just [])
              where f (S q) (Just args) = Just (q : args)
                    f _     _           = Nothing
-- AS: vollkommen effektlos; aufgrund des frischen Zustandes werden mit
--     insertRule zwar keine neuen Simplifikationen anwendbar, aber der
--     Automat um einen Zustand und eine Regel verkompliziert
--           insertRule args = do q <- mkFreshState
--                                mkInsertRule (Collapse f_l args q)
--                                return (S q)

fixViolation :: Automaton -> (LTerm, State) -> Automaton
fixViolation a (t, q) = runMemoAction $ State.execStateT m a'
    where a' = State.execState (simplify t) a
          m = ifM (isViolation (t,q)) handleViolation (return ())
          handleViolation = reduceConstraint stdSelDis stdSelProb stdCutProb $ requireAll [Reach t q]
          stdSelDis = selectCheapestDisjunct
          stdSelProb = selectFirstProblem
          stdCutProb = cutNothing -- cutToCheapestConstraints 3


selectFirstDisjunct :: DisjunctSelector
selectFirstDisjunct = return . Set.toList . Set.findMin

selectCheapestDisjunct :: DisjunctSelector
selectCheapestDisjunct pss = return $ Set.toList $ List.minimumBy comp $ Set.toList pss
  where comp p q = compLex (getCost p) (getCost q)
        compLex (p, q) (p', q') = let firstComp = compare p p' in if firstComp == EQ then compare q q' else firstComp
        getCost ps = let (eps, col) = Set.partition isEpsilonRule $ Set.map addToRule ps in (Set.size eps, Set.size col)
        addToRule (Reach _ _) = error "Bounds.Violation.selectCheapestDisjunct: Argument Reach not allowed in addToRule"
        addToRule (Add r) = r

selectFirstProblem :: ProblemSelector
selectFirstProblem pss = return $ Set.findMin $ Set.filter isReducibleProblem $ Set.findMin reducibleDisjuncts
  where reducibleDisjuncts = Set.filter (not . Set.null . Set.filter isReducibleProblem) pss

cutToCheapestConstraints :: Int -> ProblemCutter
cutToCheapestConstraints n pss = return $ Set.fromList $ take n $ List.sortBy comp $ Set.toList pss
  where comp p q = compLex (getCost p) (getCost q)
        compLex (p, q) (p', q') = let firstComp = compare p p' in if firstComp == EQ then compare q q' else firstComp
        getCost ps = let (adds, reas) = Set.partition isAdd ps in
                     let (eps, col) = Set.partition isEpsilonRule $ Set.map addToRule adds in
                     (Set.size eps, Set.size col + Set.fold (\p k -> k + countFuns p) 0 reas)
        countFuns (Reach t _) = size t
        countFuns (Add _) = error "Bounds.Violation.cutToCheapestConstraints: Argument Add not allowed in countFuns"
        isAdd (Add _) = True
        isAdd (Reach _ _) = False
        addToRule (Reach _ _) = error "Bounds.Violation.cutToCheapestConstraints: Argument Reach not allowed in addToRule"
        addToRule (Add r) = r

cutToFirstDisjunct :: ProblemCutter
cutToFirstDisjunct = return . Set.singleton . Set.findMin

cutNothing :: ProblemCutter
cutNothing = return

