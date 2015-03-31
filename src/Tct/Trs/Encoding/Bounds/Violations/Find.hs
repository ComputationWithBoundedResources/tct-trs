----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Method.Bounds.Violations.Find
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>,
--                Georg Moser <georg.moser@uibk.ac.at>,
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>,
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable
--
-- This module implements search for compatibility violations, as employed in
-- the bound processor.
----------------------------------------------------------------------------------

module Tct.Trs.Encoding.Bounds.Violations.Find where

import           Control.Monad                    (filterM, foldM, liftM)
import qualified Data.Map                         as M
import           Data.Maybe                       (fromMaybe)
import qualified Data.Set                         as S

import qualified Data.Rewriting.Rule              as R
import qualified Data.Rewriting.Term              as T

import qualified Tct.Trs.Data.Rewriting           as R

import           Tct.Trs.Encoding.Bounds.Automata




decidingLabel :: Ord v => Enrichment -> Strictness -> WeakBoundedness -> Label -> R.Rule f v -> LTerm -> Label
decidingLabel e str wb ml (R.Rule lhs rhs) = case e of {Top -> mtop; Match -> case str of {StrictRule -> mmatch; WeakRule -> mmatchrt}; Roof  -> mroof}
    where mtop   (F (_,l) _)    = l
          mtop   (S _)          = error "Bounds.decidingLabel.mtop: cannot determine label from state"
          mmatch (F (_,l) ts)   = minimum $ l:[ mmatch ti | ti <- ts, isFun ti ]
              where isFun (F _ _) = True
                    isFun _       = False
          mmatch (S _)          = error "Bounds.decidingLabel.mmatch: cannot determine label from state"
          mmatchrt t@(F (_,l) _) = if rtApplicable then applyMaxLabel (l - 1) else applyMaxLabel (mmatch t)
                                      where rtApplicable = (R.size lhs >= R.size rhs) && equalLabels t
                                            equalLabels (F (_,l') ts) = l == l' && all equalLabels ts
                                            equalLabels (S _) = True
                                            applyMaxLabel lab = case wb of
                                                                  WeakMayExceedBound -> lab
                                                                  WeakMayNotExceedBound -> min (ml - 1) lab
          mmatchrt (S _)         = error "Bounds.decidingLabel.mmatchrt: cannot determine label from state"
          mroof                  = mroof' lhs
              where mroof' (R.Fun _ ts) (F (_,l) lts) = minimum $ l:[ mroof' ti lti | (ti,lti) <- zip ts lts, isRoof ti ]
                    mroof'  _ _                       = error "Bounds.decidingLabel.mroof': called with strange arguments"
                    isRoof (R.Var _) = False
                    isRoof u       = rvars `S.isSubsetOf` R.tvars u
                    rvars = R.tvars rhs

reachableFromLifted :: Automaton -> T.Term Symbol v -> S.Set State -> S.Set (LTerm, State)
reachableFromLifted a t qs = runMemoAction reachableFromLiftedM
    where t' = identifyVars t
          reachableFromLiftedM = foldM (\ r q ->
                                            do lterms <- reachLiftS (t',q)
                                               return $ r `S.union` S.map (\ lt -> (lt,q)) lterms)
                                 S.empty $ S.toList qs
          reachLiftS (T.Var _,      q)   = return $ S.singleton $ S q
          reachLiftS s@(T.Fun f ts, q)   = memo (s,q) $
                                         foldM (\ lterms (l,args) ->
                                                     S.union lterms `liftM` labeledSubterms (f,l) (zip ts args))
                                          S.empty  [(l, args) | (l,argss) <- bstepUL a f q , args <- S.toList argss]
          labeledSubterms fl subproblems = do ltis <- mapM reachLiftS subproblems
                                              return $ S.fromList [F fl lts | lts <- listProduct $ map S.toList ltis]
              
          -- identifyVars (T.Var _) = T.Var (Var.canonical 0)
          identifyVars = T.map id (const (0::Int))
          -- TODO: MS what happens here
          -- identifyVars (T.Var _) = T.Var 0
          -- identifyVars (T.Fun f ts) = T.Fun f $ map identifyVars ts

reaches :: Automaton -> LTerm -> State -> MemoAction (LTerm,State) Bool Bool
reaches _ (S p) q | p == q  = return True
                  | otherwise = return False
reaches a (F fl lts) q2 = foldM f False (S.toList $ bstep a fl q2)
    where f True  _ = return True
          f False arg = foldM g True (zip lts arg)
          g False _ = return False
          g True (lti,qi) = memo (lti,qi) $ reaches a lti qi

findViolations :: Ord v => Automaton -> Enrichment -> Strictness -> WeakBoundedness -> Label -> R.Rule Symbol v -> S.Set (LTerm, State)
findViolations a e str wb ml rule = S.fromList $ runMemoAction $ filterM (\ (lt, q) -> not `liftM` candidateRejected lt q) candidates
    where candidates = snub [ (labeledRhs labeledLhs, q) | (labeledLhs, q) <- S.toList $ reachableFromLifted a l qs]
          candidateRejected lt q = ifM (reaches a lt q) (return True) (isTrivialEpsilon lt q)
          isTrivialEpsilon (F _ _) _ = return False
          isTrivialEpsilon (S p) q = return trivial
            where trivial = a == insert (Epsilon p q) a
          rt = case T.root l of Right f' -> f'; Left  _ -> error "Bounds.violations: Encountered variable on left-hand side"
          qs = S.unions [qs' | (_,_,qs') <- rulesDefiningUL a rt]
          l = R.lhs rule
          r = R.rhs rule
          labeledRhs labeledLhs = computeRhs (subst l labeledLhs) r
              where newLabel = decidingLabel e str wb ml rule labeledLhs + 1
                    subst (R.Var v)    (S s)     = M.singleton v s
                    subst (R.Fun _ ts) (F _ lts) = M.unions [subst ti lti | (ti,lti) <- zip ts lts]
                    subst _          _         = error "Bounds.violations: labeled term does not match left-hand side"
                    computeRhs s (R.Var v)       = S $ fromMaybe (error "Variables of right-hand side not included in variables of left-hand side") (M.lookup v s)
                    computeRhs s (R.Fun f ts)    = F (f,newLabel) [computeRhs s ti | ti <- ts]
