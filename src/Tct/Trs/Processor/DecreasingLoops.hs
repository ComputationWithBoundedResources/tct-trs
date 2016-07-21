-- | This module implements /Decreasing Loops/ for linear and exponential lower bounds.
-- See /Lower Bounds for Runtime Complexity of Term Rewriting/, Frohn et al. for more details.
module Tct.Trs.Processor.DecreasingLoops
  ( decreasingLoops
  , decreasingLoops'
  , decreasingLoopsDeclaration

  , Loop(..)
  ) where


import           Control.Applicative      ((<|>))
import           Control.Monad            (guard)
import           Data.Function            ((&))
import           Data.List                ((\\))
import qualified Data.Map                 as M
import           Data.Maybe               (fromMaybe)
import           Data.Monoid              ((<>))

import qualified Data.Rewriting.Pos       as R (parallelTo)
import           Data.Rewriting.Rule      (Rule (..))
import qualified Data.Rewriting.Rule      as R (rename, vars)
import           Data.Rewriting.Term      (Term (..))
import qualified Data.Rewriting.Term      as R (fold, isLinear, map, properSubterms, varsDL)

import           Tct.Core.Common.Pretty   ((<$$>), (<+>))
import qualified Tct.Core.Common.Pretty   as PP
import qualified Tct.Core.Common.Xml      as Xml
import qualified Tct.Core.Data            as T
import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem     as Prob (isInnermostProblem, isRCProblem, isRCProblem', startTerms,
                                                   allComponents, strictComponents)
import qualified Tct.Trs.Data.ProblemKind as Prob (isStartTerm)
import qualified Tct.Trs.Data.Rewriting   as R (narrow, narrowing, narrowings)
import qualified Tct.Trs.Data.Rules       as RS (toList)


data Loop' f v = Loop'
  { ctx       :: Term f v        -- ^ start/result context
  , startSub  :: [(v, Term f v)] -- ^ pumping substitution
  , resultSub :: [(v, Term f v)] -- ^ result substitution
  } deriving Show

data DecreasingLoop' f v = DecreasingLoop'
  { lterm :: Term f v  -- ^ start term
  , rctx  :: Term f v  -- ^ resulting term
  , rterm :: Term f v  -- ^ result term below some context
  , loop  :: Loop' f v -- ^ loop
  } deriving Show

data Omega' f v = Linear' (DecreasingLoop' f v) | Exponential' [DecreasingLoop' f v]
  deriving Show


--- * loop -----------------------------------------------------------------------------------------------------------

-- MS:
-- Definition 27 (Decreasing Loop)
-- `isLoop` assumes that l is a linear basic term and r not a variable
isLoop :: (Ord f, Ord v) => Term f v -> Term f v -> Maybe (Loop' f v)
isLoop l r = do
  lp  <- go l r
  guard $ not (null $ startSub lp)
  return lp

  where

  go (Fun f1 ts1) (Fun f2 ts2)
    | f1 == f2  = k <$> sequenceA (zipWith go ts1 ts2)
    | otherwise = Nothing
    where k ls = Loop'{ctx=Fun f1 (ctx `fmap` ls), startSub=startSub `concatMap` ls, resultSub=resultSub `concatMap` ls}

  go t1@Fun{} t2@(Var v2)
    | t2 `elem` R.properSubterms t1 = pure Loop'{ctx=t2, startSub=[(v2,t1)], resultSub=[]}
    | otherwise                     = Nothing

  go t1@(Var v1) (Var v2) | v1 == v2 = pure Loop'{ctx=t1, startSub=[], resultSub=[]}
  go t1@(Var v1) t2                  = pure Loop'{ctx=t1, startSub=[], resultSub=[(v1,t2)]}


--- * linear ---------------------------------------------------------------------------------------------------------

isLinear :: (Ord f, Ord v) => Term f v -> Term f v -> Term f v -> Maybe (Omega' f v)
isLinear l r r1 = (\lp -> Linear' DecreasingLoop'{lterm=l,rctx=r,rterm=r1,loop=lp}) <$> isLoop l r1

anyLinear :: (Ord f, Ord v) => Term f v -> Term f v -> Maybe (Omega' f v)
anyLinear l@(Fun f _) r = alternative (isLinear l r) (fSubterms r) where
  fSubterms t@(Fun f' ts)
    | f' == f   = t: concatMap fSubterms ts
    | otherwise = concatMap fSubterms ts
  fSubterms _ = []
anyLinear _ _           = Nothing


--- * exponential ----------------------------------------------------------------------------------------------------

isExponential :: (Ord f, Ord v, Show f, Show v) => Term f v -> Term f v -> Term f v -> Term f v -> Maybe (Omega' f v)
isExponential l r r1 r2 = do
  lp1 <- isLoop l r1
  lp2 <- isLoop l r2
  guard $
    startSub lp1 `commutesWith` startSub lp2
    && resultSub lp1 `notInferesWith` startSub lp2
    && resultSub lp2 `notInferesWith` startSub lp1
  return $ Exponential'
    [ DecreasingLoop'{lterm=l,rctx=r,rterm=r1,loop=lp1}
    , DecreasingLoop'{lterm=l,rctx=r,rterm=r2,loop=lp2}]
  where

  s1 `notInferesWith` s2 = null $ map fst s1 \\ foldr (R.varsDL . snd) [] s2
  s1 `commutesWith` s2   = M.fromList (compose s1 s2) == M.fromList (compose s2 s1)

  compose s1 s2 = fmap (apply s2) `fmap` s1
  apply s    = R.fold (\v -> Var v `fromMaybe` lookup v s) Fun

anyExponential :: (Ord f, Ord v, Show f, Show v) => Term f v -> Term f v -> Maybe (Omega' f v)
anyExponential l@(Fun f _) r = alternative (uncurry (isExponential l r)) (parallelfSubterms r) where
  parallelfSubterms t =
    [ (oPos t1, oPos t2)
      | let t' = wPos t
      , t1@(Fun (f1,p1) _) <- R.properSubterms t'
      , t2@(Fun (f2,p2) _) <- R.properSubterms t'
      , f1 == f
      , f2 == f
      , p1 `leftOf` p2 ]

  p1 `leftOf` p2 =
    let
      p1' = reverse p1
      p2' = reverse p2
    in p1' < p2' && p1' `R.parallelTo` p2'
  wPos t = go t [0] where
    go (Fun g ts) p = Fun (g,p) (zipWith (\s i -> go s (i:p)) ts [0..])
    go (Var v)    _ = Var v
  oPos = R.map fst id
anyExponential _ _           = Nothing


--- * processor ------------------------------------------------------------------------------------------------------

data Loop = AnyLoop | LinearLoop | ExponentialLoop
  deriving (Show, Enum, Bounded)

data DecreasingLoops = DecreasingLoops
  { bound  :: Loop
  , narrow :: Int
  } deriving Show

-- MS: output is not really good it, it would be nice to display
-- * the context
-- * the corresponding rewriting/narrowing sequence
data DecreasingLoopsProof = DecreasingLoopsProof (Omega' F V')
  deriving Show

instance T.Processor DecreasingLoops where
  type ProofObject DecreasingLoops = DecreasingLoopsProof
  type In  DecreasingLoops         = Trs
  type Out DecreasingLoops         = Trs
  type Forking DecreasingLoops     = T.Judgement

  execute p prob = maybe decreasing T.abortWith (Prob.isRCProblem' prob) where

    decreasing = case entscheide p prob of
      Nothing -> T.abortWith "Incompatible"
      Just lp -> T.succeedWith0 (DecreasingLoopsProof lp) (T.judgement $ T.timeLBCert bnd)
        where bnd = case lp of {Linear' _ -> T.linear; Exponential' _ -> T.Exp Nothing}


newtype V' = V' Int deriving (Eq, Ord, Enum, Num)

instance Show V'      where show   (V' i) = "x_" <> show i
instance PP.Pretty V' where pretty (V' i) = maybe (PP.text "x_" <> PP.int i ) PP.char $ lookup i (zip [0..] ['x','y','z','u','v','w'])

alternative :: (a -> Maybe b) -> [a] -> Maybe b
alternative f = foldr (<|>) Nothing . fmap f

find :: Eq a => a -> [(a,b)] -> b
find a = fromMaybe err . lookup a
  where err = error "Tct.Processor.DecreasingLoops.find: not found"

-- MS: extensions (not implemented):
-- * runtime innermost:
--   variants of narrowing that (under-approximattes) innermost rewriting (eg non-overlapping narrowing)
-- * relative setting:
--   in principle only one rewrite step has to be strict, ie l ->=* . ->+ . ->=* C[r]
-- * non-left linear start term:
--   ok when corresponding variables only appear in the context, eg Various04_18.xml : +(*(x,y),*(x,z)) -> *(x,+(y,z))
-- * reachable term:
--   generalise to l' ->+ l ->+ C[r]
entscheide :: (Ord f, Ord v, Show f, Show v) => DecreasingLoops -> Problem f v -> Maybe (Omega' f V')
entscheide DecreasingLoops{bound=bnd,narrow=nrw} prob 
  | not (Prob.isRCProblem prob)             = Nothing
  | Prob.isInnermostProblem prob || nrw < 0 = search bnd 0
  | otherwise                               = search bnd nrw
  where

  normalise r = R.rename (flip find $ zip (R.vars r) [V' 0..]) r
  allrules    = normalise `fmap` RS.toList (Prob.allComponents prob)
  startrules  = normalise `fmap` RS.toList (Prob.strictComponents prob) & filter f
    where f Rule{lhs=l} = R.isLinear l && Prob.isStartTerm (Prob.startTerms prob) l

  rename      = R.rename (either (succ . (*2)) (*2))
  narrowings r = (rename . R.narrowing) `fmap` (R.narrowings `concatMap`  R.narrow r allrules)

  gen 0 rs = rs
  gen 1 _  = []
  gen n rs = rs ++ gen (n-1 :: Int) (concatMap narrowings rs)

  k f Rule{lhs=l,rhs=r} = f l r
  search ExponentialLoop nrws = alternative (k anyExponential) (gen nrws startrules)
  search LinearLoop      nrws = alternative (k anyLinear)      (gen nrws startrules)
  search AnyLoop         nrws = alternative (k anyExponential) startrules            <|> alternative (k anyLinear) (gen nrws startrules)


--- * instances ------------------------------------------------------------------------------------------------------

boundArg :: T.Argument 'T.Required Loop
boundArg = T.flag "loop" [ "This argument specifies which bound to search for." ]

narrowArg :: T.Argument 'T.Required T.Nat
narrowArg = T.nat "narrow" [ "This argument specifies how many narrowing should be applied." ]


decreasingLoopsDeclaration :: T.Declaration ('[T.Argument 'T.Optional Loop, T.Argument 'T.Optional T.Nat] T.:-> TrsStrategy)
decreasingLoopsDeclaration =
  T.declare
    "decreasingLoops"
    ["Tries to find decreasing loops."]
    (boundArg `T.optional` AnyLoop, narrowArg `T.optional` 10)
    (\bnd nrw -> T.processor DecreasingLoops{bound=bnd,narrow=nrw})

decreasingLoops :: TrsStrategy
decreasingLoops = T.deflFun decreasingLoopsDeclaration

decreasingLoops' :: Loop -> Int -> TrsStrategy
decreasingLoops' = T.declFun decreasingLoopsDeclaration


--- * proofdata ------------------------------------------------------------------------------------------------------

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Omega' f v) where
  pretty lp =
    PP.text "The system has following decreasing Loops:"
    <$$> PP.indent 2 (PP.vcat $ PP.pretty `fmap` lps)
    where lps = case lp of {Linear' ls -> [ls]; Exponential' ls -> ls}

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (DecreasingLoop' f v) where
  pretty DecreasingLoop'{lterm=l,rctx=r,rterm=r1,loop=lp} =
    PP.pretty (ctx lp) <> ppSub (startSub lp)
    <+> PP.char '='
    <$$>PP.indent 2 (
        PP.pretty l
      <+> PP.text "->^+"
      <+> PP.pretty r
      <$$>PP.indent 2 (
            PP.char '='
        <+> PP.char 'C'
        <>  PP.enclose PP.lbracket PP.rbracket
            (PP.pretty r1
            <+> PP.char '='
            <+>  PP.pretty (ctx lp) <> ppSub (resultSub lp))))
    where
      ppSub s    = PP.encloseSep PP.lbrace PP.rbrace PP.comma $ ppTo `fmap` s
      ppTo (v,t) = PP.pretty v <+> PP.text "->" <+> PP.pretty t


instance Xml.Xml DecreasingLoopsProof   where toXml = const Xml.empty
instance PP.Pretty DecreasingLoopsProof where pretty (DecreasingLoopsProof dl)= PP.pretty dl

