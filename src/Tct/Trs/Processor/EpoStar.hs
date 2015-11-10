{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- Implementation details can be found in the technical report 'http://arxiv.org/pdf/1010.1128v3.pdf'.
-- | This module provides the \EpoStar\ processor.
module Tct.Trs.Processor.EpoStar
  ( epoStarDeclaration
  , epoStar
  , epoStar'

  , ExtComp (..)
  , extCompArg
  ) where


import           Control.Applicative
import           Control.Monad
import qualified Data.Array                   as Ar
import qualified Data.Foldable                as F (foldr)
import qualified Data.Map.Strict              as M
import           Data.Maybe                   (fromMaybe)
import           Data.Monoid                  ((<>))
import qualified Data.Set                     as S
import           Data.Typeable

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           SLogic.Smt.Solver            (minismt)

import qualified Data.Rewriting.Rule          as R (lhs, rhs)
import qualified Data.Rewriting.Term          as R

import           Tct.Common.ProofCombinators
import           Tct.Common.SMT               ((.&&), (.<=>), (.=<), (.==), (.=>), (.>), (.||))
import qualified Tct.Common.SMT               as SMT

import           Tct.Trs.Data
import           Tct.Trs.Data.Precedence      (Order (..), Precedence (..))
import qualified Tct.Trs.Data.Precedence      as Prec
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.Rewriting       as R (directSubterms)
import qualified Tct.Trs.Data.Signature       as Sig
import qualified Tct.Trs.Data.Rules as RS
import qualified Tct.Trs.Encoding.SafeMapping as SM


newtype EpoStar = EpoStar { extComp_ :: ExtComp } deriving Show

data ExtComp = ExtComp | NoExtComp deriving (Bounded, Enum, Eq, Typeable, Show)

useExtComp :: ExtComp -> Bool
useExtComp = (ExtComp==)

data EpoStarProof f v = EpoStarProof
  { stricts_             :: Rules f v          -- ^ The oriented input TRS.
  , safeMapping_         :: SM.SafeMapping f -- ^ The safe mapping.
  , precedence_          :: Precedence f     -- ^ The precedence.
  , argumentPermutation_ :: MuMapping f      -- ^ Employed argument permutation.
  , signature_           :: Signature f      -- ^ Signature underlying 'epoInputTrs'
  } deriving Show

instance T.Processor EpoStar where
  type ProofObject EpoStar = ApplicationProof (OrientationProof (EpoStarProof F V))
  type In  EpoStar         = Trs
  type Out EpoStar         = Trs
  type Forking EpoStar     = T.Judgement

  execute p prob =
    maybe epo (\s -> T.abortWith (Inapplicable s :: ApplicationProof (OrientationProof (EpoStarProof F V)))) maybeApplicable
    where

      maybeApplicable = Prob.isRCProblem' prob <|> Prob.isInnermostProblem' prob <|> RS.isConstructorTrs' sig trs

      trs    = Prob.allComponents prob
      sig    = Prob.signature prob
      -- solver = SMT.smtSolveTctM prob
      solver = minismt

      epo = do
        res <- entscheide solver trs sig (extComp_ p)
        case res of
          SMT.Sat m -> T.succeedWith0 (Applicable . Order $ nproof m) (const $ T.timeUBCert (T.Exp Nothing))
          _         -> T.abortWith (Applicable (Incompatible :: OrientationProof (EpoStarProof F V)))

      nproof (prec,safe,mu) = EpoStarProof
        { stricts_             = trs
        , safeMapping_         = safe
        , precedence_          = prec
        , argumentPermutation_ = mu
        , signature_           = sig }


find :: Ord k => k -> M.Map k v -> v
find e = fromMaybe (error "EpoStar.find") . M.lookup e


--- * precedence encoding --------------------------------------------------------------------------------------------

data PrecedenceEncoder f w = PrecedenceEncoder
  (Precedence f)          -- ^ initial precedence
  (M.Map f (SMT.IExpr w)) -- ^ a (bounded) integer variable for each defined symbol

precedenceEncoder :: (SMT.Fresh w, Ord f) => Signature f -> SMT.SmtSolverSt w (PrecedenceEncoder f w)
precedenceEncoder sig = PrecedenceEncoder (Prec.empty sig) . M.fromList <$> mapM bounded (S.toList ds)
  where
    bounded f = do v <- SMT.ivarM'; SMT.assert (v .> SMT.zero .&& v .=< SMT.num k); return (f,v)
    ds        = Sig.defineds sig
    k         = S.size ds

precedence :: Ord f => PrecedenceEncoder f w -> Order f -> SMT.Formula w
precedence (PrecedenceEncoder (Precedence (sig,_)) fm) (f :>: g)
  | f == g                   = SMT.bot
  | Sig.isConstructor f sig  = SMT.bot
  | Sig.isConstructor g sig  = SMT.top
  | otherwise                = find f fm .> find g fm
precedence (PrecedenceEncoder (Precedence (sig,_)) fm) (f :~: g)
  | f == g        = SMT.top
  | cf && cg      = SMT.top
  | cf && not cg  = SMT.bot
  | not cf && cg  = SMT.bot
  | otherwise     = find f fm .== find g fm
  where
    cf = Sig.isConstructor f sig
    cg = Sig.isConstructor g sig

instance (Ord f, SMT.Storing w) => SMT.Decode (SMT.Environment w) (PrecedenceEncoder f w) (Precedence f) where
  decode (PrecedenceEncoder (Precedence (sig,_)) fm) = do
    fis :: [(f,Int)] <- M.assocs <$> SMT.decode fm
    return $ Precedence (sig,  gts fis ++ eqs fis)
    where
      gts fis = [ f:>:g | (f,i) <- fis, (g,j) <- fis, i > j ]
      eqs fis = [ f:~:g | (f,i) <- fis, (g,j) <- fis, i == j  ]


--- * safe mapping ---------------------------------------------------------------------------------------------------

data SafeMappingEncoder f w = SafeMappingEncoder
  (SM.SafeMapping f)              -- ^ initial safe mapping
  (M.Map (f,Int) (SMT.Formula w)) -- ^ variable safe_f_i for defined symbol f and argument position i

safeMappingEncoder :: (SMT.Fresh w, Ord f) => Signature f -> SMT.SmtSolverSt w (SafeMappingEncoder f w)
safeMappingEncoder sig = SafeMappingEncoder (SM.empty sig) <$> sfm
  where
    sfm    = M.fromList <$> mapM bvar [ (f,i) | f <- S.toList (Sig.defineds sig), i <- Sig.positions sig f ]
    bvar k = SMT.bvarM' >>= \v -> return (k,v)

safeMapping :: Ord f => SafeMappingEncoder f w -> f -> Int -> SMT.Formula w
safeMapping (SafeMappingEncoder (SM.SafeMapping (sig,_)) sfm) f i
  | Sig.isConstructor f sig = SMT.top
  | otherwise               = find (f,i) sfm

instance (Ord f, SMT.Storing w) => SMT.Decode (SMT.Environment w) (SafeMappingEncoder f w) (SM.SafeMapping f) where
  decode (SafeMappingEncoder sf sfm) = do
    sfs :: S.Set (f,Int) <- SMT.decode (SMT.Property (fromMaybe False) sfm)
    return $ F.foldr (uncurry SM.setSafe) sf sfs


--- * mu mapping -----------------------------------------------------------------------------------------------------

newtype MuMapping f = MuMapping (M.Map f [Int]) deriving Show

-- mu_f,i,k = mu(f,i)=k
newtype MuMappingEncoder f w = MuMappingEncoder (M.Map f (Ar.Array (Int,Int) (SMT.Formula w)))

muMappingEncoder :: (SMT.Fresh w, Ord f) => Signature f -> SMT.SmtSolverSt w (MuMappingEncoder f w)
muMappingEncoder sig = MuMappingEncoder . M.fromList <$> mapM bijection (Sig.elems sig)
  where
    bijection (f,af) = do
      let ((u,l),(o,r)) = ((1,1),(af,af))
      ar <- Ar.listArray ((u,l),(af,af)) <$> replicateM (af*af) SMT.bvarM'

      sequence_ $ do
        x <- Ar.range (u,o)
        return $ SMT.assert $ exactlyOne1 (ar,l,r) x $ do y <- Ar.range (l,r); return (ar Ar.! (x,y))
      sequence_ $ do
        x <- Ar.range (u,o)
        return $ SMT.assert $ exactlyOne2 (ar,l,r) x $ do y <- Ar.range (l,r); return (ar Ar.! (y,x))

      return (f,ar)

    exactlyOne1 (ar,l,r) x vs = SMT.bigOr vs .&& 
      SMT.bigAnd [ SMT.bigAnd [ SMT.bnot (ar Ar.! (x,i)) .|| SMT.bnot (ar Ar.! (x,j)) | j <- [i+1..r] ] | i <- [l..r-1] ]
    exactlyOne2 (ar,l,r) x vs = SMT.bigOr vs .&& 
      SMT.bigAnd [ SMT.bigAnd [ SMT.bnot (ar Ar.! (i,x)) .|| SMT.bnot (ar Ar.! (j,x)) | j <- [i+1..r] ] | i <- [l..r-1] ]


muMapping :: Ord f => MuMappingEncoder f w -> f -> (Int, Int) -> SMT.Formula w
muMapping (MuMappingEncoder fm) f ix = find f fm Ar.! ix

instance (Ar.Ix i, SMT.Decode m c a) => SMT.Decode m (Ar.Array i c) (Ar.Array i a) where
  decode ar = Ar.array bnds <$> mapM ( \(i,a) -> SMT.decode a >>= \c -> return (i,c) ) (Ar.assocs ar)
    where bnds = Ar.bounds ar

instance (Ord f, SMT.Storing w) => SMT.Decode (SMT.Environment w) (MuMappingEncoder f w) (MuMapping f) where
  decode (MuMappingEncoder fm) = do
    fa :: M.Map f (Ar.Array (Int,Int) Bool) <- SMT.decode fm
    return $ MuMapping $ (\ar -> foldr set [] $ Ar.assocs ar) `fmap` fa
    where
      set (_, False) is   = is
      set ((_,k),True) is = k:is


--- * orient ---------------------------------------------------------------------------------------------------------

data EpoOrder  f v
  = Epo (R.Term f v) (R.Term f v)
  | Eposub (R.Term f v) (R.Term f v)
  | Eq (R.Term f v) (R.Term f v)
  deriving (Eq, Ord)

unorientable :: (Ord f, Ord v) => Signature f -> R.Term f v -> R.Term f v -> Bool
unorientable sig u v =
  varsS u `S.isProperSubsetOf` varsS v
  || (isConstructorTerm u && not (isConstructorTerm v))
  where
    varsS = S.fromList . R.vars
    isConstructorTerm = all (`Sig.isConstructor` sig) . R.funs

entscheide :: (Functor m, Monad m, Ord f, Ord v, Show f, Show v) =>
  SMT.SmtSolver m Int
  -> Rules f v
  -> Signature f
  -> ExtComp
  -> m (SMT.Result (Precedence f, SM.SafeMapping f, MuMapping f))
entscheide solver trs sig ecomp = do
  res :: SMT.Result (Precedence f, SM.SafeMapping f, MuMapping f) <- SMT.smtSolveSt solver $ do
    SMT.setLogic SMT.QF_LIA

    sfenc <- safeMappingEncoder sig
    prenc <- precedenceEncoder sig
    muenc <- muMappingEncoder sig

    let
      safe = safeMapping sfenc
      prec = precedence prenc
      mu = muMapping muenc
      epo s t = orient (useExtComp ecomp) sig prec safe mu (Epo s t)
      -- epoM s t = orientM (useExtComp ecomp) sig prec safe mu (Epo s t)

    SMT.assert $ SMT.bigAnd [ R.lhs r `epo` R.rhs r | r <- rs  ]
    -- SMT.assert =<< fst <$> SMT.memo (SMT.bigAndM [ R.lhs r `epoM` R.rhs r | r <- rs  ])
    -- consistency (5)
    SMT.assert $ SMT.bigAnd
      [
        prec (f:~:g) .=> SMT.bigAnd
          [
            (mu f (i,k) .&& mu g (j,k)) .=> (safe f i .<=> safe g j)
          | i <- [1..af], j <- [1..af], k <- [1..af] ]

      | let ds = S.toList (Sig.defineds sig), f <- ds, g <- ds, let af = Sig.arity sig f, af == Sig.arity sig g ]

    return $ SMT.decode (prenc, sfenc, muenc)
  return $ res
    where
      rs = RS.toList trs

orient :: (Show v, Show f, Ord v, Ord f) =>
  Bool
  -> Signature f
  -> (Order f -> SMT.Formula w)
  -> (f -> Int -> SMT.Formula w)
  -> (f -> (Int, Int) -> SMT.Formula w)
  -> EpoOrder f v -> SMT.Formula w
orient allowEcomp sig prec safe mu a =
  case a of
    Epo s t    -> s `epoimp` t
    Eposub s t -> s `eposubimp` t
    Eq s t     -> s `equivimp` t
  where
    ite g t e = SMT.implies g t `SMT.band` SMT.implies (SMT.bnot g) e
    unsatisfiable u v = unorientable sig u v

    s `epo` t    = orient allowEcomp sig prec safe mu (Epo s t)
    s `eposub` t = orient allowEcomp sig prec safe mu (Eposub s t)
    s `equiv` t  = orient allowEcomp sig prec safe mu (Eq s t)

    -- epo: s >epo* t
    u `epoimp` v
      | u `isProperSupertermOf` v = SMT.top
      | unorientable sig u v      = SMT.bot
      | otherwise                 = SMT.bigOr [u `epo1` v, u `epo23` v]
      where
        isProperSupertermOf s t = any (t==) (concatMap R.subterms $ R.directSubterms s)

        epo1 (R.Fun _ ss) t = SMT.bigOr [ SMT.bigOr [si `epo` t, si `equiv` t] | si <- ss ]
        epo1 _            _ = SMT.bot

        epo23 s@(R.Fun f ss) (R.Fun g ts) =
          SMT.bigAnd
          [ SMT.bigOr  [ prec $ f:>:g, epo3 ]
          , SMT.bigAnd [ ite (safe g i) (s `epo` ti) (s `eposub` ti) | (i,ti) <- tsi ] ]
          where
            ssi = [ (i, si) | i <- [1..] | si <- ss ]
            tsi = [ (i, ti) | i <- [1..] | ti <- ts ]
            epo3
              | Sig.isDefined g sig && not (null ss) && length ss == length ts = SMT.bigAnd [ prec (f:~:g), epolex 1 ]
              | otherwise                                                      = SMT.bot
            epolex k
              | length ssi < k = SMT.bot
              | otherwise      = SMT.bigAnd [
                let
                  rec  = epolex (k+1)
                  comp = SMT.bigOr [ si `eposub` tj, SMT.bigAnd [si `equiv` tj, rec] ]
                in
                SMT.bigAnd [mu f (i,k), mu g (j,k)] `SMT.implies` ite (safe g j) rec comp
                | (i, si) <- ssi, (j, tj) <- tsi]
        epo23 _ _ = SMT.bot

    -- eposub: s \sqltepo t
    u `eposubimp` v
      | unsatisfiable u v = SMT.bot
      | otherwise         = SMT.bigOr [ u `eposub1` v, u `eposub2` v ]
      where

        (R.Fun f ss) `eposub1` t = SMT.bigOr [ SMT.bigAnd [maybeNormal i, SMT.bigOr [si `eposub` t, si `equiv` t]] | i <- [1..] | si <- ss]
          where
            maybeNormal i
              | Sig.isDefined f sig = SMT.bnot $ safe f i
              | otherwise           = SMT.top
        _ `eposub1` _ = SMT.bot

        -- special case: with extended composition
        s@(R.Fun f _) `eposub2` (R.Fun g ts)
          | allowEcomp = SMT.bigAnd [ prec (f:>:g) , SMT.bigAnd [ SMT.bigAnd [ safe g i, s `eposub` ti] | i <- [1..] | ti <- ts] ]
          | otherwise  = SMT.bot
        _ `eposub2` _ = SMT.bot

    -- equivalence: s ~ t modulo mu
    u `equivimp` v
      | u == v            = SMT.top
      | unsatisfiable u v = SMT.bot
      | otherwise         = case (u,v) of
        (R.Var _ , R.Var _) -> SMT.bot
        (R.Fun f ss, R.Fun g ts)
          | unsat           -> SMT.bot
          | otherwise       -> SMT.bigAnd
            [ prec (f:~:g)
            , SMT.bigAnd
              [ SMT.bigAnd [mu f (i,k), mu g (j,k)] `SMT.implies` (si `equiv` tj)
              | (i,si) <- zip [1..] ss, (j,tj) <- zip [1..] ts, k <- [1..length ss] ]
            ]
          where unsat = length ss /= length ts || (Sig.isConstructor f sig /= Sig.isConstructor g sig)
        _              -> SMT.bot

-- FIXME: MS monadic/memoised version has a memory problem
-- it doesn't affect the outcome on the (used) testbed
-- orientM :: (Show v, Show f, Ord v, Ord f, Monad m) =>
--   Bool
--   -> Signature f
--   -> (Order f -> SMT.Formula w)
--   -> (f -> Int -> SMT.Formula w)
--   -> (f -> (Int, Int) -> SMT.Formula w)
--   -> EpoOrder f v -> SMT.Memo (EpoOrder f v) (SMT.Formula w) m (SMT.Formula w)
-- orientM allowEcomp sig prec safe mu = SMT.memoized $ \a ->
--   case a of
--     Epo s t    -> s `epoimp` t
--     Eposub s t -> s `eposubimp` t
--     Eq s t     -> s `equivimp` t
--   where
--     precM = return . prec
--     safeM g = return . safe g
--     iteM g t e = SMT.impliesM g t `SMT.bandM` SMT.impliesM (SMT.bnotM g) e
--     unsatisfiable u v = unorientable sig u v

--     s `epo` t    = orientM allowEcomp sig prec safe mu (Epo s t)
--     s `eposub` t = orientM allowEcomp sig prec safe mu (Eposub s t)
--     s `equiv` t  = orientM allowEcomp sig prec safe mu (Eq s t)


--     -- epo: s >epo* t
--     u `epoimp` v
--       | u `isProperSupertermOf` v = SMT.topM
--       | unorientable sig u v      = SMT.botM
--       | otherwise                 = SMT.bigOrM [u `epo1` v, u `epo23` v]
--       where
--         isProperSupertermOf s t = any (t==) (concatMap R.subterms $ R.directSubterms s)

--         epo1 (R.Fun _ ss) t = SMT.bigOrM [ SMT.bigOrM [si `epo` t, si `equiv` t] | si <- ss ]
--         epo1 _            _ = SMT.botM

--         epo23 s@(R.Fun f ss) (R.Fun g ts) =
--           SMT.bigAndM
--           [ SMT.bigOrM  [ precM $ f:>:g, epo3 ]
--           , SMT.bigAndM [ iteM (safeM g i) (s `epo` ti) (s `eposub` ti) | (i,ti) <- tsi ] ]
--           where
--             ssi = [ (i, si) | i <- [1..] | si <- ss ]
--             tsi = [ (i, ti) | i <- [1..] | ti <- ts ]
--             epo3
--               | Sig.isDefined g sig && not (null ss) && length ss == length ts = SMT.bigAndM [ precM (f:~:g), epolex 1 ]
--               | otherwise                                                      = SMT.botM
--             epolex k
--               | length ssi < k = SMT.botM
--               | otherwise      = SMT.bigAndM [
--                 let
--                   rec  = epolex (k+1)
--                   comp = SMT.bigOrM [ si `eposub` tj, SMT.bigAndM [si `equiv` tj, rec] ]
--                 in
--                 return (SMT.bigAnd [mu f (i,k), mu g (j,k)]) `SMT.impliesM` iteM (safeM g j) rec comp
--                 | (i, si) <- ssi, (j, tj) <- tsi]
--         epo23 _ _ = SMT.botM

--     -- eposub: s \sqltepo t
--     u `eposubimp` v
--       | unsatisfiable u v = SMT.botM
--       | otherwise         = SMT.bigOrM [ u `eposub1` v, u `eposub2` v ]
--       where

--         (R.Fun f ss) `eposub1` t = SMT.bigOrM [ SMT.bigAndM [maybeNormal i, SMT.bigOrM [si `eposub` t, si `equiv` t]] | i <- [1..] | si <- ss]
--           where
--             maybeNormal i
--               | Sig.isDefined f sig = return $ SMT.bnot $ safe f i
--               | otherwise           = SMT.topM
--         _ `eposub1` _ = SMT.botM

--         -- special case: with extended composition
--         s@(R.Fun f _) `eposub2` (R.Fun g ts)
--           | allowEcomp = SMT.bigAndM [ precM (f:>:g) , SMT.bigAndM [ SMT.bigAndM [ return (safe g i), s `eposub` ti] | i <- [1..] | ti <- ts] ]
--           | otherwise  = SMT.botM
--         _ `eposub2` _ = SMT.botM

--     -- equivalence: s ~ t modulo mu
--     u `equivimp` v
--       | u == v            = SMT.topM
--       | unsatisfiable u v = SMT.botM
--       | otherwise         = case (u,v) of
--         (R.Var _ , R.Var _) -> SMT.botM
--         (R.Fun f ss, R.Fun g ts)
--           | unsat           -> SMT.botM
--           | otherwise       -> SMT.bigAndM
--             [ precM (f:~:g)
--             , SMT.bigAndM
--               [ return (SMT.bigAnd [mu f (i,k), mu g (j,k)]) `SMT.impliesM` (si `equiv` tj)
--               | (i,si) <- zip [1..] ss, (j,tj) <- zip [1..] ts, k <- [1..length ss] ]
--             ]
--           where unsat = length ss /= length ts || (Sig.isConstructor f sig /= Sig.isConstructor g sig)
--         _              -> SMT.botM


--- * instances ------------------------------------------------------------------------------------------------------

extCompArg :: T.Argument 'T.Required ExtComp
extCompArg = T.flag "extend"
  [ "Extended Composition: If this flag is enabled, then the slightly more ."
  , "liberal composition scheme 'f(x;y) = h(g(;x);k(x;y))' is permitted."
  , "Currently it is not known whether this extension is sound." ]
  `T.withDomain` fmap show [(minBound :: ExtComp)..]

description :: [String]
description = [ unwords
  [ "This processor implements orientation of the input problem using 'exponential path orders',"
  , "a technique applicable for innermost runtime-complexity analysis."
  , "Exponential path orders are a miniaturisation of 'lexicographic path orders',"
  , "restricted so that compatibility assesses exponential runtime complexity."] ]

-- FIXME: MS: TODO: timeout shouldn't be necessary; for some reason
-- @timeoutInt 5 (timeoutIn 5 epostar)@ works fine but @timeoutIn 5 not@
epoStarStrategy :: ExtComp -> TrsStrategy
-- epoStarStrategy = T.timeoutRemaining . T.meoutRemaining . Proc . EpoStar
epoStarStrategy = T.Apply . EpoStar

epoStarDeclaration :: T.Declaration ('[T.Argument 'T.Optional ExtComp] T.:-> TrsStrategy)
epoStarDeclaration = T.declare "epostar" description (T.OneTuple exArg) epoStarStrategy
  where exArg = extCompArg `T.optional` NoExtComp

epoStar :: TrsStrategy
epoStar = T.deflFun epoStarDeclaration

epoStar' :: ExtComp -> TrsStrategy
epoStar' = T.declFun epoStarDeclaration


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty f => PP.Pretty (MuMapping f) where
  pretty (MuMapping m) = PP.hsep $ PP.punctuate (PP.char ',') (pp `fmap` M.toList m)
    where pp (f,is) = PP.text "mu" <> PP.parens (PP.pretty f) PP.<+> PP.char '=' PP.<+> PP.list' is

instance (Ord f, PP.Pretty f, PP.Pretty v) => PP.Pretty (EpoStarProof f v) where
  pretty proof = PP.vcat
    [ PP.text "Strict Rules in Predicative Notation:"
    , ppind (SM.prettySafeTrs (safeMapping_ proof) (stricts_ proof))
    , PP.text "Safe Mapping:"
    , ppind (safeMapping_ proof)
    , PP.text "Argument Permuation:"
    , ppind (argumentPermutation_ proof)
    , PP.text "Precedence:"
    , ppind (precedence_ proof) ]
    where ppind a = PP.indent 2 $ PP.pretty a

instance Xml.Xml (EpoStarProof f v) where
  toXml _ = Xml.empty

