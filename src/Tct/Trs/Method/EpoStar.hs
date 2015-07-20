{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Trs.Method.EpoStar where

import qualified Data.Array as Ar
import Data.Typeable
import           Control.Applicative
import qualified Data.Foldable                as F (foldr)
import qualified Data.Map.Strict              as M
import           Data.Maybe                   (fromMaybe)
import           Data.Monoid                  ((<>))
import qualified Data.Set                     as S

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import qualified Data.Rewriting.Rule          as R (lhs, rhs)
import qualified Data.Rewriting.Term          as R

import           Tct.Common.ProofCombinators
import           Tct.Common.SMT               ((.&&), (.<=>), (.=>))
import qualified Tct.Common.SMT               as SMT

import           Tct.Trs.Data
import           Tct.Trs.Data.Precedence      (Order (..), Precedence (..))
import qualified Tct.Trs.Data.Precedence      as Prec
import qualified Tct.Trs.Data.Rewriting       as R (directSubterms)
import qualified Tct.Trs.Data.Signature       as Sig
import qualified Tct.Trs.Data.Trs             as Trs
import qualified Tct.Trs.Data.Problem             as Prob
import qualified Tct.Trs.Encoding.SafeMapping as SM

newtype ArgumentPermutation f = AP (M.Map f [Int]) deriving Show

instance PP.Pretty f => PP.Pretty (ArgumentPermutation f) where
  pretty (AP m) = PP.hsep $ PP.punctuate (PP.char ',') (uncurry pp `fmap` M.toList m)
    where pp f is = PP.text "mu" <> PP.parens (PP.pretty f) PP.<+> PP.char '=' PP.<+> PP.list' is


newtype EpoStar = EpoStar { ecomp_ :: Extended } deriving Show

data Extended = Extended | NoExtended deriving (Bounded, Enum, Eq, Typeable, Show)

-- instance T.SParsable i i Extended where
--   parseS = P.enum

-- extendedArgs :: T.Argument 'T.Required Extended
-- extendedArgs = T.arg
--   `T.withName` "extended"
--   `T.withHelp`
--     [ "This argument specifies whether usable arguments are computed (if applicable)"
--     , "in order to relax the monotonicity constraints on the interpretation."]
--   `T.withDomain` fmap show [(minBound :: UsableArgs)..]

useExtended :: Extended -> Bool
useExtended = (Extended==)

data EpoStarProof f v = EpoStarProof
  { stricts_             :: Trs f v -- ^ The oriented input TRS.
  , safeMapping_         :: SM.SafeMapping f -- ^ The safe mapping.
  , precedence_          :: Precedence f -- ^ The precedence.
  , argumentPermutation_ :: ArgumentPermutation f -- ^ Employed argument permutation.
  , signature_           :: Signature f  -- ^ Signature underlying 'epoInputTrs'
  } deriving Show

instance T.Processor EpoStar where
  type ProofObject EpoStar = ApplicationProof (OrientationProof (EpoStarProof F V))
  type I EpoStar           = TrsProblem
  type O EpoStar           = TrsProblem
  type Forking EpoStar     = T.Judgement

  solve p prob = T.resultToTree p prob <$>
    maybe epo (return . T.Fail . Inapplicable) maybeApplicable
    where

      maybeApplicable = Prob.isRCProblem' prob <|> Prob.isInnermostProblem' prob <|> Trs.isConstructorTrs' sig trs

      trs    = Prob.allComponents prob
      sig    = Prob.signature prob
      solver = SMT.smtSolveTctM prob

      epo = do
        res <- entscheide solver sig trs (ecomp_ p)
        return $ case res of
          SMT.Sat m -> T.Success T.Judgement (Applicable . Order $ nproof m) (const $ T.timeUBCert (T.Exp Nothing))
          _         -> T.Fail (Applicable Incompatible)

      nproof (prec,safe) = EpoStarProof
        { stricts_            = trs
        , safeMapping_        = safe
        , precedence_         = prec
        , argumentPermutation_ = undefined
        , signature_          = sig }

instance Xml.Xml (EpoStarProof f v) where
  toXml _ = Xml.empty

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (EpoStarProof f v) where
  pretty proof = PP.vcat
    [ PP.text "Safe Mapping:"
    -- , PP.indent 2 $ PP.pretty (safeMapping_ proof)
    , PP.text "Precedence:"
    , ppind (precedence_ proof)
    , PP.text "Argument Permuation:"
    , ppind (argumentPermutation_ proof)
    , PP.text "Strict Rules in Predicative Notation:"
    , ppind (stricts_ proof) ]
    where ppind a = PP.indent 2 $ PP.pretty a

data EpoOrder  f v
  = Epo (R.Term f v) (R.Term f v)
  | Eposub (R.Term f v) (R.Term f v)
  | Eq (R.Term f v) (R.Term f v)
  deriving (Eq, Ord)



--- * precedence encoding --------------------------------------------------------------------------------------------
-- introduce variables f :>: g and f :~: g for all defined symbols

data PrecedenceEncoder f w = PrecedenceEncoder
  (Precedence f)  -- ^ initial precedence
  (M.Map (f,f) (SMT.Formula w)) -- ^ variable map f :>: g
  (M.Map (f,f) (SMT.Formula w)) -- ^ variable map f :~: g

precedenceEncoder :: (SMT.Fresh w, Ord f) => Signature f -> SMT.SmtSolverSt w (PrecedenceEncoder f w)
precedenceEncoder sig = PrecedenceEncoder (Prec.empty sig) <$> gtm <*> eqm
  where
    gtm = M.fromList <$> mapM bvar [ (f,g) | f <- ds, g <- ds, f < g || f > g ]
    eqm = M.fromList <$> mapM bvar [ (f,g) | f <- ds, g <- ds, f < g ]
    bvar k = SMT.bvarM' >>= \v -> return (k,v)
    ds = S.toList $ Sig.defineds sig

precedence :: Ord f => PrecedenceEncoder f w -> Order f -> SMT.Formula w
precedence (PrecedenceEncoder (Precedence (sig,_)) gtm _) (f :>: g)
  | f == g                   = SMT.bot
  | Sig.isConstructor f sig  = SMT.bot
  | Sig.isConstructor g sig  = SMT.bot
  | otherwise                = find (f,g) gtm
precedence (PrecedenceEncoder (Precedence (sig,_)) _ eqm) (f :~: g)
  | f            == g = SMT.top
  | cf && cg      = SMT.top
  | cf && not cg  = SMT.bot
  | not cf && cg  = SMT.bot
  | otherwise     = find (if f < g then (f,g) else (g,f)) eqm
  where
    cf = Sig.isConstructor f sig
    cg = Sig.isConstructor g sig

instance (Ord f, SMT.Storing w) => SMT.Decode (SMT.Environment w) (PrecedenceEncoder f w) (Precedence f) where
  decode (PrecedenceEncoder (Precedence (sig,_)) gtm eqm) = do
    gts :: S.Set (f,f) <- SMT.decode (SMT.Property (fromMaybe False) gtm)
    eqs :: S.Set (f,f) <- SMT.decode (SMT.Property (fromMaybe False) eqm)
    return $ Precedence (sig, [f :>: g | (f,g) <- S.toList gts] ++ [ f:~: g | (f,g) <- S.toList eqs])


find :: Ord k => k -> M.Map k v -> v
find e = fromMaybe (error "EpoStar.find") . M.lookup e


--- * safe mapping ---------------------------------------------------------------------------------------------------
-- introduce variables safe_f_i

data SafeMappingEncoder f w = SafeMappingEncoder
  (SM.SafeMapping f)              -- ^ initial safe mapping
  (M.Map (f,Int) (SMT.Formula w)) -- ^ variable safe_f_i

safeMappingEncoder :: (SMT.Fresh w, Ord f) => Signature f -> SMT.SmtSolverSt w (SafeMappingEncoder f w)
safeMappingEncoder sig = SafeMappingEncoder (SM.empty sig) <$> sfm
  where
    sfm = M.fromList <$> mapM bvar [ (f,i) | f <- S.toList (Sig.defineds sig), i <- Sig.positions sig f ]
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

type Relation w = Ar.Array Int (SMT.Formula w)

data MuMappingEncoder f w = MuMappingEncoder
  (M.Map f (Relation w))

muMappingEncoder :: (SMT.Fresh w, Ord f) => Signature f -> SMT.SolverSt w (MuMappingEncoder f w)
muMappingEncoder = MuMappinEncoder <$> m
  where
    
  

muMapping :: MuMappingEncoder f w -> f -> (Int, Int) -> SMT.Formula w
muMapping = undefined

--- * orient ---------------------------------------------------------------------------------------------------------


unorientable :: (Ord f, Ord v) => Signature f -> R.Term f v -> R.Term f v -> Bool
unorientable sig u v =
  varsS u `S.isProperSubsetOf` varsS v
  || (isConstructorTerm u && not (isConstructorTerm v))
  where
    varsS = S.fromList . R.vars
    isConstructorTerm = all (`Sig.isConstructor` sig) . R.funs


entscheide :: (Functor m, Monad m, Ord f, Ord v) => 
  SMT.SmtSolver m Int
  -> Signature f
  -> Trs f v
  -> Extended 
  -- -> m (SMT.Result (Precedence f, SM.SafeMapping f, ArgumentPermutation f))
  -> m (SMT.Result (Precedence f, SM.SafeMapping f))
entscheide solver sig trs ecomp = do
  -- res :: SMT.Result (Precedence f, SM.SafeMapping f, ArgumentPermutation f) <- SMT.smtSolveSt solver $ do
  res :: SMT.Result (Precedence f, SM.SafeMapping f) <- SMT.smtSolveSt solver $ do
    SMT.setLogic SMT.QF_LIA

    sfenc <- safeMappingEncoder sig
    prenc <- precedenceEncoder sig
    muenc <- undefined

    let
      safe = safeMapping sfenc
      prec = precedence prenc
      mu = undefined
      epo s t = orient (useExtended ecomp) sig prec safe mu (Epo s t)

    SMT.assert (SMT.top :: SMT.Formula Int)
    SMT.assert =<< fst <$> SMT.memo (SMT.bigAndM [ R.lhs r `epo` R.rhs r | r <- rs ])
    SMT.assert $ SMT.bigAnd
      [
        prec (f:~:g) .=>
          SMT.bigAnd [ (mu f (i,k) .&& mu g (j,k)) .=> (safe f i .<=> safe g j) | i <- [1..af], j <- [1..af], k <- [1..af] ]

      | let ds = S.toList (Sig.defineds sig), f <- ds, g <- ds, let af = Sig.arity sig f, af == Sig.arity sig g ]

    -- return $ SMT.decode (prenc, sfenc, muenc)
    return $ SMT.decode (prenc, sfenc)
  return $ res
    where
      rs = Trs.toList trs

orient :: (Ord v, Ord f, Monad m) =>
  Bool
  -> Signature f
  -> (Order f -> SMT.Formula w)
  -> (f -> Int -> SMT.Formula w)
  -> (f -> (Int, Int) -> SMT.Formula w)
  -> EpoOrder f v -> SMT.Memo (EpoOrder f v) (SMT.Formula w) m (SMT.Formula w)
orient allowEcomp sig prec safe mu = SMT.memoized $ \a ->
  case a of
    Epo s t    -> s `epoimp` t
    Eposub s t -> s `eposubimp` t
    Eq s t     -> s `equivimp` t
  where
    precM = return . prec
    ite g t e = SMT.implies g t `SMT.band` SMT.implies (SMT.bnot g) e
    iteM g t e = SMT.impliesM g t `SMT.bandM` SMT.impliesM (SMT.bnotM g) e

    s `epo` t = orient allowEcomp sig prec safe mu (Epo s t)
    s `eposub` t = orient allowEcomp sig prec safe mu (Epo s t)
    s `equiv` t = orient allowEcomp sig prec safe mu (Epo s t)



    -- epo
    u `epoimp` v
      | u `isProperSupertermOf` v = SMT.topM
      | unorientable sig u v      = SMT.botM
      | otherwise                 = SMT.bigOrM [u `epo1` v, u `epo23` v]
      where
        isProperSupertermOf s t = any (t==) (R.directSubterms s)
        epo1 (R.Fun _ ss) t = SMT.bigOrM [ SMT.bigOrM [ si `equiv` t, si `epo` t] | si <- ss]
        epo1 _          _   = SMT.botM

        epo23 s@(R.Fun f ss) (R.Fun g ts) = SMT.bigAndM
          [ SMT.bigAndM [ iteM (return $ safe g i) (s `epo` ti) (s `eposub` ti) | (i,ti) <- tsi ]
          , SMT.bigOrM [ precM $ f :>: g, epo3]]
          where
            ssi = [ (i, si) | i <- [1..] | si <- ss]
            tsi = [ (i, ti) | i <- [1..] | ti <- ts]
            epo3
              | Sig.isDefined g sig && not (null ss) && length ss == length ts = SMT.bigAndM [ precM $ f :~: g , epolex 1]
              | otherwise                                                      = SMT.botM
            epolex k
              | length ssi < k = SMT.botM
              | otherwise      = SMT.bigAndM [
                let
                  rec  = epolex (k+1)
                  comp = SMT.bigOrM [ si `eposub` tj, SMT.bigAndM [si `equiv` tj, rec] ]
                in
                return (SMT.bigAnd [mu f (i,k), mu g (j,k)]) `SMT.impliesM` iteM (return $ safe g j) rec comp
                | (i, si) <- ssi, (j, tj) <- tsi]
        epo23 _ _ = SMT.botM

    u `eposubimp` v
      | unorientable sig u v = SMT.botM
      | otherwise            = SMT.bigOrM [u `eposub1` v, u `eposub2` v]
      where

        (R.Fun f ss) `eposub1` t = SMT.bigOrM [ SMT.bigAndM [maybeNormal i, SMT.bigOrM [si `eposub` t, si `equiv` t]] | i <- [1..] | si <- ss]
          where
            maybeNormal i
              | Sig.isDefined f sig = return $ SMT.bnot $ safe f i
              | otherwise           = SMT.topM
        _ `eposub1` _ = SMT.botM

        s@(R.Fun f _) `eposub2` (R.Fun g ts)
          | allowEcomp = SMT.bigAndM [ precM (f:>:g) , SMT.bigAndM [ SMT.bigAndM [ return (safe g i), s `eposub` ti] | i <- [1..] | ti <- ts] ]
          | otherwise  = SMT.botM
        _ `eposub2` _ = SMT.botM


    -- equivalence
    u `equivimp` v
      | u == v    = SMT.topM
      | unorientable sig u v = SMT.botM
      | otherwise = case (u,v) of
        (R.Var _, R.Var _) -> SMT.botM -- u != v assumed
        (R.Fun f ss, R.Fun g ts)
          | unsat     -> SMT.botM
          | otherwise -> SMT.bigAndM
            [ return $ prec $ f :~: g
            , SMT.bigAndM [ return (SMT.bigAnd [mu f (i,k), mu g (j,k)]) `SMT.impliesM` (si `equiv` tj)
                    | (i,si) <- zip [1..] ss
                    , (j,tj) <- zip [1..] ts
                    , k <- [1..length ss]]]
          where unsat = length ss /= length ts || (Sig.isConstructor f sig /= Sig.isConstructor g sig)
        _              -> SMT.botM




