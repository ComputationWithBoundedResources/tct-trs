{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- Implementation details can be found in the technical report '@tba@'.
-- | This module provides the \AmortisedAnalysis\ processor.
module Tct.Trs.Processor.AmortisedAnalysis
  ( araDeclaration
  , ara
  , ara'

  , Heuristics (..)
  , heuristicsArg
  ) where


import           Control.Applicative
import           Control.Monad
import qualified Data.Array                   as Ar
import qualified Data.Foldable                as F (foldr)
import qualified Data.Map.Strict              as M
import           Data.Maybe                   (fromMaybe)
import           Data.Monoid                  ((<>))
import qualified Data.Set                     as S

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           SLogic.Smt.Solver            (minismt)

import qualified Data.Rewriting.Rule          as R
import qualified Data.Rewriting.Term          as R
import qualified Data.Rewriting.Problem       as R
import qualified Data.Rewriting.Typed.Rule    as RT
import qualified Data.Rewriting.Typed.Term    as RT
import qualified Data.Rewriting.Typed.Problem as RT

import           Tct.Common.ProofCombinators
import           Tct.Common.SMT               ((.&&), (.<=>), (.<=), (.==), (.=>), (.>), (.||))
import qualified Tct.Common.SMT               as SMT

import           Tct.Trs.Data
import           Tct.Trs.Data.Precedence      (Order (..), Precedence (..))
import qualified Tct.Trs.Data.Precedence      as Prec
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.ProblemKind     as Prob
import qualified Tct.Trs.Data.Rewriting       as R (directSubterms)
import qualified Tct.Trs.Data.Signature       as Sig
import qualified Tct.Trs.Data.Rules as RS
import qualified Tct.Trs.Encoding.SafeMapping as SM

import Debug.Trace


data Ara = Ara { heuristics_ :: Heuristics }
            deriving Show

data Heuristics = Heuristics | NoHeuristics deriving (Bounded, Enum, Eq, Show)

-- useHeuristics :: Heuristics -> Bool
-- useHeuristics = (Heuristics==)

data AraProof f v = AraProof
  { stricts_             :: Rules f v        -- ^ The oriented input TRS.
  -- , safeMapping_         :: SM.SafeMapping f -- ^ The safe mapping.
  -- , precedence_          :: Precedence f     -- ^ The precedence.
  -- , argumentPermutation_ :: MuMapping f      -- ^ Employed argument permutation.
  -- , signature_           :: Signature f      -- ^ Signature underlying 'epoInputTrs'
  } deriving Show


instance T.Processor Ara where
  type ProofObject Ara = ApplicationProof (OrientationProof (AraProof F V))
  type In  Ara         = Trs
  type Out Ara         = Trs
  type Forking Ara     = T.Judgement

  execute p prob =
    trace ("TODO: ara execute")
    trace ("show p: " ++ show p)
    trace ("prob: " ++ show prob)
    trace ("prob: " ++ show (typeProblem prob))

    -- check left linearity

    -- check innermost

    undefined


typeProblem :: Prob.Problem F V -> RT.Problem F V String String String String
typeProblem inProb = RT.Problem { RT.startTerms = convertStartTerms $ Prob.startTerms inProb
                                , RT.strategy = convertStrategy $ Prob.strategy inProb
                                , RT.theory = Nothing
                                , RT.datatypes = Nothing
                                , RT.signatures = Nothing
                                , RT.rules = RT.RulesPair
                                  (fmap convertRule $ RS.toList $ Prob.strictTrs inProb)
                                  (fmap convertRule $ RS.toList $ Prob.weakTrs inProb)
                                , RT.variables =
                                    S.toList $ RS.vars (Prob.strictTrs inProb `RS.union`
                                                        Prob.weakTrs inProb)
                                , RT.symbols =
                                    S.toList (Sig.defineds (Prob.signature inProb)) ++
                                    S.toList (Sig.constructors (Prob.signature inProb))
                                , RT.comment = Nothing
                                }
  where convertStartTerms Prob.AllTerms{} = RT.AllTerms
        convertStartTerms Prob.BasicTerms{} = RT.BasicTerms
        convertStrategy Prob.Innermost = RT.Innermost
        convertStrategy Prob.Full = RT.Full
        convertStrategy Prob.Outermost = RT.Outermost
        -- convertTheory (R.SymbolProperty a b) = (RT.SymbolProperty a b)
        -- convertTheory (R.Equations rules) = RT.Equations (fmap convertRule rules)
        -- convertRulesPair (R.RulesPair strict weak) =
        --   RT.RulesPair (fmap convertRule strict) (fmap convertRule weak)
        -- convertRules (RS.RulesT set) = fmap convertRule (S.toList set)
        convertRule (R.Rule lhs rhs) = RT.Rule (convertTerm lhs) (convertTerm rhs)
        convertTerm (R.Var v) = RT.Var v
        convertTerm (R.Fun f ch) = RT.Fun f (fmap convertTerm ch)
        -- makeSyms (Sig.Signature sigs defs cons) = S.toList defs ++ S.toList cons


    -- maybe epo (\s -> T.abortWith (Inapplicable s :: ApplicationProof (OrientationProof (EpoStarProof F V)))) maybeApplicable
    -- where

    --   maybeApplicable = Prob.isRCProblem' prob <|> Prob.isInnermostProblem' prob <|> RS.isConstructorTrs' sig trs

    --   trs    = Prob.allComponents prob
    --   sig    = Prob.signature prob
    --   -- solver = SMT.smtSolveTctM prob
    --   solver = minismt

    --   epo = do
    --     res <- entscheide solver trs sig (heuristics_ p)
    --     case res of
    --       SMT.Sat m -> T.succeedWith0 (Applicable . Order $ nproof m) (const $ T.timeUBCert (T.Exp Nothing))
    --       _         -> T.abortWith (Applicable (Incompatible :: OrientationProof (EpoStarProof F V)))

    --   nproof (prec,safe,mu) = EpoStarProof
    --     { stricts_             = trs
    --     , safeMapping_         = safe
    --     , precedence_          = prec
    --     , argumentPermutation_ = mu
    --     , signature_           = sig }


-- find :: Ord k => k -> M.Map k v -> v
-- find e = fromMaybe (error "EpoStar.find") . M.lookup e


-- --- * precedence encoding --------------------------------------------------------------------------------------------

-- data PrecedenceEncoder f w = PrecedenceEncoder
--   (Precedence f)          -- ^ initial precedence
--   (M.Map f (SMT.IExpr w)) -- ^ a (bounded) integer variable for each defined symbol

-- precedenceEncoder :: (SMT.Fresh w, Ord f) => Signature f -> SMT.SmtSolverSt w (PrecedenceEncoder f w)
-- precedenceEncoder sig = PrecedenceEncoder (Prec.empty sig) . M.fromList <$> mapM bounded (S.toList ds)
--   where
--     bounded f = do v <- SMT.ivarM'; SMT.assert (v .> SMT.zero .&& v .<= SMT.num k); return (f,v)
--     ds        = Sig.defineds sig
--     k         = S.size ds

-- precedence :: Ord f => PrecedenceEncoder f w -> Order f -> SMT.Formula w
-- precedence (PrecedenceEncoder (Precedence (sig,_)) fm) (f :>: g)
--   | f == g                   = SMT.bot
--   | Sig.isConstructor f sig  = SMT.bot
--   | Sig.isConstructor g sig  = SMT.top
--   | otherwise                = find f fm .> find g fm
-- precedence (PrecedenceEncoder (Precedence (sig,_)) fm) (f :~: g)
--   | f == g        = SMT.top
--   | cf && cg      = SMT.top
--   | cf && not cg  = SMT.bot
--   | not cf && cg  = SMT.bot
--   | otherwise     = find f fm .== find g fm
--   where
--     cf = Sig.isConstructor f sig
--     cg = Sig.isConstructor g sig

-- instance (Ord f, SMT.Storing w) => SMT.Decode (SMT.Environment w) (PrecedenceEncoder f w) (Precedence f) where
--   decode (PrecedenceEncoder (Precedence (sig,_)) fm) = do
--     fis :: [(f,Int)] <- M.assocs <$> SMT.decode fm
--     return $ Precedence (sig,  gts fis ++ eqs fis)
--     where
--       gts fis = [ f:>:g | (f,i) <- fis, (g,j) <- fis, i > j ]
--       eqs fis = [ f:~:g | (f,i) <- fis, (g,j) <- fis, i == j  ]


-- --- * safe mapping ---------------------------------------------------------------------------------------------------

-- data SafeMappingEncoder f w = SafeMappingEncoder
--   (SM.SafeMapping f)              -- ^ initial safe mapping
--   (M.Map (f,Int) (SMT.Formula w)) -- ^ variable safe_f_i for defined symbol f and argument position i

-- safeMappingEncoder :: (SMT.Fresh w, Ord f) => Signature f -> SMT.SmtSolverSt w (SafeMappingEncoder f w)
-- safeMappingEncoder sig = SafeMappingEncoder (SM.empty sig) <$> sfm
--   where
--     sfm    = M.fromList <$> mapM bvar [ (f,i) | f <- S.toList (Sig.defineds sig), i <- Sig.positions sig f ]
--     bvar k = SMT.bvarM' >>= \v -> return (k,v)

-- safeMapping :: Ord f => SafeMappingEncoder f w -> f -> Int -> SMT.Formula w
-- safeMapping (SafeMappingEncoder (SM.SafeMapping (sig,_)) sfm) f i
--   | Sig.isConstructor f sig = SMT.top
--   | otherwise               = find (f,i) sfm

-- instance (Ord f, SMT.Storing w) => SMT.Decode (SMT.Environment w) (SafeMappingEncoder f w) (SM.SafeMapping f) where
--   decode (SafeMappingEncoder sf sfm) = do
--     sfs :: S.Set (f,Int) <- SMT.decode (SMT.Property (fromMaybe False) sfm)
--     return $ F.foldr (uncurry SM.setSafe) sf sfs


-- --- * mu mapping -----------------------------------------------------------------------------------------------------

-- newtype MuMapping f = MuMapping (M.Map f [Int]) deriving Show

-- -- mu_f,i,k = mu(f,i)=k
-- newtype MuMappingEncoder f w = MuMappingEncoder (M.Map f (Ar.Array (Int,Int) (SMT.Formula w)))

-- muMappingEncoder :: (SMT.Fresh w, Ord f) => Signature f -> SMT.SmtSolverSt w (MuMappingEncoder f w)
-- muMappingEncoder sig = MuMappingEncoder . M.fromList <$> mapM bijection (Sig.elems sig)
--   where
--     bijection (f,af) = do
--       let ((u,l),(o,r)) = ((1,1),(af,af))
--       ar <- Ar.listArray ((u,l),(af,af)) <$> replicateM (af*af) SMT.bvarM'

--       sequence_ $ do
--         x <- Ar.range (u,o)
--         return $ SMT.assert $ exactlyOne1 (ar,l,r) x $ do y <- Ar.range (l,r); return (ar Ar.! (x,y))
--       sequence_ $ do
--         x <- Ar.range (u,o)
--         return $ SMT.assert $ exactlyOne2 (ar,l,r) x $ do y <- Ar.range (l,r); return (ar Ar.! (y,x))

--       return (f,ar)

--     exactlyOne1 (ar,l,r) x vs = SMT.bigOr vs .&&
--       SMT.bigAnd [ SMT.bigAnd [ SMT.bnot (ar Ar.! (x,i)) .|| SMT.bnot (ar Ar.! (x,j)) | j <- [i+1..r] ] | i <- [l..r-1] ]
--     exactlyOne2 (ar,l,r) x vs = SMT.bigOr vs .&&
--       SMT.bigAnd [ SMT.bigAnd [ SMT.bnot (ar Ar.! (i,x)) .|| SMT.bnot (ar Ar.! (j,x)) | j <- [i+1..r] ] | i <- [l..r-1] ]


-- muMapping :: Ord f => MuMappingEncoder f w -> f -> (Int, Int) -> SMT.Formula w
-- muMapping (MuMappingEncoder fm) f ix = find f fm Ar.! ix

-- instance (Ar.Ix i, SMT.Decode m c a) => SMT.Decode m (Ar.Array i c) (Ar.Array i a) where
--   decode ar = Ar.array bnds <$> mapM ( \(i,a) -> SMT.decode a >>= \c -> return (i,c) ) (Ar.assocs ar)
--     where bnds = Ar.bounds ar

-- instance (Ord f, SMT.Storing w) => SMT.Decode (SMT.Environment w) (MuMappingEncoder f w) (MuMapping f) where
--   decode (MuMappingEncoder fm) = do
--     fa :: M.Map f (Ar.Array (Int,Int) Bool) <- SMT.decode fm
--     return $ MuMapping $ (\ar -> foldr set [] $ Ar.assocs ar) `fmap` fa
--     where
--       set (_, False) is   = is
--       set ((_,k),True) is = k:is


-- --- * orient ---------------------------------------------------------------------------------------------------------


-- --- * instances ------------------------------------------------------------------------------------------------------

heuristicsArg :: T.Argument 'T.Required Heuristics
heuristicsArg = T.flag "TODO"
  [ "Description is to be done" ]

description :: [String]
description = [ unwords
  [ "This processor implements the amortised resource analysis."] ]

araStrategy :: Heuristics -> TrsStrategy
araStrategy = T.Apply . Ara

araDeclaration :: T.Declaration ('[T.Argument 'T.Optional Heuristics] T.:-> TrsStrategy)
araDeclaration = T.declare "ara" description (T.OneTuple exArg) araStrategy
  where exArg = heuristicsArg `T.optional` NoHeuristics

ara :: TrsStrategy
ara = T.deflFun araDeclaration

ara' :: Heuristics -> TrsStrategy
ara' = T.declFun araDeclaration


--- * proofdata
--------------------------------------------------------------------------------

instance (Ord f, PP.Pretty f, PP.Pretty v) => PP.Pretty (AraProof f v) where
  pretty proof = PP.text "TODO"
  -- PP.vcat
  --   [ PP.text "Strict Rules in Predicative Notation:"
  --   , ppind (SM.prettySafeTrs (safeMapping_ proof) (stricts_ proof))
  --   , PP.text "Safe Mapping:"
  --   , ppind (safeMapping_ proof)
  --   , PP.text "Argument Permuation:"
  --   , ppind (argumentPermutation_ proof)
  --   , PP.text "Precedence:"
  --   , ppind (precedence_ proof) ]
  --   where ppind a = PP.indent 2 $ PP.pretty a

instance Xml.Xml (AraProof f v) where
  toXml _ = Xml.empty

