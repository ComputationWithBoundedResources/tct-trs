-- | This module provides the /With Certification/ processor.
-- Is used to certify the proof output of a (sub) strategy.
module Tct.Trs.Method.WithCertification 
  ( withCertificationDeclaration
  , withCertification
  , withCertification'
  -- * arguments
  , TotalProof (..)
  ) where


import           Control.Monad.Error    (throwError)
import           Data.Typeable

import qualified Tct.Core.Common.Parser as P
import qualified Tct.Core.Data          as T

import           Tct.Trs.Data
import qualified Tct.Trs.Data.CeTA      as CeTA


-- TODO: MS: the behaviour should be changed; return some feedback (not an error) if certification is applied/successful
-- | Indicates wether to allow partial proofs.
-- A partial proof uses unknown proofs/assumptions to handle unsupported transformations and open problems.
-- 
-- The current implementation behaves as follows
--  * if TotalProof is set, certification is ignored if there are open problems left
--  * throws an error if certification is not successful
--  * silent return if certification is successful.
data TotalProof = TotalProof | PartialProof
  deriving (Show, Eq, Enum, Bounded, Typeable)

instance T.SParsable i i TotalProof where parseS = P.enum 

data WithCertification = WithCertification
  { kind       :: TotalProof
  , onStrategy :: TrsStrategy
  } deriving Show


instance T.Processor WithCertification where
  type ProofObject WithCertification = ()
  type In  WithCertification         = TrsProblem
  type Out WithCertification         = TrsProblem

  execute p prob = do
    undefined
    -- ret <- T.evaluate (onStrategy p) prob
    -- tmp <- T.tempDirectory `fmap` T.askState
    -- undefined
      rpt 
    -- res <- undefined -- case ret of
      -- T.Halt _ -> return (Left "Halting computation.")
      -- rpt
      --   | kind p == PartialProof -> CeTA.partialProofIO' tmp pt
      --   | T.isOpen pt            -> return (Right pt)
      --   | otherwise              -> CeTA.totalProofIO' tmp pt
      --   where pt = T.fromReturn rpt
    -- let
      -- toRet = case ret of
      --   T.Continue _ -> T.Continue
      --   T.Abort _    -> T.Abort
      --   T.Halt pt    -> const (T.Halt pt)

    -- either (throwError . userError) (return . toRet) res

withCertificationStrategy :: TotalProof -> TrsStrategy -> TrsStrategy
withCertificationStrategy t st = T.Apply $ WithCertification { kind = t, onStrategy = st }

withCertificationDeclaration :: T.Declaration(
  '[ T.Argument 'T.Optional TotalProof
   , T.Argument 'T.Required TrsStrategy]
   T.:-> TrsStrategy)
withCertificationDeclaration = T.declare "withCertification" [desc] (totalArg, T.strat) withCertificationStrategy
  where
    desc = "This processor invokes CeTA on the result of the provided strategy."
    totalArg = T.arg
      `T.withName` "kind"
      `T.withHelp` [ "This argument specifies wheter to invoke CeTA with '--allow-assumptions' to provide certification of partial proofs." ]
      `T.optional` TotalProof
      `T.withDomain` fmap show [(minBound :: TotalProof)..]

-- | 
-- > withCertification (dependencyTuples .>>> matrix .>>> empty)
-- > dependencyPairs' WIDP .>>> withCertification (matrix .>>> empty)
withCertification :: TrsStrategy -> TrsStrategy
withCertification = T.deflFun withCertificationDeclaration

-- | > (withCertification' PartialProof dependencyTuples) .>>> matrix >>> empty
withCertification' :: TotalProof -> TrsStrategy -> TrsStrategy
withCertification' = T.declFun withCertificationDeclaration

