-- | This module provides the /With Certification/ processor.
-- Is used to certify the proof output of a (sub) strategy.
module Tct.Trs.Method.WithCertification 
  ( --withCertificationDeclaration
  withCertification
  , withCertification'
  -- * arguments
  , TotalProof (..)
  ) where


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

data WithCertification = WithCertification
  { kind       :: TotalProof
  , onStrategy :: TrsStrategy
  } deriving Show


instance T.Processor WithCertification where
  type ProofObject WithCertification = ()
  type In  WithCertification         = TrsProblem
  type Out WithCertification         = TrsProblem

  execute p prob = do
    pt  <- T.evaluate (onStrategy p) (T.Open prob)
    tmp <- T.tempDirectory `fmap` T.askState
    res <- case pt of
      T.Failure r -> return $ Left (show r)
      rpt
        | kind p == PartialProof -> CeTA.partialProofIO' tmp rpt
        | T.isOpen rpt           -> return (Right pt)
        | otherwise              -> CeTA.totalProofIO' tmp rpt
    either T.abortWith k res
    where k pt = return $ T.Progress () T.fromId (T.toId pt)

withCertificationStrategy :: TotalProof -> TrsStrategy -> TrsStrategy
withCertificationStrategy t st = T.Apply $ WithCertification { kind = t, onStrategy = st }

-- withCertificationDeclaration :: T.Declaration(
--   '[ T.Argument 'T.Optional TotalProof
--    , T.Argument 'T.Required TrsStrategy]
--    T.:-> TrsStrategy)
-- withCertificationDeclaration = T.declare "withCertification" [desc] (totalArg, T.strat) withCertificationStrategy
--   where
--     desc = "This processor invokes CeTA on the result of the provided strategy."
--     totalArg = (T.flag "kind"
--       [ "This argument specifies wheter to invoke CeTA with '--allow-assumptions' to provide certification of partial proofs." ]
--       `T.withDomain` fmap show [(minBound :: TotalProof)..])
--       `T.optional` TotalProof

-- | 
-- > withCertification (dependencyTuples .>>> matrix .>>> empty)
-- > dependencyPairs' WIDP .>>> withCertification (matrix .>>> empty)
withCertification :: TrsStrategy -> TrsStrategy
withCertification = undefined --T.deflFun withCertificationDeclaration

-- | > (withCertification' PartialProof dependencyTuples) .>>> matrix >>> empty
withCertification' :: TotalProof -> TrsStrategy -> TrsStrategy
withCertification' = undefined --T.declFun withCertificationDeclaration

