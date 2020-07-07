-- | This module provides the /With Certification/ processor.
-- Is used to certify the proof output of a (sub) strategy.
module Tct.Trs.Processor.WithCertification
  ( withCertificationDeclaration
  , withCertification
  , withCertification'
  -- * arguments
  , TotalProof (..)
  ) where


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
  deriving (Show, Eq, Enum, Bounded)

data WithCertification = WithCertification
  { kind       :: TotalProof
  , onStrategy :: TrsStrategy
  } deriving Show


instance T.Processor WithCertification where
  type ProofObject WithCertification = ()
  type In  WithCertification         = Trs
  type Out WithCertification         = Trs

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

withCertificationDeclaration :: T.Declared Trs Trs => T.Declaration(
  '[ T.Argument 'T.Optional TotalProof
   , T.Argument 'T.Required TrsStrategy]
   T.:-> TrsStrategy)
withCertificationDeclaration = T.declare "withCertification" [desc] (totalArg, stratArg) withCertificationStrategy
  where
    stratArg = T.strat "toCertify" ["The strategy to certify."]
    desc = "This processor invokes CeTA on the result of the provided strategy."
    totalArg = (T.flag "kind"
      [ "This argument specifies wheter to invoke CeTA with '--allow-assumptions' to provide certification of partial proofs." ])
      `T.optional` TotalProof

-- | Invokes CeTA on the result of the strategy.
-- > withCertification (dependencyTuples .>>> matrix .>>> empty)
-- > dependencyPairs' WIDP .>>> withCertification (matrix .>>> empty)
withCertification :: TrsStrategy -> TrsStrategy
withCertification = withCertificationStrategy TotalProof-- T.deflFun withCertificationDeclaration

-- | Invokes CeTA on the result of the strategy.
-- | > (withCertification' PartialProof dependencyTuples) .>>> matrix >>> empty
withCertification' :: TotalProof -> TrsStrategy -> TrsStrategy
withCertification' = withCertificationStrategy --T.declFun withCertificationDeclaration

