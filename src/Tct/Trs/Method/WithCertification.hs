module Tct.Trs.Method.WithCertification 
  ( withCertification
  , withCertification'
  , withCertificationDeclaration
  ) where


import           Control.Monad.Error    (throwError)
import           Data.Typeable

import qualified Tct.Core.Common.Parser as P
import qualified Tct.Core.Data          as T

import           Tct.Trs.Data
import qualified Tct.Trs.Data.CeTA      as CeTA


data TotalProof = TotalProof | PartialProof
  deriving (Show, Eq, Enum, Bounded, Typeable)

data ClosedProof = ClosedProof | OpenProof
  deriving (Show, Eq, Enum, Bounded, Typeable)

instance T.SParsable i i TotalProof where parseS = P.enum
instance T.SParsable i i ClosedProof where parseS = P.enum

data WithCertification = WithCertification
  { total_      :: TotalProof
  , closed_     :: ClosedProof
  , onStrategy_ :: TrsStrategy
  } deriving Show


instance T.Processor WithCertification where
  type ProofObject WithCertification = ()
  type I WithCertification           = TrsProblem
  type O WithCertification           = TrsProblem

  solve p prob = do
    ret <- T.evaluate (onStrategy_ p) prob
    tmp <- T.tempDirectory `fmap` T.askState
    res <- case ret of
      T.Halt _ -> return (Left "Halting computation.")
      rpt
        | T.isOpen pt && (closed_ p == OpenProof) -> return (Right pt)
        | T.isOpen pt                             -> return (Left "Can not be certified. Problem is Open ")
        | (total_ p == TotalProof)                -> CeTA.totalProofIO' tmp pt
        | otherwise                               -> CeTA.partialProofIO' tmp pt
        where pt = T.fromReturn rpt
    let
      toRet = case ret of
        T.Continue _ -> T.Continue
        T.Abort _    -> T.Abort
        T.Halt pt    -> const (T.Halt pt)

    either (throwError . userError) (return . toRet) res

withCertificationStrategy :: TotalProof -> ClosedProof -> TrsStrategy -> TrsStrategy
withCertificationStrategy t c st = T.Proc $ WithCertification { total_ = t, closed_ = c, onStrategy_ = st }

withCertificationDeclaration :: T.Declaration(
  '[ T.Argument 'T.Optional TotalProof
   , T.Argument 'T.Optional ClosedProof
   , T.Argument 'T.Required TrsStrategy]
   T.:-> TrsStrategy)
withCertificationDeclaration = T.declare "withCertification" [desc] (totalArg, closedArg, T.strat) withCertificationStrategy
  where
    desc = "This processor invokes CeTA on the result of the provided strategy."
    totalArg = T.arg
      `T.withName` "totalProof"
      `T.withHelp` ["This argument specifies wheter to invoke CeTA with '--allow-assumptions'. To allow partial proof" ]
      `T.optional` TotalProof
      `T.withDomain` fmap show [(minBound :: TotalProof)..]
    closedArg = T.arg
      `T.withName` "closedProof"
      `T.withHelp` ["This argument specifies wether certficiation should only be invoked on closed proof trees."]
      `T.optional` OpenProof
      `T.withDomain` fmap show [(minBound :: ClosedProof)..]

withCertification :: TrsStrategy -> TrsStrategy
withCertification = T.deflFun withCertificationDeclaration

withCertification' :: TotalProof -> ClosedProof -> TrsStrategy -> TrsStrategy
withCertification' = T.declFun withCertificationDeclaration


