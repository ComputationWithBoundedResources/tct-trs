module Tct.Trs.Processor 
  ( 
  defaultDeclarations

  , empty
  , emptyDeclaration
  ) where


import System.Process
import System.Exit
import System.IO.Temp
import System.IO (hFlush, hClose)
import Control.Monad.Error (throwError)
import Control.Monad.Trans (liftIO, lift)

import qualified Tct.Core.Data            as T
import qualified Tct.Core.Processor.Empty as E
import           Tct.Core.Common.Xml as Xml


import           Tct.Trs.Data.Problem
import           Tct.Trs.Data.Xml         ()
import           Tct.Trs.Data.CeTA

import Tct.Trs.Method.DP.UsableRules (usableRulesDeclaration)
import Tct.Trs.Method.DP.DependencyPairs (dependencyPairsDeclaration, dependencyTuplesDeclaration)
import Tct.Trs.Method.Poly.NaturalPI (polyDeclaration)


defaultDeclarations :: [T.StrategyDeclaration TrsProblem]
defaultDeclarations = 
  [ T.SD emptyDeclaration
  , T.SD usableRulesDeclaration
  , T.SD dependencyPairsDeclaration 
  , T.SD dependencyTuplesDeclaration 
  , T.SD polyDeclaration
  ]

empty :: T.Strategy TrsProblem
empty = E.empty isTrivial

emptyDeclaration :: T.Declaration ('[] T.:-> T.Strategy TrsProblem)
emptyDeclaration = T.declare "empty" [desc] () empty
  where desc = "Checks if the the strict components is empty."


--- * withCertification ----------------------------------------------------------------------------------------------

data WithCertificationProcessor = 
  WithCertificationProc { allowPartial :: Bool, onStrategy :: T.Strategy TrsProblem } deriving Show

-- TODO: 
-- MS: the only way to stop a computation currently is using throwError;
-- we could extend the Continue with Stop ?
type WithCertificationProof = ()

instance T.Processor WithCertificationProcessor where
  type ProofObject WithCertificationProcessor = WithCertificationProof
  type Problem WithCertificationProcessor     = TrsProblem

  solve p prob = do
    ret <- T.evaluate (onStrategy p) prob
    let prover = if allowPartial p then partialProof else totalProof
    errM <- case prover (T.fromReturn ret) of
      Left r    -> return $ Left (show r)
      Right xml ->
        liftIO $ withSystemTempFile "ceta" $ \file hfile -> do
          Xml.putXmlHandle xml hfile
          hFlush hfile
          hClose hfile
          (code , stdout, stderr) <- readProcessWithExitCode "ceta" [file] ""
          return $ case code of
            ExitFailure i -> Left $ "Error(" ++ show i ++ "," ++ show stderr ++ ")"
            ExitSuccess   -> case lines stdout of
              "CERTIFIED <complexityProof>" :_ -> Right ret
              _               -> Left stdout
    either (throwError . userError) (return . id) errM

