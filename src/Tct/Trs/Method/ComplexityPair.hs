module Tct.Trs.Method.ComplexityPair where

import qualified Tct.Core.Data as T
import qualified Tct.Core.Data as P (SParser, SParsable(..))
import qualified Tct.Core.Common.Parser as P
import qualified Tct.Core.Parse as P

import Tct.Trs.Data (TrsProblem)
import Tct.Trs.Data.ComplexityPair
-- import Tct.Trs.Method.Poly.NaturalPI (polyDeclarationCP)

--- * Complexity Pair Instances --------------------------------------------------------------------------------------

cps :: [ComplexityPairDeclaration]
cps = []--[ CD $ polyDeclarationCP ]

cpsParser :: P.SParser TrsProblem TrsProblem ComplexityPair
cpsParser = P.choice ((\(CD d) -> P.declaration d) `fmap` cps)

cpArg :: T.Argument 'T.Required ComplexityPair
cpArg = T.arg
  `T.withName` "complexityPair"
  `T.withHelp`
    [ "This argument the complexity pair to apply." ]

instance P.SParsable TrsProblem TrsProblem ComplexityPair where 
  parseS = cpsParser

