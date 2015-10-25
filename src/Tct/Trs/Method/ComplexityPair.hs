-- | This module collects declarations for /Complexity Pairs/.
module Tct.Trs.Method.ComplexityPair
  ( complexityPairDeclarations
  , complexityPairArg
  ) where


import qualified Tct.Core.Common.Parser          as P
import qualified Tct.Core.Data                   as T
import qualified Tct.Core.Data                   as P (SParser)
import qualified Tct.Core.Parse                  as P

import           Tct.Trs.Data.ComplexityPair
import           Tct.Trs.Method.Matrix.NaturalMI (matrixCPDeclaration)
import           Tct.Trs.Method.Poly.NaturalPI   (polyCPDeclaration)


complexityPairDeclarations :: [ComplexityPairDeclaration]
complexityPairDeclarations =
  [ someComplexityPair polyCPDeclaration
  , someComplexityPair matrixCPDeclaration ]

cpsParser :: P.SParser ComplexityPair
cpsParser = P.choice ((\(CD d) -> P.declaration d) `fmap` complexityPairDeclarations)

complexityPairArg :: T.Argument 'T.Required ComplexityPair
complexityPairArg = T.arg "complexityPair" "<complexityPair>"
  [ "This argument specifies the complexity pair to apply." ]
  cpsParser
