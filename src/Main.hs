module Main where

import Tct
import Tct.Processors.Timeout

import Tct.Trs
import Tct.Trs.Poly.NaturalPolynomialInterpretation

main :: IO ()
main = applyMode $ trsMode 
  `withStrategies` [ SD poly, bestPolysSD, fastestPolysSD ]
  `withDefaultStrategy` timeoutIn 30 bestPolys
  
bestPolys :: Strategy (TrsProblem Fun Var)
bestPolys = es linear >=> es quadratic >=> es (mixed 2)
  where es = exhaustively

fastestPolys :: Strategy (TrsProblem Fun Var)
fastestPolys = exhaustively $ linear <||> quadratic <||> mixed 2 <||> mixed 3

withTimeout :: Strategy (TrsProblem Fun Var) -> Maybe Int -> Strategy (TrsProblem Fun Var)
withTimeout st (Just i) = timeoutIn i st
withTimeout st Nothing  = st

bestPolysSD :: StrategyDeclaration (TrsProblem Var Fun)
bestPolysSD = SD $ strategy "bestPolys" (OneTuple $ some nat) (withTimeout bestPolys)

fastestPolysSD :: StrategyDeclaration (TrsProblem Var Fun)
fastestPolysSD = SD $ strategy "fastestPolys" (OneTuple $ some nat) (withTimeout fastestPolys)

