-- Infer.hs ---
--
-- Filename: Infer.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Wed Nov  2 15:34:35 2016 (+0100)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sun Apr  9 21:53:59 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 45
-- URL:
-- Doc URL:
-- Keywords:
-- Compatibility:
--
--

-- Commentary:
--
--
--
--

-- Change Log:
--
--
--
--
--
--
--

-- Code:


module Tct.Trs.Processor.ARA.InferTypes
    ( inferTypesAndSignature
    ) where


import           Data.Rewriting.Typed.Datatype
import           Data.Rewriting.Typed.Problem
import           Data.Rewriting.Typed.Rule
import           Data.Rewriting.Typed.Signature


import           Control.Lens
import           Control.Monad.State
import           Data.List
import qualified Data.Map.Strict                as M
import qualified Data.Text                      as T
import           Text.PrettyPrint.ANSI.Leijen

import           Debug.Trace

type St = ( Problem String String String String String String
          , M.Map String Int
          , [String]
          )

inferTypesAndSignature :: Problem String String String String String String
                       -> Problem String String String String String String
inferTypesAndSignature prob = (^._1) $ execState infer (prob,M.empty,[])

infer :: State St ()
infer = do
  inferSigs
  inferTypes

getProblem :: State St (Problem String String String String String String)
getProblem = do
  st <- get
  return (st^._1)

inferSigs :: State St ()
inferSigs = do
  p <- getProblem
  let syms = nub $ symbols p

  let termColl m (Var v) = m
      termColl m (Fun f ch) =
        let m' = case M.lookup f m of
              Nothing -> M.insert f (length ch) m
              Just x -> if x == length ch
                       then m
                       else error $ "different number of parameters in function " ++ f
        in foldl termColl m' ch

  let ruls = allRules (rules p)
  let paramLen = foldl termColl M.empty (map lhs ruls ++ map rhs ruls)

  let definedFuns = nub $ map ((\(Fun f _) -> f). lhs) ruls
  let getSig f =
        let pLen = M.findWithDefault 0 f paramLen
        in Signature f (replicate pLen "A") "A"

  let definedFunsSigs = map getSig definedFuns
  modify $ _1 %~ (\x -> x { signatures = Just definedFunsSigs })
  modify $ _2 .~ paramLen
  modify $ _3 .~ filter (`notElem` definedFuns) syms

  -- trace ("problem: " ++ show (prettyWST' p))
  --   trace ("startTerms: " ++ show (startTerms p))
  --   trace ("symbols: " ++ show (symbols p))
  --   trace ("paramLen: " ++ show paramLen)
  --   trace ("definedFuns: " ++ show definedFuns)
  --   trace ("definedFunsSigs: " ++ show definedFunsSigs)
  --   undefined


getParamLens :: State St (M.Map String Int)
getParamLens = do
  st <- get
  return (st^._2)

getConstructorNames :: State St [String]
getConstructorNames = do
  st <- get
  return (st^._3)

inferTypes :: State St ()
inferTypes = do

  paramLens <- getParamLens
  constrs <- getConstructorNames
  let makeConstructors n =
        let len = M.findWithDefault 0 n paramLens
        in Constructor n (replicate len ConstructorRecursive)
  let dt = Datatype "A" $ map makeConstructors constrs

  modify $ _1 %~ (\x -> x { datatypes = Just [dt]})

  -- trace ("paramLens: " ++ show paramLens)
  --   trace ("constrs: " ++ show constrs)
  --   trace ("datatypes : " ++ show dt)

  --   undefined


--
-- Infer.hs ends here
