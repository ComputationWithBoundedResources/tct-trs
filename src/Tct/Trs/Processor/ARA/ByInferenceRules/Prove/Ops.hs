{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- Ops.hs ---
--
-- Filename: Ops.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Fri Sep  5 15:21:41 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sun Apr  9 17:30:01 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 1090
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

-- Code:

{-# LANGUAGE CPP                   #-}

-- | TODO: comment this module
module Tct.Trs.Processor.ARA.ByInferenceRules.Prove.Ops
    ( mapInfTreeNodes
    , mapInfTreeNodesVarNr
    , mapProvenInfTreeNodes
    , mapDatatypesVarNr
    , mapDatatypes
    , mapSignaturesVarNr
    , mapProveAB
    , mapProveAsB
    , mapProveABs
    , mapProveAsBs
    , mapRulesInfTreeNodesVar
    , accessorMaybe

    )
                        where


import           Data.Rewriting.Typed.Datatype
import           Data.Rewriting.Typed.Problem
import           Data.Rewriting.Typed.Rule
import           Data.Rewriting.Typed.Signature
import           Tct.Trs.Processor.ARA.ByInferenceRules.Prove.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures
import           Tct.Trs.Processor.ARA.Constants

import           Data.Maybe                                            (fromMaybe)
import           Debug.Trace                                           (trace)


-- | This function takes as input parameter another function which modifies a
-- tuple of a prove and an integer value. The Int refers to the variable number.
-- Therefore, if new variables get created by the function it has to update this
-- integer and set it accordingly in the return tuple, such that this function
-- can update the varNr field in the Prove data structure accordingly.
updateProve :: Show a => (Prove -> a)
            -> (Prove -> a -> Prove)
            -> ((Prove, a) -> (Prove, a))
            -> Prove -> Prove
updateProve accessor updateFun fun pr =
  let (nPr, nVal) = fun (pr, accessor pr)
  in updateFun nPr nVal


-- | @execFunOnProblem fun@ updates the problem from the State by using the
-- function @fun@. Afterwards it returns the number that was returned by the
-- function @fun@.
-- execFunOnProblem :: ((ProblemSig, a) -> (ProblemSig, a)) -> (ProblemSig, a) -> (ProblemSig, a)
-- execFunOnProblem fun (pr, nr) = fun (pr, nr)


-- | This function maps over the infTreeNodesToProve of the input prove. In case variables
-- get created one should use the postfix according to the given number in the
-- input of the function and increase the Int value of the output. It returns
-- the new prove, in which the varNr field is already set according to the
-- output integer value of the input function.
mapInfTreeNodesVarNr :: ((InfTreeNode, Int) -> (InfTreeNode, Int)) -> Prove -> Prove
mapInfTreeNodesVarNr = mapInfTreeNodes varNr updateVarNr

-- | @mapInfTreeNodes accessor updateFun fun pr@ can be used to iterate over the
-- infTreeNodesToProve of a prove @pr@. The function @fun@ will be applied to all
-- functions. An accumulator @a@ is used to hold the result of the function
-- @fun@. The input parameters to fun are retrieved using the specified
-- @accessor@ field of the Prove data-structure. The update function sets the
-- accumulated result from the function calls @fun@ through the function
-- @updateFunction@.
mapInfTreeNodes :: Show a => (Prove -> a)
                -> (Prove -> a -> Prove)
                -> ((InfTreeNode, a) -> (InfTreeNode, a))
                -> Prove -> Prove
mapInfTreeNodes = mapProveAsB infTreeNodesToProve (\p x -> p { infTreeNodesToProve = x })


mapProveAB :: Show b => (Prove -> a) -> (Prove -> a -> Prove) -> (Prove -> b) ->
              (Prove -> b -> Prove) -> ((a, b) -> (a, b)) -> Prove -> Prove
mapProveAB accessorIt updateIt accessorCum updateCum fun =
  updateProve accessorCum updateCum (iterateA fun accessorIt updateIt)

mapProveAsB :: Show b => (Prove -> [a]) -> (Prove -> [a] -> Prove) -> (Prove -> b) ->
               (Prove -> b -> Prove) -> ((a, b) -> (a, b)) -> Prove -> Prove
mapProveAsB accessorIt updateIt accessorCum updateCum fun =
  updateProve accessorCum updateCum (iterateAs fun accessorIt updateIt)

mapProveABs :: Show b => (Prove -> a) -> (Prove -> a -> Prove) -> (Prove -> [b]) ->
               (Prove -> [b] -> Prove) -> ((a, [b]) -> (a, [b])) -> Prove -> Prove
mapProveABs accessorIt updateIt accessorCum updateCum fun =
  updateProve accessorCum updateCum  (iterateA fun accessorIt updateIt)

mapProveAsBs :: Show b => (Prove -> [a]) -> (Prove -> [a] -> Prove) -> (Prove -> [b]) ->
                (Prove -> [b] -> Prove) -> ((a, [b]) -> (a, [b])) -> Prove -> Prove
mapProveAsBs accessorIt updateIt accessorCum updateCum fun =
  updateProve accessorCum updateCum  (iterateAs fun accessorIt updateIt)

-- | @updateFun pr nr@ is used to set the update Function for the prove @pr@ to
-- the variable number field @varNr@.
updateVarNr :: Prove -> Int -> Prove
updateVarNr pr nr = pr { varNr = nr }


mapRulesInfTreeNodesVar :: ((Rule String String, ([InfTreeNode], Int)) ->
                       (Rule String String, ([InfTreeNode], Int))) -> Prove -> Prove
mapRulesInfTreeNodesVar =
  mapProveAsB (allRules . rules . problem) const (\x -> (infTreeNodesToProve x, varNr x))
               (\p (x, y) -> p {infTreeNodesToProve = x, varNr = y })


-- | This function maps over the proven infTreeNodesToProve of the input prove. In
-- case variables get created one should use the postfix according to the given
-- number in the input of the function and increase the Int value of the output. It
-- returns the new prove, in which the varNr field is already set according to the
-- output integer value of the input function.
mapProvenInfTreeNodes :: ((InfTreeNode, Int) -> (InfTreeNode, Int)) -> Prove -> Prove
mapProvenInfTreeNodes = mapProveAsB provenInfTreeNodes (\p x -> p { provenInfTreeNodes = x }) varNr updateVarNr


-- | @iterateAs fun pr@ can be used to iterate over the problem of a prove. It
-- calls the given function @fun@ on the problem and updates the prove @pr@ with
-- the newly generated problem.
iterateProblemVarNr :: ((ProblemSig, Int) -> (ProblemSig, Int)) -> Prove -> Prove
iterateProblemVarNr = mapProveAB problem (\p x -> p { problem = x }) varNr updateVarNr


-- | @mapSignatures fun (pr, nr)@ maps over the signatures of a problem. It
-- saves an integer which is used as suffix for new variables during the
-- execution.
mapSignaturesVarNr :: ((SignatureSig, Int) -> (SignatureSig, Int)) -> Prove -> Prove
mapSignaturesVarNr fun = iterateProblemVarNr (iterateAs fun accessor update)
  where accessor :: ProblemSig -> [SignatureSig]
        accessor = accessorMaybe signatures

        update         :: ProblemSig -> [SignatureSig] -> ProblemSig
        update pr' sig = pr' { signatures = if null sig
                                               then Nothing
                                               else Just sig }


-- | @accessorMaybe fun prob@ is used to access a field using the function @fun@
-- from the problem @pr@. In case the field is @Nothing@ it will return the
-- empty list (@[]@).
accessorMaybe :: (ProblemSig -> Maybe [a]) -> ProblemSig -> [a]
accessorMaybe fun pr = fromMaybe [] (fun pr)


-- | @mapDatatypes fun (prob, nr)@ iterates over the datatypes of the problem
-- @prob@ executing the function @fun@ on each of the data-type elements. In
-- case no elements are given in the Maybe data-structure (Nothing or Just []),
-- then Nothing will be returned. The integer @nr@ is used to keep track of the
-- suffixes of the newly generated variables.
mapDatatypesVarNr :: ((DatatypeSig, Int) -> (DatatypeSig, Int)) -> Prove -> Prove
mapDatatypesVarNr fun =
  mapProveAB problem (\p x -> p { problem = x }) (const 0) const -- varNr updateVarNr
              (iterateAs fun accessor update)

  where accessor :: ProblemSig -> [DatatypeSig]
        accessor = accessorMaybe datatypes

        update :: ProblemSig -> [DatatypeSig] -> ProblemSig
        update p n = p { datatypes = if null n
                                       then Nothing
                                       else Just n }

-- type DatatypeSig = Datatype (String, [Cost Int]) (String, Cost Int)

-- | This function maps over the datatypes accumulating the result int the second
-- part of the tuple. It sets the resulting data-types using the first function,
-- and uses the specified update function to update the prove with the resulting
-- list @[a]@.
mapDatatypes :: Show a => (Prove -> [DatatypeSig] -> Prove)
             -> (Prove -> [a])
             -> (Prove -> [a] -> Prove)
             -> ((DatatypeSig, [a]) -> (DatatypeSig, [a]))
             -> Prove
             -> Prove
mapDatatypes = mapProveAsBs accessorIt

  where accessorIt :: Prove -> [DatatypeSig]
        accessorIt = accessorMaybe datatypes . problem


-- | This function updates a field using the input function. The accessor
-- specifies the access to the field to be updated. It will be called on the
-- input prove. The update function is used to update the prove data structure
-- with the result of the function calls using a foldl over the elements
-- retrieved using the accessor. The integer return value is supposed to be the
-- new variable counter. This means it is the input variable number + new
-- variables created using the given function (and not the number of new
-- variables).
iterateAs :: ((a, c) -> (a, c)) -> (b -> [a]) -> (b -> [a] -> b) -> (b, c) -> (b, c)
iterateAs fun accessor update (pr, nr) =
  do let (nVal, nAcc) = foldl f ([], nr) (accessor pr)
     (update pr nVal, nAcc)

  where f (acc, nr') ctx = let (nVal, nNr) = fun (ctx, nr')
                           in (acc ++ [nVal], nNr)


-- | This function updates a field using the input function. The @accessor@
-- specifies the function to access the field of the data-structure @pr@ to be
-- updated. It will be called on the input prove. The update function is used to
-- update the prove data structure with the result of the function call.
iterateA :: ((a, c) -> (a, c)) -> (b -> a) -> (b -> a -> b) -> (b, c) -> (b, c)
iterateA fun accessor update (pr, nr) =
         let (nVal, nNr) = fun (accessor pr, nr)
         in (update pr nVal, nNr)


--
-- Ops.hs ends here
