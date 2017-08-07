{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
-- Implementation details can be found in the technical report '@tba@'.
-- | This module provides the \CheckProperty\ processor, which will only check for
-- a certain property.
module Tct.Trs.Processor.CheckProperty
  ( checkPropDeclaration
  , checkProp
  , checkProp'
  , checkPropLogOpArg
  , checkPropLLArg
  , checkPropCtrArg
  , LogOp (..)
  , LL (..)
  , Ctr (..)
  ) where


import           Data.Maybe
import Data.List (intersperse)

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T
import qualified Tct.Core.Common.SemiRing        as SR

import           Tct.Common.ProofCombinators

import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem         as Prob
import qualified Tct.Trs.Data.Rules as RS


data CheckProp = CheckProp { logOp :: LogOp   -- ^ How to combine outcomes.
                           , ll :: Maybe LL   -- ^ Check for left-linearity
                           , ctr :: Maybe Ctr -- ^ Check for constructor TRS
                           }
               deriving Show


data LogOp = OR | AND           -- how to combine property check outcomes
         deriving (Bounded, Enum, Eq, Show)

data LL = IsLL | IsNotLL        -- left linearity
        deriving (Bounded, Enum, Eq, Show)
data Ctr = IsCtr | IsNotCtr     -- constructor TRS
         deriving (Bounded, Enum, Eq, Show)

class Pos x where
  pos :: x
  inv :: x -> x

instance Pos LL where
  pos = IsLL
  inv IsLL = IsNotLL
  inv IsNotLL = IsLL

instance Pos Ctr where
  pos = IsCtr
  inv IsCtr = IsNotCtr
  inv IsNotCtr = IsCtr

data CheckPropProof f v = CheckPropProof
  { proofLogOp :: LogOp

    -- results of checks
  , proofLL :: Maybe Bool
  , proofCtr   :: Maybe Bool

    -- what was checked for
  , checkLL :: Maybe LL
  , checkCtr :: Maybe Ctr

  } deriving Show


instance T.Processor CheckProp where
  type ProofObject CheckProp = ApplicationProof (OrientationProof (CheckPropProof F V))
  type In  CheckProp         = Prob.Trs
  type Out CheckProp         = Prob.Trs
  type Forking CheckProp     = T.Optional T.Id

  execute p probTcT =
    let op = logOp p
        rules = Prob.allComponents probTcT
        sigs = Prob.signature probTcT
        checkLLFun _ = RS.isLeftLinear rules
        checkCtrFun _ = RS.isConstructorTrs sigs rules

        chkLL = ll p
        prLL = maybe Nothing (Just . checkLLFun) chkLL

        chkCtr = ctr p
        prCtr = maybe Nothing (Just . checkCtrFun) chkCtr

    in T.succeedWith (Applicable . Order $ CheckPropProof op prLL prCtr chkLL chkCtr)
       (certification $ answer op chkLL chkCtr prLL prCtr)
       T.Null


answer :: LogOp -> Maybe LL -> Maybe Ctr -> Maybe Bool -> Maybe Bool -> Bool
answer op chkLL chkCtr prLL prCtr =
  (case op of
      AND -> all
      OR -> any)
  (\(a,b) -> a == b) $ concatMap (\(a,b) -> if isJust b then [(a,b)] else [])
  (zip [prLL,prCtr] chks)

  where cF x = if x == pos then True else False

        chks = [ cF <$> chkLL  -- testing for True/False values
               , cF <$> chkCtr
               ]


certification :: Bool -> T.Optional T.Id T.Certificate -> T.Certificate
certification comp cert = case cert of
  T.Null         -> T.yesNoCert comp
  T.Opt (T.Id c) -> T.updateYesNoCert c (`SR.add` comp)


-- instances

checkPropLogOpArg :: T.Argument 'T.Required LogOp
checkPropLogOpArg = T.flag
  "logOp"
  ["Specify the logical operation for combining outcomes of the property checks."]


checkPropLLArg :: T.Argument 'T.Required (Maybe LL)
checkPropLLArg = T.some $ T.flag
  "left-linear"
  ["Check for (non)-left-linarity."]

checkPropCtrArg :: T.Argument 'T.Required (Maybe Ctr)
checkPropCtrArg = T.some $ T.flag
  "constructorTRS"
  ["Check whether the TRS is a constructor TRS or not."]

description :: [String]
description = [ unwords
  [ "This processor only checks for one or more properties and the exits the program."] ]

propStrategy :: LogOp -> Maybe LL -> Maybe Ctr -> TrsStrategy
propStrategy op ll ctr = T.Apply (CheckProp op ll ctr)

checkPropDeclaration :: T.Declaration ( [T.Argument 'T.Optional LogOp
                                        ,T.Argument 'T.Optional (Maybe LL)
                                        ,T.Argument 'T.Optional (Maybe Ctr)
                                        ] T.:-> TrsStrategy)
checkPropDeclaration =
  T.declare "checkprop" description (logOp,llArg,ctrArg) propStrategy
  where logOp = checkPropLogOpArg `T.optional` AND
        llArg = checkPropLLArg `T.optional` Nothing
        ctrArg = checkPropCtrArg `T.optional` Nothing


checkProp :: TrsStrategy
checkProp = T.deflFun (checkPropDeclaration)

checkProp' :: LogOp -> Maybe LL -> Maybe Ctr -> TrsStrategy
checkProp' = T.declFun checkPropDeclaration


--- * proofdata
--------------------------------------------------------------------------------

instance PP.Pretty LogOp where
  pretty AND = PP.text " AND "
  pretty OR  = PP.text " OR "

instance PP.Pretty LL where
  pretty IsLL = PP.text "is left-linear"
  pretty IsNotLL = PP.text "is not left-linear"

instance PP.Pretty Ctr where
  pretty IsCtr = PP.text "is a constructor TRS"
  pretty IsNotCtr = PP.text "is not a constructor TRS"

instance (Ord f, PP.Pretty f, PP.Pretty v) => PP.Pretty (CheckPropProof f v) where
  pretty (CheckPropProof op prLL prCtr chkLL chkCtr) =
    -- Signatures
    if null questionList
    then PP.text "No properties were checked. Specify some using arguments."
    else PP.hcat [ maybe PP.empty (\x -> pretty chkLL x PP.<$> PP.empty) prLL
                 , maybe PP.empty (\x -> pretty chkCtr x PP.<$> PP.empty) prCtr
                 ] PP.<>
         PP.text "Overall Answer to question if TRS " PP.<> question PP.<> PP.colon
         PP.<+> PP.bool (answer op chkLL chkCtr prLL prCtr)

    where question = PP.hcat $ intersperse (PP.pretty op) questionList

          questionList = concat $ filter (not.null)
                     [ maybe [] (return . PP.pretty) chkLL
                     , maybe [] (return . PP.pretty) chkCtr
                     ]


          pretty Nothing _ = PP.empty
          pretty (Just (_::a)) o = PP.pretty (pos :: a) PP.<> PP.colon PP.<+> PP.pretty o


instance Xml.Xml (CheckPropProof f v) where
  toXml _ = Xml.empty

