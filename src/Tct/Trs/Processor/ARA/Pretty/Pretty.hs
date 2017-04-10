-- Pretty.hs ---
--
-- Filename: Pretty.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Wed Sep 17 09:05:42 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sun Apr  9 17:36:40 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 397
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

{-# LANGUAGE CPP #-}

-- | TODO: comment this module
module Tct.Trs.Processor.ARA.Pretty.Pretty
    ( prettyAraDatatype
    , prettyAraSignature
    , prettyAraProblem
    , prettyDtTuple
    )
    where
import           Data.Rewriting.Typed.Datatype
import           Data.Rewriting.Typed.Problem
import           Data.Rewriting.Typed.Rule
import           Data.Rewriting.Typed.Signature
import           Tct.Trs.Processor.ARA.ByInferenceRules.AnalyzerCost.Pretty
import           Tct.Trs.Processor.ARA.ByInferenceRules.TypeSignatures
import           Tct.Trs.Processor.ARA.Constants
import           Tct.Trs.Processor.ARA.Exception

import           Debug.Trace                                                (trace)

import           Control.Exception                                          (throw)
import           Data.List                                                  (find,
                                                                             intersperse)
import           Data.Maybe                                                 (fromMaybe)
import           Text.PrettyPrint
import qualified Text.PrettyPrint.ANSI.Leijen                               as L

printWhen' :: Bool -> Doc -> (Doc -> Doc)
printWhen' False _ = (empty <>)
printWhen' True  p = (p $+$ empty $+$ )
infixr 5 `printWhen'`


prettyAraProblem ::  ProblemSig -> Doc
prettyAraProblem prob = undefined
    -- printWhen' (sterms /= AllTerms) (block "STARTTERM" $ text "CONSTRUCTOR-BASED")
    -- $ printWhen' (strat /= Full) (block "STRATEGY" $ ppStrat strat)
    -- $ maybeblock "THEORY" theory ppTheories
    -- $+$ empty $+$ block "VAR" (ppTexts $ variables prob)
    -- $+$ empty $+$ maybeblock "DATATYPES" datatypes ppDatatypes
    -- $+$ empty $+$ maybeblock "SIGNATURES" signatures ppSigs
    -- $+$ empty $+$ block "RULES" (ppRules $ rules prob)
    -- $+$ empty $+$ maybeblock "COMMENT" comment text

  where block n pp = parens $ hang empty 3 $ text n $+$ empty $+$ pp
        maybeblock n f fpp = case f prob of
                               Just e  -> block n (fpp e)
                               Nothing -> empty

        ppStrat Innermost = text "INNERMOST"
        ppStrat Outermost = text "OUTERMOST"
        ppStrat Full      = error "Should not be possible."

        ppTexts vs = fsep [ text v | v <- vs]

        ppTheories thys = vcat [ppThy thy | thy <- thys]
            where ppThy (SymbolProperty p fs) = block p (fsep [ text f | f <- fs ])
                  ppThy (Equations rs)        = block "EQUATIONS" $ vcat [ppRule "==" r | r <- rs]

        ppRules rp = vcat ([ppRule "->" r | r <- strictRules rp]
                           ++ [ppRule "->=" r | r <- weakRules rp])

        ppRule sep' = text . show . prettyRule (L.pretty sep') L.pretty L.pretty

        ppDatatypes dts' = vcat [ ppDatatype dt | dt <- dts' ]
        ppDatatype = prettyAraDatatype ppCost ppCost
        ppCost = const empty

        ppSigs sigs        = vcat
#ifdef DEBUG
                             [ ppSig sig | sig <- sigs ]
#else
                             [ ppSig sig | sig <- filter ((\(_,_,r,_) -> not r) . lhsRootSym) sigs ]
#endif
        ppSig     = prettyAraSignature text ppCost
          (\(a,b) -> text a) -- <> text ":" <> hcat (intersperse (text ",") $
                                                 -- map ppCost b))

        dts = fromMaybe [] (datatypes prob)

        sterms = startTerms prob
        strat  = strategy prob
        thry   = theory prob


prettyAraDatatype :: (a -> Doc) -> (b -> Doc) -> Datatype (String, [a]) (String, b) -> Doc
prettyAraDatatype pA pB (Datatype (n, cst) chld) =
  hang empty 2 $ text n <> params <+> text "=" <+>
   text (if isRecursive chld then "µX.<" else "<")
   <+> prettyList' (prettyAraCtr pA pB) chld <+> text ">"
    where
          isRecursive = any (\(Constructor _ ch) -> any (\ctrCh -> case ctrCh of
                                                                   ConstructorRecursive -> True
                                                                   _ -> False
                                                                   ) ch)
          params =  if null (show txt)
                       then empty
                       else parens txt
                     where txt = prettyList' pA cst

prettyDtTuple :: (a -> Doc) -> (String, [a]) -> Doc
prettyDtTuple pCst (n, cst) =
  if null cst then empty else text n <> parens (prettyList' pCst cst)


prettyAraCtr :: (a -> Doc) -> (b -> Doc) -> Constructor (String, [a]) (String, b) -> Doc
prettyAraCtr pA pB (Constructor (cn, cst) []) =
    text cn <>  csts
      where csts = if null (show txt)
                      then empty
                      else text ":" <> txt
                    where txt = pB cst

prettyAraCtr pA pB (Constructor (cn,cst) chlds) =
    text cn <> ctrTxt <> cstTxt
    where ctrTxt = if null (show txt)
                   then empty
                   else parens txt
                   where txt = prettyList' (prettyAraCtrChld pA) chlds
          cstTxt = if null (show txt)
                      then empty
                      else text ":" <> txt
                   where txt = pB cst


prettyAraCtrChld :: (a -> Doc) -> ConstructorChild (String, [a]) -> Doc
prettyAraCtrChld _ ConstructorRecursive          = text "X"
prettyAraCtrChld _ (ConstructorDatatype (dt, _)) = text dt


prettyAraSignature :: (f -> Doc) -> (a -> Doc) -> (b -> Doc) -> Signature (f, a,c,d) b -> Doc
prettyAraSignature pF pCst pDt (Signature (n, cst, _,_) lhs' rhs') =
  hang empty 2 $ pF n <+> text "::" <+>
  pLhs <+> text "-" <> pCst cst <> text "->" <+> pDt rhs'
      where
        pLhs = brackets (hcat $ intersperse (text " x ") (map pDt  lhs'))


prettyList'     :: (a -> Doc) -> [a] -> Doc
prettyList' f l = hcat $ intersperse (comma <> space) (map f l)


--
-- Pretty.hs ends here
