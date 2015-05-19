module Tct.Trs.Data.Problem
  (
  -- * problem
    Problem (..)

  , dependencyGraph
  , congruenceGraph
  , allComponents
  , dpComponents
  , trsComponents
  , strictComponents
  , weakComponents
  , startComponents
  , ruleSet

  -- * construction
  , fromRewriting

  -- * updates
  , sanitiseDPGraph
  , toInnermost
  , toFull
  , toDC
  , toRC

  -- * properties
  , progressUsingSize
  , isDPProblem
  , isDTProblem
  , isRCProblem
  , isDCProblem
  , isInnermostProblem
  , isTrivial

  , note
  , isDPProblem'
  , isDTProblem'
  , isRCProblem'
  , isDCProblem'
  , isInnermostProblem'

  , noWeakComponents
  , noWeakComponents'

  -- * instance
  , TrsProblem
  , F
  , V
  , markFun
  , compoundf
  , isCompoundf
  ) where


import           Control.Applicative          ((<|>))
import qualified Data.ByteString.Char8        as BS
import qualified Data.Set                     as S
import           Data.Typeable

import qualified Data.Rewriting.Problem       as R
import qualified Data.Rewriting.Rule          as R (Rule (..))
import qualified Data.Rewriting.Term          as R

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml

import           Tct.Trs.Data.DependencyGraph (CDG, DG, DependencyGraph)
import qualified Tct.Trs.Data.DependencyGraph as DPG
import           Tct.Trs.Data.ProblemKind
import           Tct.Trs.Data.RuleSet
import           Tct.Trs.Data.Trs             (Trs)
import qualified Tct.Trs.Data.Trs             as Trs

import           Tct.Trs.Data.Signature       (Signature)
import qualified Tct.Trs.Data.Signature       as Sig



--- * trs problem ----------------------------------------------------------------------------------------------------

-- MS:
-- following properties should hold, when updating the problem (NOTE: there are not checked)
-- the DP/TRS components are mutually distinct
-- the signature contains all symbols of the DP/TRS components and all symbols stored in the start terms
-- the dp graph corrensponds to the DP components. is empty if the DP components are empty

-- NOTE: the dp graph stores DP rules as well as a Flag that indiciates wether it belongs to the strict/weak component
-- this information has to be updated when the dp components of the problem are updated
-- use santisieDPGraph to re-compute the graph


-- | The problem type parameterised in the function symbol and variable type.
data Problem f v = Problem
  { startTerms :: StartTerms f
  , strategy   :: Strategy
  , signature  :: Signature f

  , strictDPs  :: Trs f v
  , strictTrs  :: Trs f v
  , weakDPs    :: Trs f v
  , weakTrs    :: Trs f v

  , dpGraph    :: DependencyGraph f v
  } deriving (Show, Eq, Typeable)


-- | Returns the dependency graph of the problem.
dependencyGraph :: Problem f v -> DG f v
dependencyGraph = DPG.dependencyGraph . dpGraph

-- | Retruns the congruence of the problem.
congruenceGraph :: Problem f v -> CDG f v
congruenceGraph = DPG.congruenceGraph . dpGraph

strictComponents, weakComponents, allComponents :: (Ord f, Ord v) => Problem f v -> Trs f v
strictComponents prob = strictDPs prob `Trs.concat` strictTrs prob
weakComponents prob   = weakDPs prob `Trs.concat` weakTrs prob
allComponents prob    = strictComponents prob `Trs.concat` weakComponents prob

dpComponents, trsComponents :: (Ord f, Ord v) => Problem f v -> Trs f v
dpComponents prob  = strictDPs prob `Trs.concat` weakDPs prob
trsComponents prob = strictTrs prob `Trs.concat` weakTrs prob

-- | Returns all rules a reduction wrt to the start terms can start with.
startComponents :: (Ord f, Ord v) => Problem f v -> Trs f v
startComponents prob = case st of
  AllTerms{}   -> k (trsComponents prob)
  BasicTerms{} -> k (dpComponents prob)
  where
    st = startTerms prob
    k  = Trs.filter (isStartTerm st . R.lhs)

-- | Returns all rules.
ruleSet :: Problem f v -> RuleSet f v
ruleSet prob = RuleSet
  { sdps = strictDPs prob
  , wdps = weakDPs prob
  , strs = strictTrs prob
  , wtrs = weakTrs prob }


--- ** construction --------------------------------------------------------------------------------------------------

-- TODO: MS: add sanity check of symbols;
-- we use a wrapper for distinguishing dp/com symbols; but pretty printing can still fail if a symbols c_1 or f# exists
-- are there any conventions?

-- NOTE: MS: the tpdb contains non-wellformed examples; with free vars on the rhs
-- the current implementation is not designed to deal with them; we catch them in 'fromRewriting'

-- | Transforms a 'Data.Rewriting.Problem' into a 'TrsProblem'.
fromRewriting :: R.Problem String String -> Either String TrsProblem
fromRewriting prob = 
  if Trs.isWellformed sTrs && Trs.isWellformed wTrs
    then
      Right Problem
        { startTerms   = case R.startTerms prob of
            R.AllTerms   -> AllTerms (defs `S.union` cons)
            R.BasicTerms -> BasicTerms defs cons
        , strategy = case R.strategy prob of
            R.Innermost -> Innermost
            R.Full      -> Full
            R.Outermost -> Outermost
        , signature  = sig

        , strictDPs  = Trs.empty
        , strictTrs  = sTrs
        , weakDPs    = Trs.empty
        , weakTrs    = wTrs

        , dpGraph = DPG.empty }
    else
      Left "problem not wellformed."
  where
    toFun (R.Rule l r) = let k = R.map (F . TrsFun . BS.pack) (V . BS.pack) in R.Rule (k l) (k r)
    sTrs = Trs.fromList . map toFun $ R.strictRules (R.rules prob)
    wTrs = Trs.fromList . map toFun $ R.weakRules (R.rules prob)
    trs  = sTrs `Trs.union` wTrs

    sig  = Trs.signature trs
    defs = Sig.defineds sig
    cons = Sig.constructors sig


--- ** updates  ------------------------------------------------------------------------------------------------------

-- | Computes the dpGraph from the DP components of the problem and updates the dpGraph component of the Problem.
sanitiseDPGraph :: (Ord f, Ord v) => Problem f v -> Problem f v
sanitiseDPGraph prob = prob
  { dpGraph = DPG.estimatedDependencyGraph (ruleSet prob) (strategy prob) }

-- | Sets the innermost flag.
toInnermost :: Problem f v -> Problem f v
toInnermost prob = prob { strategy = Innermost }

-- | Sets the full flag.
toFull :: Problem f v -> Problem f v
toFull prob = prob { strategy = Full }

-- | Sets terms to basic terms; preserves the set of start symbols.
toDC :: (Ord f, Ord v) => Problem f v -> Problem f v
toDC prob = case startTerms prob of
  AllTerms{}       -> prob
  BasicTerms ds cs -> prob { startTerms = AllTerms (ds `S.union` cs) }

-- | Sets basic terms to terms; preserves the set of start symbols.
toRC :: (Ord f, Ord v) => Problem f v -> Problem f v
toRC prob = case startTerms prob of
  BasicTerms{} -> prob
  AllTerms fs  -> prob { startTerms = BasicTerms (fs `S.intersection` ds) (fs `S.intersection` cs) }
  where (ds,cs) = (Sig.defineds $ signature prob, Sig.constructors $ signature prob)


--- ** properties ----------------------------------------------------------------------------------------------------

progressUsingSize :: Problem f v -> Problem f v -> Bool
progressUsingSize p1 p2 =
  Trs.size (strictDPs p1) /= Trs.size (strictDPs p2)
  || Trs.size (strictTrs p1) /= Trs.size (strictTrs p2)
  || Trs.size (weakDPs p1) /= Trs.size (weakDPs p2)
  || Trs.size (weakTrs p1) /= Trs.size (weakTrs p2)

isDPProblem :: Problem f v -> Bool
isDPProblem prob = not $ Trs.null (strictDPs prob) && Trs.null (weakDPs prob)

isDTProblem :: Problem f v -> Bool
isDTProblem prob = isDPProblem prob && Trs.null (strictTrs prob)

isRCProblem, isDCProblem :: Problem f v -> Bool
isRCProblem prob = case startTerms prob of
  BasicTerms{} -> True
  _            -> False
isDCProblem prob = case startTerms prob of
  AllTerms{} -> True
  _          -> False


note :: Bool -> String -> Maybe String
note b st = if b then Just st else Nothing

isDPProblem' :: Problem f v -> Maybe String
isDPProblem' prob = note (not $ isDPProblem  prob) " not a DP problem"

isDTProblem' :: Problem f v -> Maybe String
isDTProblem' prob = isDPProblem' prob <|> note (not $ Trs.null (strictTrs prob)) " contains strict rules"

isRCProblem', isDCProblem' :: Problem f v -> Maybe String
isRCProblem' prob = note (not $ isRCProblem  prob) " not a RC problem"
isDCProblem' prob = note (not $ isDCProblem  prob) " not a DC problem"

isInnermostProblem :: Problem f v -> Bool
isInnermostProblem prob = strategy prob == Innermost

isInnermostProblem' :: Problem f v -> Maybe String
isInnermostProblem' prob = note (not $ isInnermostProblem prob) "not an innermost problem"

-- | A problem is trivial, if the strict DP/TRS components are empty.
isTrivial :: (Ord f, Ord v) => Problem f v -> Bool
isTrivial prob = Trs.null (strictComponents prob)

noWeakComponents :: (Ord f, Ord v) =>  Problem f v -> Bool
noWeakComponents = Trs.null . weakComponents

noWeakComponents' :: (Ord f, Ord v) => Problem f v -> Maybe String
noWeakComponents' prob = note (not $ noWeakComponents prob) " contains weak components "


--- * problem instance -----------------------------------------------------------------------------------------------

-- MS:
-- it would be no problem to keep the symbol type and variable type abstract; provided one defines a suitable class
-- yet it gets annoying when defining processors / strategies

type TrsProblem = Problem F V

-- | Annotated function symbol.
data AFun f
  = TrsFun f
  | DpFun f
  | ComFun Int
  deriving (Eq, Ord, Show, Typeable)

newtype F = F (AFun BS.ByteString)
  deriving (Eq, Ord, Show, Typeable)

newtype V = V BS.ByteString
  deriving (Eq, Ord, Show, Typeable)

-- | Transforms a function symbol into a dependency pair symbol.
markFun :: F -> F
markFun (F (TrsFun f)) = F (DpFun f)
markFun _              = error "Tct.Trs.Data.Problem.markFun: not a trs symbol"

-- | Returns a compound symbol with the given index.
compoundf :: Int -> F
compoundf = F . ComFun

-- | Checks wether the symbol is a compound symbol.
isCompoundf :: F -> Bool
isCompoundf (F (ComFun _)) = True
isCompoundf _              = False


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty V where
  pretty (V v) = PP.text (BS.unpack v)

instance Xml.Xml V where
  toXml (V v) = Xml.elt "var" [Xml.text (BS.unpack v)]
  toCeTA      = Xml.toXml

instance PP.Pretty BS.ByteString where
  pretty = PP.text . BS.unpack

instance Xml.Xml BS.ByteString where
  toXml  = Xml.text . BS.unpack
  toCeTA = Xml.text . BS.unpack

instance PP.Pretty F where
  pretty (F (TrsFun f)) = PP.text (BS.unpack f)
  pretty (F (DpFun f))  = PP.text (BS.unpack f) PP.<> PP.char '#'
  pretty (F (ComFun i)) = PP.pretty "c_" PP.<> PP.int i

instance Xml.Xml F where
  toXml (F (TrsFun f)) = Xml.elt "name" [Xml.text $ BS.unpack  f]
  toXml (F (DpFun f))  = Xml.elt "sharp" [Xml.elt "name" [Xml.text $ BS.unpack f]]
  toXml (F (ComFun f)) = Xml.elt "name" [Xml.text $ 'c':show f]
  toCeTA = Xml.toXml


instance (Ord f, PP.Pretty f, PP.Pretty v) => PP.Pretty (Problem f v) where
  pretty prob = PP.vcat
    [ PP.text "Strict DP Rules:"
    , PP.indent 2 $ PP.pretty (strictDPs prob)
    , PP.text "Strict TRS Rules:"
    , PP.indent 2 $ PP.pretty (strictTrs prob)
    , PP.text "Weak DP Rules:"
    , PP.indent 2 $ PP.pretty (weakDPs prob)
    , PP.text "Weak TRS Rules:"
    , PP.indent 2 $ PP.pretty (weakTrs prob)
    , PP.text "Signature:"
    , PP.indent 2 $ PP.pretty (signature prob)
    , PP.text "Kind:"
    , PP.indent 2 $ PP.pretty (strategy prob)
    , PP.indent 2 $ PP.pretty (startTerms prob) ]


-- MS: the ceta instance is not complete as it contains a tag <complexityClass> which depends on ProofTree
-- furthermore CeTA (2.2) only supports polynomial bounds; so we add the tag manually in the output
instance (Ord f, Ord v, Xml.Xml f, Xml.Xml v) => Xml.Xml (Problem f v) where
  toXml prob =
    Xml.elt "problem"
      [ Xml.elt "strictTrs"         [Xml.toXml (strictTrs prob)]
      , Xml.elt "weakTrs"           [Xml.toXml (strictTrs prob)]
      , Xml.elt "strictDPs"         [Xml.toXml (strictTrs prob)]
      , Xml.elt "weakDPs"           [Xml.toXml (strictTrs prob)] ]
  toCeTA prob =
    Xml.elt "complexityInput"
      [ Xml.elt "trsInput"
          [ Xml.elt "trs" [Xml.toXml (strictComponents prob)]
          , Xml.toCeTA (strategy prob)
          , Xml.elt "relativeRules" [Xml.toCeTA (weakComponents prob)] ]
      , Xml.toCeTA (startTerms prob, signature prob) ]

