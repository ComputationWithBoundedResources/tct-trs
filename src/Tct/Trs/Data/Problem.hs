module Tct.Trs.Data.Problem
  (
  TrsProblem (..)
  , Trs
  , Rule
  , Fun
  , Var
  , allRules
  , withBasicTerms
  , withAllTerms
  , closed
  , trsMode
  , CC
  ) where


import           Tct.Common.Answer          (answering)

import           Tct.Core.Common.Error
import qualified Tct.Core.Common.Pretty     as PP
import qualified Tct.Core.Common.Xml        as Xml
import           Tct.Core.Main
import           Tct.Core.Processor.Trivial (failing)

import           Data.Data                  (Typeable)
import           Data.List                  ((\\))
import qualified Data.Map.Strict            as M (Map, fromList, keys)

import qualified Data.Rewriting.Problem     as R
import qualified Data.Rewriting.Rule        as R (Rule (..))
import qualified Data.Rewriting.Term        as R (Term (..), funsDL, withArity)


data TrsProblem f v = TrsProblem
  { startTerms      :: R.StartTerms
  , rewriteStrategy :: R.Strategy
  , strictRules     :: [R.Rule f v]
  , weakRules       :: [R.Rule f v]
  , signature       :: M.Map f Int
  , constructors    :: [f]
  } deriving (Show, Typeable)

type Fun = String
type Var = String

type Rule = R.Rule Fun Var
type Trs  = TrsProblem Fun Var

allRules :: TrsProblem f v -> [R.Rule f v]
allRules prob = strictRules prob ++ weakRules prob

withBasicTerms, withAllTerms :: TrsProblem f v -> Bool
withBasicTerms prob = startTerms prob == R.BasicTerms
withAllTerms prob   = startTerms prob == R.AllTerms

closed :: TrsProblem f v -> Bool
closed = null . strictRules

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (TrsProblem f v) where
  pretty prob = PP.vcat
    [ PP.text "Strict Rules:"
    , PP.indent 2 $ PP.vcat (map PP.pretty $ strictRules prob)
    , PP.text "Weak Rules"
    , PP.indent 2 $ PP.vcat (map PP.pretty $ weakRules prob) ]

instance (Show f, Show v) => Xml.Xml (TrsProblem f v) where
  toXml a = Xml.elt "trs" [Xml.text $ show a]

data CC = DCF | DCI | RCF | RCI deriving (Eq, Read)

instance Show CC where
  show DCF = "DCF"
  show DCI = "DCI"
  show RCF = "RCF"
  show RCI = "RCI"


ccProperties :: CC -> (R.StartTerms, R.Strategy)
ccProperties cc = case cc of
  DCF -> (R.AllTerms,   R.Full)
  DCI -> (R.AllTerms,   R.Innermost)
  RCF -> (R.BasicTerms, R.Full)
  RCI -> (R.BasicTerms, R.Innermost)

parser :: String -> Either TctError (TrsProblem Fun Var)
parser s = case R.fromString s of
  Left e  -> Left $ TctParseError (show e)
  Right p -> Right TrsProblem
    { startTerms      = R.startTerms p
    , rewriteStrategy = R.strategy p
    , strictRules     = R.strictRules (R.rules p)
    , weakRules       = R.weakRules   (R.rules p)
    , signature       = sig
    , constructors    = consts }
    where
      rules = R.allRules (R.rules p)
      sig = M.fromList $ foldr k [] rules
        where k (R.Rule l r) = R.funsDL (R.withArity l) . R.funsDL (R.withArity r)
      consts = M.keys sig \\ froots
      froots = foldl k [] rules
        where
          k xs   (R.Rule (R.Fun f _) (R.Fun g _)) = f:g:xs
          k xs   (R.Rule (R.Fun f _) _        ) = f:xs
          k xs   (R.Rule _           (R.Fun g _)) = g:xs
          k xs _ = xs

options :: Options CC
options = option $ eopt
  `withArgLong` "complexity"
  `withCropped` 'c'
  `withHelpDoc` PP.text "RCF - runtime complexity"
  `withDefault` RCF

modifyer :: TrsProblem f v -> CC -> TrsProblem f v
modifyer p cc = p { startTerms = ts, rewriteStrategy = st }
  where (ts,st) = ccProperties cc

trsMode :: TctMode Trs CC
trsMode = TctMode
  { modeParser          = parser
  , modeStrategies      = []

  , modeDefaultStrategy = failing
  , modeOptions         = options
  , modeModifyer        = modifyer
  , modeAnswer          = answering }

