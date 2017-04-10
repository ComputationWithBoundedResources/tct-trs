-- Parse.hs ---
--
-- Filename: Parse.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Thu Sep  4 12:21:55 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sat Apr  8 15:22:39 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 241
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


module Tct.Trs.Processor.ARA.ByInferenceRules.CmdLineArguments.Parse
    ( parseArgOpts
    ) where

import           Tct.Trs.Processor.ARA.ByInferenceRules.CmdLineArguments.Type
import           Tct.Trs.Processor.ARA.Exception

import           Control.Exception.Base                                       (throw)
import           Data.Foldable                                                (foldlM)
import           Data.Function                                                (on)
import           Data.List                                                    (sortBy)
import           System.Console.GetOpt
import           System.Environment                                           (getArgs,
                                                                               getProgName)

-- |These are the default options. They are used, if the
-- options do not get set specifically.
defaultOptions :: ArgumentOptions
defaultOptions = ArgumentOptions {
                   filePath = ""
                 , maxVectorLength = 1
                 , minVectorLength = 1
                 , uniqueConstrFuns = False
                 , separateBaseCtr = False
                 , tempFilePath = "/tmp"
                 , helpText = False
                 , keepFiles = False
                 , printInfTree = False
                 , verbose = False
                 , shift = False
                 , allowLowerSCC = False
                 , lowerbound = False
                 }

-- |This function defines the options, the function to be called, when
-- the option is set and its help text, in case the -h option gets passed.
--
-- Arguments: The help message to be displayed in case the -h option is set.
options :: [OptDescr (ArgumentOptions -> IO ArgumentOptions)]
options = sortBy (compare `on` (\(Option c _ _ _) -> c))
  [ Option ['d'] ["temp-dir"]
   (ReqArg (\str opts -> return $ opts { tempFilePath = str } ) "DIR" )
   "the temporary directory [Default: /tmp)]"

  , Option ['h'] ["help"]
   (NoArg (\opts -> return $ opts { helpText = True } ))
   "Print usage information."

  , Option ['c'] ["allow-child-sccs"]
  (NoArg (\opts -> return $ opts { allowLowerSCC = True }))
  "Allow reachable SCCs in the call graph to use the cost-free inference."

  , Option [] ["verbose"]
   (NoArg (\opts -> return $ opts { verbose = True } ))
   "Print more information, like input problem."

  , Option ['b'] ["no-base-ctr"]
   (NoArg (\opts -> return $ opts { shift = True } ))
   "Uses heuristics instead of base constructors [Default: False]."

  , Option ['l'] ["lowerbound"]
   (NoArg (\opts -> return $ opts { lowerbound = True } ))
   "Search for best case lowerbound instead of upperbound."

  , Option ['v'] ["max-vector-length"]
   (ReqArg (\str opts -> do
               let readRes = reads str :: [(Int, String)]
               if null readRes
                 then return (opts { maxVectorLength = 1 })
                 else return (opts { maxVectorLength = fst $ head readRes })) "INT")
    "Maximum length of vectors to use [Default: 1]."

  , Option ['m'] ["min-vector-length"]
   (ReqArg (\str opts -> do
               let readRes = reads str :: [(Int, String)]
               if null readRes
                 then return (opts { minVectorLength = 1 })
                 else return (opts { minVectorLength = fst $ head readRes })) "INT")
    "Minimum length of vectors to use [Default: 1]."

  , Option ['i'] ["inference-tree"]
   (NoArg (\opts -> return $ opts { printInfTree = True } ))
   "Print the inference trees."

  , Option ['k'] ["keep-files"]
   (NoArg (\opts -> return $ opts { keepFiles = not (keepFiles opts) } ))
   "Keep the SMT files."

  , Option ['u'] ["unique-fun"]
   (NoArg (\opts -> return $
            opts { uniqueConstrFuns = not (uniqueConstrFuns opts) } ))
   "Toggle constraints to gain unique function signatures [Default: Disabled]."

  , Option ['s'] ["separate-base-ctr"]
   (NoArg (\opts -> return $
            opts { separateBaseCtr = not (separateBaseCtr opts) } ))
   "Use different base vectors for the constructors of cost free (cf) and non-cf signatures [Default: Disabled]."

  ]


-- |This function parses the Arguments. It gets them and then parses it, and
-- returns a ArgumentOptions object or throws an ioError Exception.
--
-- There is the possiblitiy of optionally giving the filePath. If it is not
-- given, then the default filepath will be taken and a warning will be
-- displayed.
parseArgOpts :: (Monad m) => IO (m ArgumentOptions)
parseArgOpts = do
  argv <- getArgs                                      -- get arguments
  progName <- getProgName                              -- get Program name

  let                                                  -- create help text
      header = "Usage: " ++ progName ++ " [OPTION...] filePath"
      helpMessage = usageInfo header options
      (o, files, err) = getOpt Permute options argv

  -- case errors occured, throw exception, else call functions for each option
  -- selected
  if not (null err)
    then throw $ FatalException $ concat err ++ "\n" ++ helpMessage
    else do
      opt <- foldlM (flip id) defaultOptions o
      if helpText opt
        then throw $ ShowTextOnly helpMessage
        else case files of
               [] ->  throw $
                     ShowTextOnly $ "Error: No input file was given!\n\n" ++ helpMessage
               [f] -> return $ return $ opt { filePath = f }
               (_ : _) -> throw $
                          FatalException $ "Could not parse command line arguments. " ++
                            "There were to many input files given. \n\n" ++ helpMessage


--
-- Parse.hs ends here
