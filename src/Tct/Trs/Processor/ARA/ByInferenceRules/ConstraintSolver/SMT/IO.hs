{-# LANGUAGE OverloadedStrings #-}
-- IO.hs ---
--
-- Filename: IO.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Sun May 22 19:14:44 2016 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sat Apr  8 15:22:53 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 320
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

module Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.SMT.IO
    ( solveSMTProblem
    ) where

import           Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.SMT.ConvertToSMTProblem
import           Tct.Trs.Processor.ARA.ByInferenceRules.ConstraintSolver.SMT.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.Data.Type
import           Tct.Trs.Processor.ARA.ByInferenceRules.Operator
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Pretty
import           Tct.Trs.Processor.ARA.ByInferenceRules.Vector.Type
import           Tct.Trs.Processor.ARA.Exception

import           Control.Exception
                                                                                                  (throw)
import           Control.Lens
import           Control.Monad.State
import           Data.List
import qualified Data.Map                                                                        as M
import qualified Data.Set                                                                        as S
import qualified Data.Text                                                                       as T
import           System.IO
import qualified System.Process                                                                  as Cmd
import           Text.Parsec
import           Text.Parsec.Prim
import           Text.ParserCombinators.Parsec                                                   hiding
                                                                                                  (try)

import           Debug.Trace

-- (set-logic QF_LIA)
-- (declare-const x19 Int)
-- (declare-const x20 Int)
-- (declare-const x22 Int)
-- (declare-const x12 Int)
-- (declare-const x15 Int)
-- (assert (>= x19 0))
-- (assert (>= x20 0))
-- (assert (>= x22 0))
-- (assert (>= x12 0))
-- (assert (>= x15 0))
-- (assert (>= x19 x22))
-- (assert (>= (+ x22 (+ x12 x20)) (+ x15 2)))
-- (assert (> x15 (+ x20 x19)))
-- (check-sat)
-- (get-value (x19 x20 x22 x12 x15))


intro :: Bool -> T.Text
intro shift
  | shift = "(set-logic QF_LIA)\n(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x))\n"
  | otherwise = "(set-logic QF_NIA)\n(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x))\n"
  -- "(set-logic QF_LIA)\n"

outro :: [T.Text] -> T.Text
outro vars = "(check-sat)\n(get-value (" +++ T.unwords vars +++ "))"
-- outro vars = "(check-sat-using (then qe smt))\n(get-value (" ++ unwords vars ++ "))"

varsDecl :: [T.Text] -> T.Text
varsDecl = T.concat . map (\n -> "(declare-const " +++ n +++ " Int)\n")

fromComp :: Comparison -> T.Text
fromComp Eq  = "="
fromComp Geq = ">="

assertVarsGeq0 :: [T.Text] -> T.Text
assertVarsGeq0 vars =
  T.concat (map (\n -> "(assert (>= " +++ n +++ " 0))\n") vars)
  -- `T.append`
  -- T.concat (map (\n -> "(assert (<= " +++ n +++ " 20))\n") vars)

asserts :: [(T.Text, Comparison, T.Text)] -> T.Text
asserts =
  T.concat . map (\(l,c,r) -> "(assert (" +++ fromComp c +++ " " +++ l +++ " "
                   +++ r +++ "))\n")

assertsStr :: [T.Text] -> T.Text
assertsStr = T.concat . map (\s -> "(assert " +++ s +++ ")\n")

ifAsserts :: [([(T.Text, T.Text)], [(T.Text,T.Text)])] -> T.Text
ifAsserts =
  T.concat . map (\(conds,xs) -> "(assert (ite " +++ toAndList conds +++ " " +++
                                 toAndList xs +++ " true))\n")

toAndList :: [(T.Text, T.Text)] -> T.Text
toAndList conds =
  if length conds > 1
  then bef +++ head condEq +++ " " +++ T.intercalate ") " (tail condEq) +++ ")"
  else head condEq
  where condEq = map (\(bl, br) -> "(= " +++ bl +++ " " +++ br +++ ")") conds
        bef = T.concat $ map (const "(and ") [1..length condEq-1]


solveSMTProblem :: Bool -> Bool -> FilePath -> StateT SMTProblem IO (M.Map String Int)
solveSMTProblem shift keepFiles tempDir = do

  vs <- fmap S.elems (gets (^. vars))
  ass <- gets (^. assertions)
  assStr <- gets (^. assertionsStr)
  ifs <- gets (^. ifs)

  let txt = intro shift +++ varsDecl vs +++ assertVarsGeq0 vs +++ ifAsserts ifs +++
        asserts ass +++ assertsStr assStr +++ outro vs

  -- create the temporary files
  (pName, pHandle) <- liftIO (openTempFile tempDir "SMTP")
  (sName, sHandle) <- liftIO (openTempFile tempDir "SMTS")

  -- write to the temporary file
  liftIO (hPutStrLn pHandle (T.unpack txt))

  -- close the files
  liftIO (hClose pHandle)
  liftIO (hClose sHandle)

  -- execute binary and read in solution
  bin <- gets (^. programName)
  args <- gets (^. programOptions)
  let args' = unwords (map T.unpack args)

  -- Cmd.system
  _ <- liftIO (Cmd.system $
               T.unpack bin ++ " " ++ args' ++ " " ++ pName ++ " > " ++ sName)
  solStr <- liftIO (readFile sName)
  unless keepFiles
    (liftIO (void (Cmd.system ("rm " ++ pName  ++ " "  ++ sName ))))


  case parse smtSolveResult sName solStr of
    Left err -> fail (show err)
    Right xs -> return (M.fromList xs)


smtSolveResult :: Parser [(String, Int)]
smtSolveResult = unkown <|> unsolveable <|> solution <|> parseError


parseError :: Parser a
parseError = throw $ ParseException "Could not parse solution. Programming error."

unkown :: Parser a
unkown = do
  _ <- try (string "unknown")
  parserFail "The smt solver returned 'unkown'."


unsolveable :: Parser a
unsolveable = do
  _ <- string "unsat"
  fail "The smt problem could not be solved (was unsat)."


solution :: Parser [(String, Int)]
solution = do
  _ <- string "sat" >> spaces
  _ <- char '('
  v <- many varMap
  _ <- char ')' >> spaces
  _ <- eof
  return v

varMap :: Parser (String, Int)
varMap = do
  _ <- spaces >> char '('
  n <- name
  _ <- spaces
  v <- int
  _ <- char ')' >> spaces
  return (n, v)

name :: Parser String
name = do
  l <- letter
  r <- many (alphaNum <|> char '_' <|> char '\'')
  return $ l:r


int :: Parser Int
int = do
  ds <- (do
          nr <- char '-'
          d <- many digit
          return (nr:d)
        ) <|> many digit
  return (read ds :: Int)


--
-- IO.hs ends here
