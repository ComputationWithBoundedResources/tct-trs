{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Trs.Method.Matrix.MatrixFun where


import qualified Data.Map as Map

import qualified Control.Monad.Trans as CMT
import qualified Control.Monad as CM

import qualified Tct.Common.SMT                     as SMT

import qualified Tct.Trs.Method.Matrix.Matrix as MX

import qualified Tct.Trs.Method.Matrix.Matrix as EncM


import qualified Tct.Trs.Method.Matrix.MatrixInterpretation as MI

import qualified Tct.Trs.Data.Signature as Sig

import qualified Tct.Core.Common.SemiRing as SR


-- test_scalarProduct = do
--   res :: SMT.Result ([Int],[Int],Int) <- CMT.liftIO $ SMT.solveStM (SMT.minismtW "scalarProduct.smt2") $ do
--     SMT.setFormat "QF_NIA"
--     a :: MX.Vector SMT.IExpr <- toNumVector $ MX.Vector [10,0,0]
--     b :: MX.Vector SMT.IExpr <- toNumVector $ MX.Vector [10,0,0]
--     c :: SMT.IExpr <-  SMT.nvarM'
--     let p :: SMT.IExpr = MX.scalarProduct a b
--     SMT.assert $ p SMT..== c
--     return $ SMT.decode (elemsVec a, elemsVec b,c)
--   print res


-- test_mProduct = do
--   res :: SMT.Result [[[Int]]] <- CMT.liftIO $ SMT.solveStM (SMT.minismtW "mProduct.smt2") $ do
--     SMT.setFormat "QF_NIA"
--     a <- toNumMatrix $ MX.Matrix $ map MX.Vector [[1,2,3],[4,5,6],[7,8,9]]
--     b <- toNumMatrix $ MX.Matrix $ map MX.Vector [[9,8,7],[6,5,4],[3,2,1]]
--     c <- variableMatrix (3,3)
--     SMT.assert $ eqMatrix (MX.mProduct a b) c
--     return $ SMT.decode [elemsMatrix a, elemsMatrix b, elemsMatrix c]
--   print res

-- test_bigmProduct = do
--   res :: SMT.Result [[[Int]]] <- CMT.liftIO $ SMT.solveStM (SMT.minismtW "bigmProduct.smt2") $ do
--     SMT.setFormat "QF_NIA"
--     a <- toNumMatrix $ MX.Matrix $ map MX.Vector [[1,2,3,4],[5,6,7,8],[9,10,11,12]]
--     b <- toNumMatrix $ MX.Matrix $ map MX.Vector [[12,11,10],[9,8,7],[6,5,4],[3,2,1]]
--     let ab3 = [a,b,a,b,a,b]
--     c <- variableMatrix (3,3)
--     SMT.assert $ eqMatrix (MX.bigmProduct ab3) c
--     return $ SMT.decode [elemsMatrix a, elemsMatrix b, elemsMatrix c]
--   print res

test =
  let sig = Sig.fromMap $ Map.fromList [("func",1)]
  in sig


isZeroExpr :: SMT.IExpr -> SMT.Formula SMT.IFormula
isZeroExpr e = e SMT..== SMT.zero

isZeroVector :: MX.Vector SMT.IExpr -> SMT.Formula SMT.IFormula
isZeroVector (MX.Vector es) = SMT.bigAnd $ map isZeroExpr es

isZeroMatrix :: MX.Matrix SMT.IExpr -> SMT.Formula SMT.IFormula
isZeroMatrix (MX.Matrix m) = SMT.bigAnd $ map isZeroVector m

applyConstraintOnEntry :: (SMT.IExpr -> SMT.Formula SMT.IFormula) -> Int -> Int -> MX.Matrix SMT.IExpr  -> SMT.Formula SMT.IFormula
applyConstraintOnEntry cfunc row col m = cfunc $ MX.mEntry row col m

isMonotoneMatrix :: MX.Matrix SMT.IExpr -> SMT.Formula SMT.IFormula
isMonotoneMatrix = applyConstraintOnEntry cfunc 1 1
  where
    cfunc e = e SMT..> SMT.zero

gtVec
  :: MX.Vector SMT.IExpr
  -> MX.Vector SMT.IExpr
  -> SMT.Formula SMT.IFormula
gtVec (MX.Vector v1) (MX.Vector v2) =
  let comps = zipWith (SMT..>) v1 v2
  in SMT.bigAnd comps

gtMatrix
  :: MX.Matrix SMT.IExpr
  -> MX.Matrix SMT.IExpr
  -> SMT.Formula SMT.IFormula
gtMatrix (MX.Matrix m1) (MX.Matrix m2) =
   let comps = zipWith gtVec m1 m2
   in SMT.bigAnd comps

eqVec
  :: MX.Vector SMT.IExpr
  -> MX.Vector SMT.IExpr
  -> SMT.Formula SMT.IFormula
eqVec (MX.Vector v1) (MX.Vector v2) =
  let comps = zipWith (SMT..==) v1 v2
  in SMT.bigAnd comps

eqMatrix
  :: MX.Matrix SMT.IExpr
  -> MX.Matrix SMT.IExpr
  -> SMT.Formula SMT.IFormula
eqMatrix (MX.Matrix m1) (MX.Matrix m2) =
   let comps = zipWith eqVec m1 m2
   in SMT.bigAnd comps

toNumList :: Monad m => [Int] -> m [SMT.IExpr]
toNumList cs = do
  ns <- CM.mapM SMT.numM cs
  return $ ns

toNumVector :: Monad m => MX.Vector Int -> m (MX.Vector SMT.IExpr)
-- is there a way to do this with MX.liftVector_
toNumVector (MX.Vector a) = toNumList a >>= (return . MX.Vector)


variableVector
  :: Int
  -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) (MX.Vector SMT.IExpr)
variableVector dim = do
  vs <- CM.replicateM dim SMT.nvarM'
  return $ MX.Vector vs

variableMatrix
  :: (Int,Int)
  -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) (MX.Matrix SMT.IExpr)
variableMatrix (x,y) = do
  rows <- CM.replicateM x (variableVector y)
  return $ MX.Matrix rows

elemsVec :: MX.Vector a -> [a]
elemsVec (MX.Vector es) = es

elemsMatrix :: MX.Matrix a -> [[a]]
elemsMatrix (MX.Matrix mx) = map elemsVec mx

toNumVectors :: Monad m => [MX.Vector Int] -> m [MX.Vector SMT.IExpr]
toNumVectors = mapM toNumVector

toNumMatrix :: Monad m => MX.Matrix Int -> m (MX.Matrix SMT.IExpr)
toNumMatrix (MX.Matrix mx) = toNumVectors mx >>= (return . MX.Matrix)


toSMTMatrixInterpretation :: (Ord fun) => MI.MatrixInterpretation fun MI.SomeIndeterminate (MI.MatrixInterpretationEntry fun) -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) (MI.MatrixInterpretation fun MI.SomeIndeterminate SMT.IExpr)
toSMTMatrixInterpretation mi = do
  let interps = Map.assocs $ MI.interpretations mi
  smtinterps <- mapM toSMTLinearInterpretation interps
  return $ mi { MI.interpretations = Map.fromList smtinterps}

toSMTLinearInterpretation :: (fun, MI.LinearInterpretation MI.SomeIndeterminate (MI.MatrixInterpretationEntry fun)) -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) (fun,MI.LinearInterpretation MI.SomeIndeterminate SMT.IExpr)
toSMTLinearInterpretation (f,li) = do
  constant <- toSMTVector $ MI.constant li
  coefficients <- mapM toSMTMatrix $ Map.assocs $ MI.coefficients li
  return (f, MI.LInter (Map.fromList coefficients) constant)
  where
    toSMTVector :: EncM.Vector (MI.MatrixInterpretationEntry fun) -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) (EncM.Vector SMT.IExpr)
    toSMTVector (EncM.Vector vec) = mapM entryToSMT vec >>= return . EncM.Vector
    toSMTMatrix  :: (MI.SomeIndeterminate, EncM.Matrix (MI.MatrixInterpretationEntry fun)) -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) (MI.SomeIndeterminate, EncM.Matrix SMT.IExpr)
    toSMTMatrix (i , EncM.Matrix vecs) = mapM toSMTVector vecs >>= (\m -> return (i, EncM.Matrix m))

entryToSMT :: MI.MatrixInterpretationEntry fun -> SMT.SolverM (SMT.SolverState (SMT.Formula SMT.IFormula)) SMT.IExpr
entryToSMT ent@(MI.MIVar{}) =
  if MI.restrict ent
  then SMT.snvarM'
  else SMT.nvarM'
entryToSMT MI.MIConstZero = return SMT.zero --SMT.numM 0
entryToSMT MI.MIConstOne = return SMT.one  -- SMT.numM 1
