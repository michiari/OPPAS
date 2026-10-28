{-# LANGUAGE LambdaCase #-}
{- |
   Module      : Pomc.Prob.Runtime
   Copyright   : 2026 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.Runtime( certifyPAST
                        , RewVarMap
                        ) where

import Prelude hiding (LT, GT)
import Pomc.Prob.ProbUtils
import Pomc.Prob.SupportGraph
import Pomc.Prob.FixPoint (retrieveEquations, FixpEq (PopEq), EqMap)
import Pomc.LogUtils (logDebugN, MonadLogger)

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import Data.Vector((!))
import qualified Data.HashTable.IO as HT

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad (forM, unless)
import Data.Maybe(fromJust, isJust)
import Z3.Monad

--- Computing the expected runtime to certify PAST ---------------------------------
-- Reference: "On Certificates, Expected Runtimes, and Termination Probabilities of pPDA", 
-- LICS 2023, Winkler and Katoen, Theorem 7
type RewVarKey = Int -- semiconfId_
type RewVarMap = HT.BasicHashTable Int AST

certifyPAST :: (MonadZ3 z3, MonadFail z3, MonadLogger z3)
  => [Int]
  -> EqMap (Double, Double)
  -> RewVarMap
  -> SupportGraph state
  -> (AST -> AST -> z3 AST)
  -> Bool
  -> z3 Bool
certifyPAST sccMembers eqMap rVarMap suppGraph mkComp expectPAST = do 
  -- preadding all equations
  pairs <- forM sccMembers $ \gnId_ -> do
    maybeVar <- liftIO $ HT.lookup rVarMap gnId_
    if isJust maybeVar
      then error "Encoding reward variable for a semiconf that has already been encoded."
      else do
        newVar <- mkFreshRealVar $ show gnId_
        liftIO $ HT.insert rVarMap gnId_ newVar
        return (gnId_, newVar)
  -- encoding all equations
  reset
  encodeReward pairs eqMap rVarMap suppGraph mkComp
  withModel (\model -> forM sccMembers $ \id_ -> do
                          var <- liftIO $ fromJust <$> HT.lookup rVarMap id_
                          evaluated <- fromJust <$> eval model var
                          liftIO $ HT.insert rVarMap id_ evaluated
                              ) >>= \case
    (Unsat, _) -> error "Fail to prove PAST."
    (Sat, _) -> do
      unless expectPAST $ error "Found a PAST certificate for a SCC which has upper bounds on termination probabilities proving non-AST."
      logDebugN "PAST certification succeeded."
      return True
    _ -> error "Undefined result when running the PAST certificate."
  
--helpers
encodeTransition :: MonadZ3 z3 => Prob -> AST -> z3 AST
encodeTransition prob_ toAST = do
  probReal <- mkRealNum prob_
  mkMul [probReal, toAST]
-- end helpers

encodeReward :: (MonadZ3 z3, MonadFail z3)
  => [(RewVarKey,AST)]
  -> EqMap (Double, Double)
  -> RewVarMap
  -> SupportGraph state
  -> (AST -> AST -> z3 AST)
  -> z3 ()
encodeReward pairs eqMap rVarMap suppGraph mkComp =
  let encode (gnId_, rewVar) = do
        let gn = suppGraph ! gnId_
            transitionCases (Push suppSet pushMap) = 
              encodeRewPush suppGraph eqMap rVarMap mkComp suppSet pushMap rewVar
            transitionCases (Shift shiftMap) = 
              encodeRewShift rVarMap mkComp shiftMap rewVar
            transitionCases (Pop _) = error "Trivial one rewards should be handled by the Termination algorithm."
        transitionCases (gnEdges gn)
  in mapM_ encode pairs

-- encoding helpers --
encodeRewPush :: (MonadZ3 z3)
  => SupportGraph state
  -> EqMap (Double, Double)
  -> RewVarMap
  -> (AST -> AST -> z3 AST)
  -> IntSet
  -> IntMap Prob
  -> AST
  -> z3 ()
encodeRewPush suppGraph eqMap rVarMap mkComp suppSet pushMap var = do
  pushInfo <- forM (IntMap.toList pushMap) (\(id_, prob_) -> do
    pushVar <- fromJust <$> (liftIO $ HT.lookup rVarMap id_)
    -- if we can find a solution with upper bound coefficient, 
    -- this solution holds also for the actual (uncomputable) coefficients
    rcs <- liftIO $ retrieveEquations eqMap id_ 
    encodedRcs <- forM rcs $ \(pushRC, PopEq (_,ub)) -> do 
      ubAST <- mkRealNum (ub :: Double)
      return (pushRC, ubAST)
    return (prob_, pushVar, encodedRcs))

  suppInfo <- forM (IntSet.toList suppSet) (\id_ -> do
    suppVar <- fromJust <$> (liftIO $ HT.lookup rVarMap id_)
    let suppStateId_ = getId . fst . semiconf $ suppGraph ! id_
    return (suppStateId_, suppVar))

  let terms = [(prob_,pushVar,
                    [[termVar,suppVar] |
                       (pushRC, termVar) <- rcs
                     , (suppStateId_, suppVar) <- suppInfo
                     , pushRC == suppStateId_
                    ]) |
                  (prob_, pushVar, rcs) <- pushInfo
             ]
  transitions <- forM terms (\(prob_,pushVar, suppTerms) -> do
    encodeTransition prob_ =<< (mkAdd . (pushVar :) =<< mapM mkMul suppTerms))
  one <- mkRealNum (1 :: Prob)
  assert =<< mkComp var =<< mkAdd (one:transitions)
  assert =<< mkGe var one

encodeRewShift :: MonadZ3 z3
  => RewVarMap
  -> (AST -> AST -> z3 AST)
  -> IntMap Prob
  -> AST
  -> z3 ()
encodeRewShift rVarMap mkComp shiftMap var =
  let shiftEnc (id_, prob_) = do
        toVar <- fromJust <$> (liftIO $ HT.lookup rVarMap id_)
        encodeTransition prob_ toVar
  in do
    transitions <- mapM shiftEnc (IntMap.toList shiftMap)
    one <- mkRealNum (1 :: Prob)
    assert =<< mkComp var =<< mkAdd (one:transitions)
    assert =<< mkGe var one
