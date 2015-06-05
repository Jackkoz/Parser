module Assignements where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import Types
import AbsGram
import Expressions

checkConst (id) = do
    Just loc <-asks (M.lookup (evalId id))
    Just val <- gets (M.lookup loc)
    case val of
        CVal val -> do
            error ("Illegal assignement to const variable: " ++ (evalId id))
        IVal val -> return ()

interpretA :: Assignment -> Semantics ()
interpretA (Assign id exp) = do
    checkConst(id)
    val <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    modify (M.insert loc (IVal val))

interpretA (AArith id AAPlus exp) = do
    checkConst(id)
    val1 <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    Just (IVal val2) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val1 + val2)))

interpretA (AArith id AAMinus exp) = do
    checkConst(id)
    val1 <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    Just (IVal val2) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val2 - val1)))

interpretA (AArith id AAMulti exp) = do
    checkConst(id)
    val1 <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    Just (IVal val2) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val1 * val2)))

interpretA (AArith id AADiv exp) = do
    checkConst(id)
    val1 <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    Just (IVal val2) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (div val2  val1)))

interpretA (AIncDec id Increment) = do
    checkConst(id)
    Just loc <-asks (M.lookup (evalId id))
    Just (IVal val) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val + 1)))

interpretA (AIncDec id Decrement) = do
    checkConst(id)
    Just loc <-asks (M.lookup (evalId id))
    Just (IVal val) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val - 1)))