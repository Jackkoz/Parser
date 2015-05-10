module Assignements where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import Types
import Expressions

interpretA :: Assignment -> Semantics ()
interpretA (Assign id exp) = do
    val <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    modify (M.insert loc val)

interpretA (AArith id AAPlus exp) = do
    val1 <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    Just val2 <- gets (M.lookup loc)
    modify (M.insert loc (val1 + val2))

interpretA (AArith id AAMinus exp) = do
    val1 <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    Just val2 <- gets (M.lookup loc)
    modify (M.insert loc (val2 - val1))

interpretA (AArith id AAMulti exp) = do
    val1 <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    Just val2 <- gets (M.lookup loc)
    modify (M.insert loc (val1 * val2))

interpretA (AArith id AADiv exp) = do
    val1 <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    Just val2 <- gets (M.lookup loc)
    modify (M.insert loc (div val1  val2))

interpretA (AIncDec id Increment) = do
    Just loc <-asks (M.lookup (evalId id))
    Just val <- gets (M.lookup loc)
    modify (M.insert loc (val + 1))

interpretA (AIncDec id Decrement) = do
    Just loc <-asks (M.lookup (evalId id))
    Just val <- gets (M.lookup loc)
    modify (M.insert loc (val - 1))