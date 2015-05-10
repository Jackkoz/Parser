module Expressions where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import Common

data Expression =
    Exp Exp
    deriving (Eq,Ord,Show)

data Exp =
      EInt Int
    | Eor  Exp Exp
    | Eand Exp Exp
    | Eeq  Exp Exp
    | Elt  Exp Exp
    | Egt  Exp Exp
    | EAdd Exp Exp
    | ESub Exp Exp
    | EMul Exp Exp
    | EDiv Exp Exp
    | EMinus Exp
    | EVar Identifier
    | Etrue
    | Efalse
    deriving (Eq,Ord,Show)

evalE :: Expression -> Semantics Int
evalE (Exp exp) = do
    eval exp

eval :: Exp -> Semantics Int
eval (EInt i) = return i

eval (EVar id) = do
    Just loc <- asks (M.lookup (evalId id))
    Just val <- gets (M.lookup loc)
    return val

eval (Eor  exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    if (or [val1 /= 0, val2 /= 0])
        then return 1
        else return 0

eval (Eand  exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    if (and [val1 /= 0, val2 /= 0])
        then return 1
        else return 0

eval (Eeq  exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    if (val1 == val2)
        then return 1
        else return 0

eval (Egt  exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    if (val1 > val2)
        then return 1
        else return 0

eval (Elt  exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    if (val1 < val2)
        then return 1
        else return 0

eval (EAdd exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    return (val1 + val2)

eval (ESub exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    return (val1 - val2)

eval (EMul exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    return (val1 * val2)

eval (EDiv exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    return (div val1 val2)

--eval (EMinus Etrue)  = return 0
--eval (EMinus Efalse) = return 1
eval (EMinus exp) = do
    val <- eval exp
    return (-val)

eval (Etrue)  = return 1

eval (Efalse) = return 0
