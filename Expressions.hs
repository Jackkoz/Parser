module Expressions where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import Types
import AbsGram

evalE :: Expression -> Semantics Integer
evalE (Exp exp) = do
    eval exp

evalE (ExpTer bexp exp1 exp2) = do
    bvalue <- eval bexp
    val1 <- eval exp1
    val2 <- eval exp2
    if (bvalue == 0)
        then return val2
        else return val1

eval :: Exp -> Semantics Integer
eval (EInt i) = return i

eval (EVar id) = do
    loc <- asks (M.lookup (evalId id))
    case loc of
        Just loc -> do
            Just val <- gets (M.lookup loc)
            case val of
                IVal val -> do
                    return val
                CVal val -> do
                    return val
        Nothing  -> error ("Undeclared variable: " ++ (evalId id))


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

eval (Call id vals) = do
    Just loc <-asks (M.lookup (evalId id))
    Just f <- gets (M.lookup loc)
    case f of
        Func env rtype args rblock -> do
            env' <- createEnv env args vals
            local (const env') (evalRetBlock rblock)
            return 1


    where
    createEnv env [] [] = return env
    createEnv env (arg:args) (Cargs val:vals) = do
        case arg of
            Args ttype id -> do
                val' <- evalE val
                Just (IVal newLoc) <- gets (M.lookup 0)
                modify (M.insert newLoc (IVal val'))
                modify (M.insert 0 (IVal (newLoc+1)))
                env' <- (return $ M.insert (evalId(id)) newLoc env)
                createEnv env' args vals

eval (Etrue)  = return 1

eval (Efalse) = return 0

evalRetBlock (RBlock decls stmts exp) = do
    interpretB (decls stmts)
    return evalE exp
