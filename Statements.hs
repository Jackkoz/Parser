module Statements where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import Types
import AbsGram
import Expressions
import Declarations
import Assignements

interpret :: Stmt -> Semantics ()

interpret (SAssign a) = do
    interpretA a

interpret (SIf (If exp b eifs)) = do
    bval <- eval exp
    if bval == 0
        then interpretEIf eifs
        else interpretB b

interpret (SIfE (If exp b eifs) belse) = do
    bval <- eval exp
    if bval == 0
        then interpretEIfE eifs belse
        else interpretB b

interpret this@(SWhile exp block) = do
    bval <- eval exp
    if bval == 0
        then return ()
        else do
            interpretB block
            interpret this

interpret (Sprint Etrue) = do
    liftIO $ print "true"
interpret (Sprint Efalse) = do
    liftIO $ print "false"
interpret (Sprint exp) = do
    val <- eval exp
    liftIO $ print val
interpret (SprintS s) = do
    liftIO $ print s

interpret (SGuard ids block) = do
    makeConst ids
    interpretB block
    makeVar ids
    where
    makeConst ids = do
        mapM_ redeclareConst ids
    makeVar ids = do
        mapM_ redeclareVar ids

interpret (SFor exp1 exp2 id block) = do
    from <- eval exp1
    to <- eval exp2

    Just (IVal newLoc) <- gets (M.lookup 0)
    modify (M.insert newLoc (CVal from))
    modify (M.insert 0 (IVal (newLoc+1)))
    env <- ask
    env' <- (return $ M.insert (evalId(id)) newLoc env)

    doFor newLoc env' to
    where
    doFor loc env to = do
        Just (CVal val) <- gets (M.lookup loc)
        if (val <= to) then do
            local (const env) (interpretB block)
            modify (M.insert loc (CVal (val + 1)))
            doFor loc env to
        else
            return ()

interpretEIfE :: [EIf] -> Block -> Semantics ()
interpretEIfE [] belse = interpretB belse

interpretEIfE ((SEIf exp b):eifs) belse = do
    bval <- eval exp
    if bval == 0
        then interpretEIfE eifs belse
        else interpretB b

interpretEIf :: [EIf] -> Semantics ()
interpretEIf [] = return ()

interpretEIf ((SEIf exp b):eifs) = do
    bval <- eval exp
    if bval == 0
        then interpretEIf eifs
        else interpretB b

interpretB :: Block -> Semantics ()
interpretB (SBlock decls stmts) = do
    env' <- evalDecls decls
    local (const env') (mapM_ interpret stmts)