module Declarations where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import Types
import AbsGram
import Expressions

evalDecl :: Decl -> Semantics Env
evalDecl (DAssign t id expr) = do
    Just (IVal newLoc) <- gets (M.lookup 0)
    val <- evalE expr
    modify (M.insert newLoc (IVal val))
    modify (M.insert 0 (IVal (newLoc+1)))
    env <- ask
    return $ M.insert (evalId(id)) newLoc env
evalDecl (Declr t id) = do
    Just (IVal newLoc) <- gets (M.lookup 0)
    -- initialize to 0
    modify (M.insert newLoc (IVal 0))
    modify (M.insert 0 (IVal (newLoc+1)))
    env <- ask
    return $ M.insert (evalId(id)) newLoc env
evalDecl (DConstDec t id expr) = do
    Just (IVal newLoc) <- gets (M.lookup 0)
    val <- evalE expr
    modify (M.insert newLoc (CVal val))
    modify (M.insert 0 (IVal (newLoc+1)))
    env <- ask
    return $ M.insert (evalId(id)) newLoc env

evalDecls :: [Decl] -> Semantics Env
evalDecls [] = ask
evalDecls (decl:decls) = do
  env' <- evalDecl decl
  local (const env') (evalDecls decls)

redeclareConst :: Identifier -> Semantics ()
redeclareConst id = do
    Just loc <-asks (M.lookup (evalId id))
    Just val <- gets (M.lookup loc)
    case val of
        IVal val -> do
            modify (M.insert loc (CVal val))
        CVal val -> do
            error ("Incorrect parameter in guard statement, already a constant: " ++ evalId(id))

redeclareVar :: Identifier -> Semantics ()
redeclareVar id = do
    Just loc <-asks (M.lookup (evalId id))
    Just (CVal val) <- gets (M.lookup loc)
    modify (M.insert loc (IVal val))

evalFuncDecl :: FunctionDeclaration -> Semantics Env
evalFuncDecl (FDec id args rtype rblock) = do
    Just (IVal newLoc) <- gets (M.lookup 0)

    modify (M.insert 0 (IVal (newLoc+1)))
    env <- ask
    env' <- return $ M.insert (evalId(id)) newLoc env
    modify (M.insert newLoc (Func env' rtype args rblock))
    return env'

evalFuncDecls :: [FunctionDeclaration] -> Semantics Env
evalFuncDecls [] = ask
evalFuncDecls (decl:decls) = do
  env' <- evalFuncDecl decl
  local (const env') (evalFuncDecls decls)