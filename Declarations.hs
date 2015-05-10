module Declarations where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import Types
import Expressions

evalDecl :: Decl -> Semantics Env
evalDecl (DAssign t id expr) = do
    Just newLoc <- gets (M.lookup 0)
    val <- evalE expr
    modify (M.insert newLoc val)
    modify (M.insert 0 (newLoc+1))
    env <- ask
    return $ M.insert (evalId(id)) newLoc env
evalDecl (Declr t id) = do
    Just newLoc <- gets (M.lookup 0)
    -- initialize to 0
    modify (M.insert newLoc 0)
    modify (M.insert 0 (newLoc+1))
    env <- ask
    return $ M.insert (evalId(id)) newLoc env

evalDecls :: [Decl] -> Semantics Env
evalDecls [] = ask
evalDecls (decl:decls) = do
  env' <- evalDecl decl
  local (const env') (evalDecls decls)