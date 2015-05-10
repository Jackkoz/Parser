module Statements where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import Types
import Expressions
import Declarations
import Assignements

interpret :: Stmt -> Semantics ()
interpret SSkip = return ()

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