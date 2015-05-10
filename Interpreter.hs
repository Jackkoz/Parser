module Interpreter where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import Types
import AbsGram
import Statements
import Expressions
import Declarations
import Assignements


interpretP :: Program -> Semantics ()
interpretP (Prog typeD decls funD b) = do
    env' <- evalDecls decls
    interpretB b

execProgram :: Program -> IO ()
execProgram p = do
    finalState <- execStateT (runReaderT (interpretP p) emptyEnv) initialSt
    return ()

test1 = Prog [] [DAssign TInt (Id (Ident "x")) (Exp (EInt 5)),DAssign TBool (Id (Ident "y")) (Exp Etrue)] [] (SBlock [] [SAssign (Assign (Id (Ident "x")) (Exp (EAdd (EVar (Id (Ident "x"))) (EInt 5)))),SAssign (Assign (Id (Ident "y")) (Exp Efalse))])

test2 = Prog [] [DAssign TInt (Id (Ident "x")) (Exp (EInt 5)),DAssign TBool (Id (Ident "y")) (Exp Etrue)] [] (SBlock [DAssign TInt (Id (Ident "x")) (Exp (EInt 5))] [SAssign (Assign (Id (Ident "x")) (Exp (EInt 5)))])

test3 = Prog [] [DAssign TInt (Id (Ident "x")) (Exp (EInt 5))] [] (SBlock [DAssign TInt (Id (Ident "x")) (Exp (EInt 6))] [SAssign (Assign (Id (Ident "x")) (Exp (EInt 7))), SIf (If Etrue (SBlock [] [SAssign (Assign (Id (Ident "x")) (Exp (EInt 8)))]) []) ])

testW = Prog [] [] [] (SBlock [DAssign TInt (Id (Ident "x")) (Exp (EInt 0))]    [SWhile (Elt (EVar (Id (Ident "x"))) (EInt 5)) (SBlock [] [SAssign (AIncDec (Id (Ident "x")) Increment)])])

test4 = Prog [] [] [] (SBlock [DAssign TInt (Id (Ident "x")) (Exp (EInt 5))] [SAssign (AIncDec (Id (Ident "x")) Increment),SIf (If Etrue (SBlock [] [SAssign (AIncDec (Id (Ident "x")) Increment)]) [SEIf Etrue (SBlock [] [SAssign (AIncDec (Id (Ident "x")) Increment)])]),SWhile Efalse (SBlock [] [SAssign (Assign (Id (Ident "x")) (Exp (EInt 0)))])])
