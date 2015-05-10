module Types where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import AbsGram

type Loc = Integer
type Env = M.Map String Loc
type St  = M.Map Loc Integer

emptyEnv :: Env
emptyEnv = M.empty

initialSt :: St
initialSt = M.singleton 0 1

type Semantics a = ReaderT Env (StateT St IO) a

evalId :: Identifier -> String
evalId (Id id) = evalIdent id

evalIdent :: Ident -> String
evalIdent (Ident str) = str

takeLocation :: Identifier -> Semantics Loc
takeLocation id = do
    loc <- asks (M.lookup (evalId id))
    case loc of
        Just loc -> return loc
        Nothing  -> error ("Undeclared variable: " ++ (evalId id))

takeValue :: Loc -> Semantics Integer
takeValue loc = do
    Just val <- gets (M.lookup loc)
    return val