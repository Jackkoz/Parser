module Common where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

data Type =
      TInt
    | TBool
    deriving (Eq,Ord,Show)

newtype Ident = Ident String
    deriving (Eq,Ord,Show)

data Identifier = Id Ident
    deriving (Eq,Ord,Show)

type Loc = Int
type Env = M.Map String Loc
type St  = M.Map Loc Int

emptyEnv :: Env
emptyEnv = M.empty

initialSt :: St
initialSt = M.singleton 0 1

type Semantics a = ReaderT Env (State St) a

evalId :: Identifier -> String
evalId (Id id) = evalIdent id

evalIdent :: Ident -> String
evalIdent (Ident str) = str

takeLocation :: Identifier -> Semantics Loc
takeLocation id = do
    Just loc <- asks (M.lookup (evalId id))
    return loc

takeValue :: Loc -> Semantics Int
takeValue loc = do
    Just val <- gets (M.lookup loc)
    return val