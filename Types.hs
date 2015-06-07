module Types where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import AbsGram

data Val = IVal Integer | CVal Integer
    | VBool Bool | CBool Bool
    | Func Env Type [Arguments] RBlock
    deriving (Eq, Ord, Show)

type Loc = Integer
type Env = M.Map String Loc
type St  = M.Map Loc Val

emptyEnv :: Env
emptyEnv = M.empty

initialSt :: St
initialSt = M.singleton 0 (IVal 1)

type Semantics a = ReaderT Env (StateT St IO) a

evalId :: Identifier -> String
evalId (Id id) = evalIdent id
evalId (Arr id size) = evalIdent id

evalIdent :: Ident -> String
evalIdent (Ident str) = str

takeLocation :: Identifier -> Semantics Loc
takeLocation (Id id) = do
    loc <- asks (M.lookup (evalIdent id))
    case loc of
        Just loc -> return loc
        Nothing  -> error ("Niezadeklarowana zmienna: " ++ (evalIdent id))

takeLocation (Arr id s) = do
    if (index < 1) then
        error ("Indeks tablicy musi być liczbą naturalną: " ++ show index ++ " ; " ++ evalIdent id)
    else do
        arrLoc <- asks (M.lookup (evalIdent id))
        case arrLoc of
            Nothing ->
                error ("Niezadeklarowana zmienna tablicowa: " ++ (evalIdent id))
            Just arrLoc -> do
                (IVal size) <- takeValue arrLoc
                if (index > size) then
                    error ("Indeks " ++ show index ++ " jest poza tablicą " ++ evalIdent id)
                else
                    return (arrLoc + index)

takeValue :: Loc -> Semantics Val
takeValue loc = do
    Just val <- gets (M.lookup loc)
    return val

getVal :: Identifier -> Semantics Val
getVal id = do
    loc <- takeLocation id
    takeValue loc