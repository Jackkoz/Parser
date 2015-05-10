module Types where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import AbsGram

--data Block =
--    SBlock [Decl] [Stmt]
--    deriving (Eq,Ord,Show)
--
--data RBlock =
--    SRBlock [Decl] [Stmt] Expression
--    deriving (Eq,Ord,Show)
--
--data Stmt = SSkip
--    | SAssign Assignment
--    | SIf If
--    | SIfE If Block
--    | SWhile Exp Block
----    | SExp Exp
----    | SBlock [Decl] [Stmt]
--    deriving (Eq,Ord,Show)
--
--data If =
--   If Exp Block [EIf]
--  deriving (Eq,Ord,Show)
--
--data EIf =
--   SEIf Exp Block
--  deriving (Eq,Ord,Show)
--
--data Expression =
--    Exp Exp
--    deriving (Eq,Ord,Show)
--
--data Exp =
--      EInt Int
--    | Eor  Exp Exp
--    | Eand Exp Exp
--    | Eeq  Exp Exp
--    | Elt  Exp Exp
--    | Egt  Exp Exp
--    | EAdd Exp Exp
--    | ESub Exp Exp
--    | EMul Exp Exp
--    | EDiv Exp Exp
--    | EMinus Exp
--    | EVar Identifier
--    | Etrue
--    | Efalse
--    deriving (Eq,Ord,Show)
--
--data TypeDeclaration =
--    TDef Identifier Type
--    deriving (Eq,Ord,Show)
--
--data FunctionDeclaration =
--      FDec Identifier [Arguments] Type RBlock
--    | PDec Identifier [Arguments] Block
--    deriving (Eq,Ord,Show)
--
--data CallArgs =
--    Cargs Expression
--    deriving (Eq,Ord,Show)
--
--data Arguments =
--    Args Type Identifier
--    deriving (Eq,Ord,Show)
--
--data Decl =
--      Declr   Type Identifier
--    | DAssign    Type Identifier Expression
--    -- | DConstDec Type Identifier Exp
--    deriving (Eq,Ord,Show)
--
--data Assignment =
--      Assign Identifier Expression
--    | AArith Identifier ArAssign Expression
--    | AIncDec Identifier IncDec
--    deriving (Eq,Ord,Show)
--
--data ArAssign =
--      AAPlus
--    | AAMinus
--    | AAMulti
--    | AADiv
--    deriving (Eq,Ord,Show)
--
--data IncDec =
--      Increment
--    | Decrement
--    deriving (Eq,Ord,Show)
--
--data Type =
--      TInt
--    | TBool
--    deriving (Eq,Ord,Show)
--
--newtype Ident = Ident String
--    deriving (Eq,Ord,Show)
--
--data Identifier = Id Ident
--    deriving (Eq,Ord,Show)

type Loc = Integer
type Env = M.Map String Loc
type St  = M.Map Loc Integer

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

takeValue :: Loc -> Semantics Integer
takeValue loc = do
    Just val <- gets (M.lookup loc)
    return val