import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

data Program =
   Prog [TypeDeclaration] [Decl] [FunctionDeclaration] Block
  deriving (Eq,Ord,Show)

data TypeDeclaration =
   TDef Identifier Type
  deriving (Eq,Ord,Show)

data FunctionDeclaration =
   FDec Identifier [Arguments] Type RBlock
 | PDec Identifier [Arguments] Block
  deriving (Eq,Ord,Show)

data CallArgs =
   Cargs Expression
  deriving (Eq,Ord,Show)

data Arguments =
   Args Type Identifier
  deriving (Eq,Ord,Show)

data Block =
    SBlock [Decl] [Stmt]
    deriving (Eq,Ord,Show)

data RBlock =
    SRBlock [Decl] [Stmt] Expression
    deriving (Eq,Ord,Show)

data Expression =
    Exp Exp
    deriving (Eq,Ord,Show)

data Exp =
      EInt Int
    | EAdd Exp Exp
    | ESub Exp Exp
    | EMul Exp Exp
    | EDiv Exp Exp
    | EMinus Exp
    | EVar Identifier
    | Etrue
    | Efalse
    deriving (Eq,Ord,Show)

data Stmt = SSkip
    | SAssign Assignment
    | SIf Expression Block Block
    | SWhile Expression Block
--    | SExp Exp
--    | SBlock [Decl] [Stmt]
    deriving (Eq,Ord,Show)
     
data Decl =
      Declr   Type Identifier
    | DAssign    Type Identifier Expression
--    | SDec
    -- | DConstDec Type Identifier Exp
    deriving (Eq,Ord,Show)

data Assignment =
      Assign Identifier Expression
--    | AArith Identifier ArAssign Expression
--    | AIncDec Identifier IncDec
    deriving (Eq,Ord,Show)

data Type =
      TInt
    | TBool
    deriving (Eq,Ord,Show)

newtype Ident = Ident String
    deriving (Eq,Ord,Show)

data Identifier = Id Ident
    deriving (Eq,Ord,Show)

type Loc = Int -- lokacja
type Env = M.Map String Loc -- środowisko
type St  = M.Map Loc Int  -- stan

emptyEnv :: Env
emptyEnv = M.empty

-- na pozycji 0 zapisany jest numer następnej wolnej lokacji
initialSt :: St
initialSt = M.singleton 0 1

type Semantics a = ReaderT Env (State St) a
-- albo StateT St (Reader Env) a
-- albo Monada = ReaderT Env (StateT St Identity)

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

evalE :: Expression -> Semantics Int
evalE (Exp exp) = do
    eval exp

eval :: Exp -> Semantics Int
eval (EInt i) = return i
eval (EVar id) = do
    Just loc <- asks (M.lookup (evalId id))
    Just val <- gets (M.lookup loc)
    return val
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
eval (EMinus exp) = do
    val <- eval exp
    return (-val)
eval (Etrue)  = return 1
eval (Efalse) = return 0

evalExp :: Exp -> Int
evalExp expr =
    let readerStuff = eval expr in
    let stateStuff = runReaderT readerStuff emptyEnv in
    evalState stateStuff initialSt

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

-- można też asks M.insert var newLoc

-- Dodatkowa zabawa, aby druga deklaracja z listy mogla juz uzywac pierwszej zmiennej
evalDecls :: [Decl] -> Semantics Env
evalDecls [] = ask
evalDecls (decl:decls) = do
  env' <- evalDecl decl
  local (const env') (evalDecls decls)

interpretP :: Program -> Semantics ()
interpretP (Prog typeD decls funD b) = do
    env' <- evalDecls decls
    interpretB b

interpretB :: Block -> Semantics ()
interpretB (SBlock decls stmts) = do
    env' <- evalDecls decls
    local (const env') (mapM_ interpret stmts)

interpretA :: Assignment -> Semantics ()
interpretA (Assign id exp) = do
    val <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    modify (M.insert loc val)

interpret :: Stmt -> Semantics ()
interpret SSkip = return ()

interpret (SAssign a) = do
    interpretA a

interpret (SIf exp block1 block2) = do
  bval <- evalE exp
  if bval == 0
     then interpretB block2
     else interpretB block1

interpret this@(SWhile exp block) = do
    bval <- evalE exp
    if bval == 0
        then return ()
        else do
            interpretB block
            interpret this

execStmt :: Stmt -> IO ()
execStmt stmt = do
  let ((), finalState) =  runState (runReaderT (interpret stmt) emptyEnv) initialSt

  print finalState

execBlock :: Block -> IO ()
execBlock b = do
    let ((), finalState) =  runState (runReaderT (interpretB b) emptyEnv) initialSt

    print finalState

execProgram :: Program -> IO ()
execProgram p = do
    let ((), finalState) =  runState (runReaderT (interpretP p) emptyEnv) initialSt

    print finalState

-- Przykładowe programy
--exp1 = EAdd (EInt 2) (EInt 3)
--
--xplus1 = (EAdd (EVar (Id (Ident "x"))) (EInt 1))
--
--prog1 = SBlock [DVar (TInt) (Id (Ident "x")) (EInt 3)] []
--
--prog2 = SBlock [DVar (TInt) (Id (Ident "x")) (EInt 3)] [SAssign (Id (Ident "x")) xplus1]
--
--prog4 = SBlock [DVar (TInt) (Id (Ident "x")) (EInt 3)]
--    [SIf (EVar (Id (Ident "x")))
--      (SBlock [DVar (TInt) (Id (Ident "y")) (EVar (Id (Ident "x")))] [])
--      (SBlock [] [SSkip])]
--
--prog4a = SBlock [DVar (TInt) (Id (Ident "x")) (EInt 0)]
--    [SIf (EVar (Id (Ident "x")))
--      (SBlock [DVar (TInt) (Id (Ident "y")) (EVar (Id (Ident "x")))] [])
--      (SBlock [] [SSkip])]
--
---- powinno wyjść x=3
--prog5 = SBlock [DVar (TInt) (Id (Ident "x")) (EInt 3)]
--    [SIf (EVar (Id (Ident "x")))
--      (SBlock [DVar (TInt) (Id (Ident "x")) xplus1] [SAssign (Id (Ident "x")) xplus1])
--      (SBlock [] [SAssign (Id (Ident "x")) xplus1])]
--
---- powinno wyjść x=1
--prog5a = SBlock [DVar (TInt) (Id (Ident "x")) (EInt 0)]
--    [SIf (EVar (Id (Ident "x")))
--      (SBlock [DVar (TInt) (Id (Ident "x")) xplus1] [SAssign (Id (Ident "x")) xplus1])
--      (SBlock [] [SAssign (Id (Ident "x")) xplus1])]
--
--
--progW =
--  (SBlock
--    [DVar (TInt) (Id (Ident "x")) (EInt 3), DVar (TInt) (Id (Ident "y")) (EInt 0)]
--    [SWhile (EVar (Id (Ident "x")))
--        (SBlock []
--          [SAssign (Id (Ident "y")) (EAdd (EVar (Id (Ident "y"))) (EVar (Id (Ident "x")))),
--           SAssign (Id (Ident "x")) (ESub (EVar (Id (Ident "x"))) (EInt 1))])]
--  )
--
--loop = SWhile (EInt 1) (SBlock [] [SSkip])
--
--test = SBlock [DVar (TInt) (Id (Ident "x")) (EInt 3)] [SAssign (Id (Ident "x")) (EAdd (EVar (Id (Ident "x"))) (EInt 1))]
--
--testP = Prog [] [] [] (SBlock [DVar (TInt) (Id (Ident "x")) (EInt 3)] [SAssign (Id (Ident "x")) (EAdd (EVar (Id (Ident "x"))) (EInt 1))])

test1 = Prog [] [DAssign TInt (Id (Ident "x")) (Exp (EInt 5)),DAssign TBool (Id (Ident "y")) (Exp Etrue)] [] (SBlock [] [SAssign (Assign (Id (Ident "x")) (Exp (EAdd (EVar (Id (Ident "x"))) (EInt 5)))),SAssign (Assign (Id (Ident "y")) (Exp Efalse))])

test2 = Prog [] [DAssign TInt (Id (Ident "x")) (Exp (EInt 5)),DAssign TBool (Id (Ident "y")) (Exp Etrue)] [] (SBlock [DAssign TInt (Id (Ident "x")) (Exp (EInt 5))] [SAssign (Assign (Id (Ident "x")) (Exp (EInt 5)))])

