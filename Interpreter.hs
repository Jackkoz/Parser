module Interpreter where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import AbsGram

interpretP :: Program -> Semantics ()
interpretP (Prog decls funD b) = do
    env' <- evalDecls decls
    env'' <- local (const env') (evalFuncDecls funD)
    local (const env'') (interpretB b)

execProgram :: Program -> IO ()
execProgram p = do
    finalState <- execStateT (runReaderT (interpretP p) emptyEnv) initialSt
    return ()

-- TYPES

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

takeLocation (Arr id s) = do
    s <- eval s
    index <- getInt s
    if (index < 1) then
        error ("Indeks tablicy musi być liczbą naturalną: " ++ show index ++ " ; " ++ evalIdent id)
    else do
        arrLoc <- asks (M.lookup (evalIdent id))
        case arrLoc of
            Just arrLoc -> do
                (CVal size) <- takeValue arrLoc
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

-- *****

-- EXPRESSIONS

evalE :: Expression -> Semantics Val
evalE (Exp exp) = do
    eval exp

evalE (ExpTer bexp exp1 exp2) = do
    bvalue <- eval bexp
    bvalue <- getBool bvalue
    if (not bvalue)
    then do
        val <- eval exp2
        return val
    else do
        val <- eval exp1
        return val

eval :: Exp -> Semantics Val
eval (EInt i) = return (IVal i)

eval (EVar id) = do
    loc <- takeLocation id
    Just val <- gets (M.lookup loc)
    return val

eval (Eor exp1 exp2) = do
    val1 <- eval exp1
    val1 <- getBool val1
    if (val1)
    then return (VBool True)
    else do
        val2 <- eval exp2
        val2 <- getBool val2
        if (val2)
            then return (VBool True)
            else return (VBool False)

eval (Eand  exp1 exp2) = do
    val1 <- eval exp1
    val1 <- getBool val1
    if (val1)
    then do
        val2 <- eval exp2
        val2 <- getBool val2
        if (val2)
            then return (VBool True)
            else return (VBool False)
    else return (VBool False)


eval (Eeq  exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    if (val1 == val2)
        then return (VBool True)
        else return (VBool False)

eval (Egt  exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    if (val1 > val2)
        then return (VBool True)
        else return (VBool False)

eval (Elt  exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    if (val1 < val2)
        then return (VBool True)
        else return (VBool False)

eval (EAdd exp1 exp2) = do
    val1 <- eval exp1
    val1 <- getInt val1
    val2 <- eval exp2
    val2 <- getInt val2
    return (IVal (val1 + val2))

eval (ESub exp1 exp2) = do
    val1 <- eval exp1
    val1 <- getInt val1
    val2 <- eval exp2
    val2 <- getInt val2
    return (IVal (val1 - val2))

eval (EMul exp1 exp2) = do
    val1 <- eval exp1
    val1 <- getInt val1
    val2 <- eval exp2
    val2 <- getInt val2
    return (IVal (val1 * val2))

eval (EDiv exp1 exp2) = do
    val1 <- eval exp1
    val1 <- getInt val1
    val2 <- eval exp2
    val2 <- getInt val2
    if (val2 == 0)
    then
        error("Próba dzielenia przez 0")
    else
        return (IVal (div val1 val2))

eval (ECast exp TInt) = do
    val <- eval exp
    case val of
        VBool val -> return (IVal (if (val) then 1 else 0))
        CBool val -> return (IVal (if (val) then 1 else 0))
        IVal val -> return (IVal val)
        CVal val -> return (IVal val)
eval (ECast exp TBool) = do
    val <- eval exp
    case val of
        VBool val -> return (VBool val)
        CBool val -> return (VBool val)
        IVal val -> return (VBool (val /= 0))
        CVal val -> return (VBool (val /= 0))

eval (EMinus exp) = do
    val <- eval exp
    case val of
        IVal val -> return (IVal (-val))
        CVal val -> return (IVal (-val))
        VBool val -> return (VBool (not val))
        CBool val -> return (VBool (not val))

eval (Call id vals) = do
    Just loc <-asks (M.lookup (evalId id))
    Just f <- gets (M.lookup loc)
    case f of
        Func env rtype args rblock -> do
            env' <- createEnv env args vals
            local (const env') (evalRetBlock rblock)

    where
    createEnv env [] [] = return env
    createEnv env (Args ttype id:args) (Cargs val:vals) = do
        val' <- evalE val
        Just (IVal newLoc) <- gets (M.lookup 0)
        modify (M.insert newLoc val')
        modify (M.insert 0 (IVal (newLoc+1)))
        env' <- (return $ M.insert (evalId(id)) newLoc env)
        createEnv env' args vals

    createEnv env (Args ttype id:args) (Ref ref:vals) = do
        Just (IVal newLoc) <- gets (M.lookup 0)
        loc <- takeLocation ref
        env' <- (return $ M.insert (evalId(id)) loc env)
        createEnv env' args vals

eval (Anon ttype rblock) = do
    env <- ask
    local (const env) (evalRetBlock rblock)

eval (Etrue)  = return (VBool True)

eval (Efalse) = return (VBool False)

evalRetBlock (SRBlock decls fdecls stmts exp) = do
    env' <- evalDecls decls
    env'' <- local (const env') (evalFuncDecls fdecls)
    local (const env'') (mapM_ interpret stmts)
    local (const env'') (evalE exp)

-- *****

-- ASSIGNMENTS

interpretA :: Assignment -> Semantics ()
interpretA (Assign id exp) = do
    checkIsNotConst(id)
    val <- evalE exp
    loc <- takeLocation id
    case val of
        IVal val ->
            modify (M.insert loc (IVal val))
        CVal val ->
            modify (M.insert loc (IVal val))
        VBool val ->
            modify (M.insert loc (VBool val))
        CBool val ->
            modify (M.insert loc (VBool val))


interpretA (AArith id AAPlus exp) = do
    checkIsNotConst(id)
    val1 <- evalE exp
    val1 <- getInt val1
    loc <- takeLocation id
    Just (IVal val2) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val1 + val2)))

interpretA (AArith id AAMinus exp) = do
    checkIsNotConst(id)
    val1 <- evalE exp
    val1 <- getInt val1
    loc <- takeLocation id
    Just (IVal val2) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val2 - val1)))

interpretA (AArith id AAMulti exp) = do
    checkIsNotConst(id)
    val1 <- evalE exp
    val1 <- getInt val1
    loc <- takeLocation id
    Just (IVal val2) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val1 * val2)))

interpretA (AArith id AADiv exp) = do
    checkIsNotConst(id)
    val1 <- evalE exp
    val1 <- getInt val1
    loc <- takeLocation id
    Just (IVal val2) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (div val2  val1)))

interpretA (AIncDec id Increment) = do
    checkIsNotConst(id)
    loc <- takeLocation id
    Just (IVal val) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val + 1)))

interpretA (AIncDec id Decrement) = do
    checkIsNotConst(id)
    loc <- takeLocation id
    Just (IVal val) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val - 1)))

-- *****

-- DECLARATIONS

evalDecl :: Decl -> Semantics Env
evalDecl (DAssign TInt id expr) = do
    Just (IVal newLoc) <- gets (M.lookup 0)
    val <- evalE expr
    val <- getInt val
    modify (M.insert newLoc (IVal val))
    modify (M.insert 0 (IVal (newLoc+1)))
    env <- ask
    return $ M.insert (evalId(id)) newLoc env
evalDecl (DAssign TBool id expr) = do
    Just (IVal newLoc) <- gets (M.lookup 0)
    val <- evalE expr
    val <- getBool val
    modify (M.insert newLoc (VBool val))
    modify (M.insert 0 (IVal (newLoc+1)))
    env <- ask
    return $ M.insert (evalId(id)) newLoc env

evalDecl (Declr t (Id id)) = do
    Just (IVal newLoc) <- gets (M.lookup 0)
    -- initialize to 0
    case t of
        TInt ->
            modify (M.insert newLoc (IVal 0))
        TBool ->
            modify (M.insert newLoc (VBool False))
    modify (M.insert 0 (IVal (newLoc+1)))
    env <- ask
    return $ M.insert (evalIdent(id)) newLoc env
evalDecl (Declr t (Arr id s)) = do
    s <- eval s
    size <- getInt s
    if (size < 1) then
        error ("Rozmiar deklarowanej tablicy musi być liczbą naturalną: " ++ evalIdent(id))
    else return ()
    Just (IVal newLoc) <- gets (M.lookup 0)
    modify (M.insert newLoc (CVal size))
    modify (M.insert 0 (IVal (newLoc+1)))
    createVars t size
    env <- ask
    return $ M.insert (evalIdent(id)) newLoc env
    where
    createVars _ 0 = return ()
    createVars ttype number = do
        Just (IVal newLoc) <- gets (M.lookup 0)
        case ttype of
            TInt ->
                modify (M.insert newLoc (IVal 0))
            TBool ->
                modify (M.insert newLoc (VBool False))
        modify (M.insert 0 (IVal (newLoc+1)))
        env <- ask
        createVars ttype (number - 1)

evalDecl (DConstDec TInt id expr) = do
    Just (IVal newLoc) <- gets (M.lookup 0)
    val <- evalE expr
    val <- getInt val
    modify (M.insert newLoc (CVal val))
    modify (M.insert 0 (IVal (newLoc+1)))
    env <- ask
    return $ M.insert (evalId(id)) newLoc env
evalDecl (DConstDec TBool id expr) = do
    Just (IVal newLoc) <- gets (M.lookup 0)
    val <- evalE expr
    val <- getBool val
    modify (M.insert newLoc (CBool val))
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
    checkIsVar(id)
    loc <- takeLocation id
    val <- getVal id
    case val of
        IVal val -> do
            modify (M.insert loc (CVal val))
        CVal val -> do
            error ("Niepoprawny parametr dla guard, identyfikator jest stałą: " ++ evalId(id))
        VBool val -> do
            modify (M.insert loc (CBool val))
        CBool val -> do
            error ("Niepoprawny parametr dla guard, identyfikator jest stałą: " ++ evalId(id))

redeclareVar :: Loc -> Semantics ()
redeclareVar loc = do
--    loc <- takeLocation id
--    val <- getVal id
    Just val <- gets (M.lookup loc)
    case val of
        CVal val ->
            modify (M.insert loc (IVal val))
        CBool val ->
            modify (M.insert loc (VBool val))

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

-- *****

-- STATEMENTS

interpret :: Stmt -> Semantics ()

interpret (SAssign a) = do
    interpretA a

interpret (SExp exp) = do
    evalE exp
    return ()

interpret (SIf (If exp b eifs)) = do
    bval <- eval exp
    bval <- getBool bval
    if (not bval)
        then interpretEIf eifs
        else interpretB b

interpret (SIfE (If exp b eifs) belse) = do
    bval <- eval exp
    bval <- getBool bval
    if (not bval)
        then interpretEIfE eifs belse
        else interpretB b

interpret this@(SWhile exp block) = do
    bval <- eval exp
    bval <- getBool bval
    if (not bval)
        then return ()
        else do
            interpretB block
            interpret this

interpret (Sprint exp) = do
    val <- eval exp
    case val of
        IVal  v -> liftIO $ print v
        CVal  v -> liftIO $ print v
        VBool v -> liftIO $ print v
        CBool v -> liftIO $ print v
interpret (SprintS s) = do
    liftIO $ print s

interpret (SGuard ids block) = do
    locs <- Prelude.mapM takeLocation ids
    env <- makeConst ids
    interpretB block
    env <- makeVar locs
    return ()
    where
    makeConst ids = do
        mapM_ redeclareConst ids
    makeVar locs = do
        mapM_ redeclareVar locs

interpret (SFor exp1 exp2 id block) = do
    from <- eval exp1
    from <- getInt from
    to <- eval exp2
    to <- getInt to

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
    bval <- getBool bval
    if (not bval)
        then interpretEIfE eifs belse
        else interpretB b

interpretEIf :: [EIf] -> Semantics ()
interpretEIf [] = return ()

interpretEIf ((SEIf exp b):eifs) = do
    bval <- eval exp
    bval <- getBool bval
    if (not bval)
        then interpretEIf eifs
        else interpretB b

interpretB :: Block -> Semantics ()
interpretB (SBlock decls fdecls stmts) = do
    env' <- evalDecls decls
    env'' <- local (const env') (evalFuncDecls fdecls)
    local (const env'') (mapM_ interpret stmts)

-- *****

-- CHECKS

checkIsNotConst (id) = do
    loc <- takeLocation id
    val <- getVal id
    case val of
        (CVal val) -> do
            error ("Nielegalna próba przypisania do stałej " ++ (evalId id))
        (CBool val) ->
            error ("Nielegalna próba przypisania do stałej " ++ (evalId id))
        _ -> do
            return ()

checkIsVar (id) = do
    loc <- takeLocation id
    val <- getVal id
    case val of
        (Func _ _ _ _) -> do
            error("Identyfikator zmiennej jest przypisany do funkcji: " ++ evalId(id))
        _ -> do
            return ()
-- *****

getInt v = do
    case v of
        IVal v -> return v
        CVal v -> return v

getBool v = do
    case v of
        VBool v -> return v
        CBool v -> return v
