module Interpreter where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import Types
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

-- EXPRESSIONS

evalE :: Expression -> Semantics Integer
evalE (Exp exp) = do
    eval exp

evalE (ExpTer bexp exp1 exp2) = do
    bvalue <- eval bexp
    if (bvalue == 0)
    then do
        val <- eval exp2
        return val
    else do
        val <- eval exp1
        return val

eval :: Exp -> Semantics Integer
eval (EInt i) = return i

eval (EVar id) = do
    checkIsDeclared(id)
    checkIsVar(id)
    loc <- asks (M.lookup (evalId id))
    case loc of
        Just loc -> do
            Just val <- gets (M.lookup loc)
            case val of
                IVal val -> do
                    return val
                CVal val -> do
                    return val

        Nothing  -> error ("Undeclared variable: " ++ (evalId id))

eval (Eor  exp1 exp2) = do
    val1 <- eval exp1
    if (val1 /= 0)
    then return 1
    else do
        val2 <- eval exp2
        if (or [val1 /= 0, val2 /= 0])
            then return 1
            else return 0

eval (Eand  exp1 exp2) = do
    val1 <- eval exp1
    if (val1 /= 0)
    then do
        val2 <- eval exp2
        if (and [val1 /= 0, val2 /= 0])
            then return 1
            else return 0
    else return 0


eval (Eeq  exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    if (val1 == val2)
        then return 1
        else return 0

eval (Egt  exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    if (val1 > val2)
        then return 1
        else return 0

eval (Elt  exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    if (val1 < val2)
        then return 1
        else return 0

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
    if (val2 == 0)
    then
        error("Próba dzielenia przez 0")
    else
        return (div val1 val2)

--eval (EMinus Etrue)  = return 0
--eval (EMinus Efalse) = return 1
eval (EMinus exp) = do
    val <- eval exp
    return (-val)

eval (Call id vals) = do
    checkIsDeclared(id)
    checkIsFunction(id)
    Just loc <-asks (M.lookup (evalId id))
    Just f <- gets (M.lookup loc)
    case f of
        Func env rtype args rblock -> do
            env' <- createEnv env args vals
            local (const env') (evalRetBlock rblock)
        _ -> error("Identifier does not match a function: " ++ evalId(id))

    where
    createEnv env [] [] = return env
    createEnv env (Args ttype id:args) (Cargs val:vals) = do
        val' <- evalE val
        Just (IVal newLoc) <- gets (M.lookup 0)
        modify (M.insert newLoc (IVal val'))
        modify (M.insert 0 (IVal (newLoc+1)))
        env' <- (return $ M.insert (evalId(id)) newLoc env)
        createEnv env' args vals

    createEnv env (Args ttype id:args) (Ref ref:vals) = do
        Just (IVal newLoc) <- gets (M.lookup 0)
        loc <-asks (M.lookup (evalId(ref)))
        case loc of
            Just loc -> do
                env' <- (return $ M.insert (evalId(id)) loc env)
                createEnv env' args vals
            Nothing ->
                error ("Identyfikator nie jest zadeklarowany: " ++ evalId(id))

eval (Anon ttype rblock) = do
    env <- ask
    local (const env) (evalRetBlock rblock)

eval (Etrue)  = return 1

eval (Efalse) = return 0

evalRetBlock (SRBlock decls fdecls stmts exp) = do
--    interpretB (SBlock decls stmts)
    env' <- evalDecls decls
    env'' <- local (const env') (evalFuncDecls fdecls)
    local (const env'') (mapM_ interpret stmts)
    local (const env'') (evalE exp)

-- *****

-- ASSIGNMENTS

interpretA :: Assignment -> Semantics ()
interpretA (Assign id exp) = do
    checkIsDeclared(id)
    checkIsNotConst(id)
    checkIsVar(id)
    val <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    modify (M.insert loc (IVal val))

interpretA (AArith id AAPlus exp) = do
    checkIsDeclared(id)
    checkIsNotConst(id)
    checkIsVar(id)
    val1 <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    Just (IVal val2) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val1 + val2)))

interpretA (AArith id AAMinus exp) = do
    checkIsDeclared(id)
    checkIsNotConst(id)
    checkIsVar(id)
    val1 <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    Just (IVal val2) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val2 - val1)))

interpretA (AArith id AAMulti exp) = do
    checkIsDeclared(id)
    checkIsNotConst(id)
    checkIsVar(id)
    val1 <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    Just (IVal val2) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val1 * val2)))

interpretA (AArith id AADiv exp) = do
    checkIsDeclared(id)
    checkIsNotConst(id)
    checkIsVar(id)
    val1 <- evalE exp
    Just loc <-asks (M.lookup (evalId id))
    Just (IVal val2) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (div val2  val1)))

interpretA (AIncDec id Increment) = do
    checkIsDeclared(id)
    checkIsNotConst(id)
    checkIsVar(id)
    Just loc <-asks (M.lookup (evalId id))
    Just (IVal val) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val + 1)))

interpretA (AIncDec id Decrement) = do
    checkIsDeclared(id)
    checkIsNotConst(id)
    checkIsVar(id)
    Just loc <-asks (M.lookup (evalId id))
    Just (IVal val) <- gets (M.lookup loc)
    modify (M.insert loc (IVal (val - 1)))

-- *****

-- DECLARATIONS

evalDecl :: Decl -> Semantics Env
evalDecl (DAssign t id expr) = do
    loc <-asks (M.lookup (evalId id))
    case loc of
        Nothing -> do
            Just (IVal newLoc) <- gets (M.lookup 0)
            val <- evalE expr
            modify (M.insert newLoc (IVal val))
            modify (M.insert 0 (IVal (newLoc+1)))
            env <- ask
            return $ M.insert (evalId(id)) newLoc env

        _ -> error("Identyfikator jest już w użyciu: " ++ evalId(id))
evalDecl (Declr t id) = do
    loc <-asks (M.lookup (evalId id))
    case loc of
        Nothing -> do
            Just (IVal newLoc) <- gets (M.lookup 0)
            -- initialize to 0
            modify (M.insert newLoc (IVal 0))
            modify (M.insert 0 (IVal (newLoc+1)))
            env <- ask
            return $ M.insert (evalId(id)) newLoc env
        _ -> error("Identyfikator jest już w użyciu: " ++ evalId(id))
evalDecl (DConstDec t id expr) = do
    loc <-asks (M.lookup (evalId id))
    case loc of
        Nothing -> do
            Just (IVal newLoc) <- gets (M.lookup 0)
            val <- evalE expr
            modify (M.insert newLoc (CVal val))
            modify (M.insert 0 (IVal (newLoc+1)))
            env <- ask
            return $ M.insert (evalId(id)) newLoc env

        _ -> error("Identyfikator jest już w użyciu: " ++ evalId(id))

evalDecls :: [Decl] -> Semantics Env
evalDecls [] = ask
evalDecls (decl:decls) = do
  env' <- evalDecl decl
  local (const env') (evalDecls decls)

redeclareConst :: Identifier -> Semantics ()
redeclareConst id = do
    checkIsVar(id)
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
    checkRedeclared(id)
    mapM_ checkArgs args
    Just (IVal newLoc) <- gets (M.lookup 0)

    modify (M.insert 0 (IVal (newLoc+1)))
    env <- ask
    env' <- return $ M.insert (evalId(id)) newLoc env
    modify (M.insert newLoc (Func env' rtype args rblock))
    return env'
    where
    checkArgs (Args t id) = checkRedeclared(id)

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

interpret (Sprint Etrue) = do
    liftIO $ print "true"
interpret (Sprint Efalse) = do
    liftIO $ print "false"
interpret (Sprint exp) = do
    val <- eval exp
    liftIO $ print val
interpret (SprintS s) = do
    liftIO $ print s

interpret (SGuard ids block) = do
    makeConst ids
    interpretB block
    makeVar ids
    where
    makeConst ids = do
        mapM_ redeclareConst ids
    makeVar ids = do
        mapM_ redeclareVar ids

interpret (SFor exp1 exp2 id block) = do
    from <- eval exp1
    to <- eval exp2

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
interpretB (SBlock decls fdecls stmts) = do
    env' <- evalDecls decls
    env'' <- local (const env') (evalFuncDecls fdecls)
    local (const env'') (mapM_ interpret stmts)

-- *****

-- CHECKS

checkIsNotConst (id) = do
    loc <-asks (M.lookup (evalId id))
    case loc of
        Just loc -> do
            val <- gets (M.lookup loc)
            case val of
                Just (CVal val) -> do
                    error ("Nielegalna próba przypisania do stałej " ++ (evalId id))
                Just (IVal val) ->
                    return ()
                _ -> do
                    error("Nielegalne przypisanie do funkcji " ++ (evalId id))
        Nothing -> return ()

checkIsFunction (id) = do
    loc <-asks (M.lookup (evalId id))
    case loc of
        Just loc -> do
            val <- gets (M.lookup loc)
            case val of
                Just (Func _ _ _ _) -> do
                    return ()
                _ -> do
                    error("Identyfikator wywołania nie jest przypisany do funkcji: " ++ evalId(id))

checkIsVar (id) = do
    loc <-asks (M.lookup (evalId id))
    case loc of
        Just loc -> do
            val <- gets (M.lookup loc)
            case val of
                Just (Func _ _ _ _) -> do
                    error("Identyfikator zmiennej jest przypisany do funkcji: " ++ evalId(id))
                _ -> do
                    return ()

checkRedeclared (id) = do
    loc <-asks (M.lookup (evalId id))
    case loc of
        Just loc -> do
            error("Identyfikator jest już w użyciu: " ++ (evalId(id)))
        Nothing ->
            return ()

checkIsDeclared (id) = do
    loc <-asks (M.lookup (evalId id))
    case loc of
        Just loc ->
            return ()
        Nothing -> do
            error("Identyfikator nie był zadeklarowany: " ++ (evalId(id)))

-- *****
