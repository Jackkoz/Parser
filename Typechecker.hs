module Typechecker where

import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

import AbsGram

interpretP :: Program -> Semantics ()
interpretP (Prog decls funD b) = do
    env' <- evalDecls decls
    env'' <- local (const env') (evalFuncDecls funD)
    local (const env'') (interpretB b)

typeCheck :: Program -> IO ()
typeCheck p = do
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

evalIdent :: Ident -> String
evalIdent (Ident str) = str

takeLocation :: Identifier -> Semantics Loc
takeLocation id = do
    loc <- asks (M.lookup (evalId id))
    case loc of
        Just loc -> return loc
        Nothing  -> error ("Identyfikator nie został zadeklarowany: " ++ (evalId id))

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
    if (not $ isBool bvalue) then
        error("Wyrażenie nie jest boolowskie: " ++ show(bexp))
    else return ()
    val <- eval exp2
    val <- eval exp1
    return val

eval :: Exp -> Semantics Val
eval (EInt i) = return (IVal 1)

eval (EVar id) = do
    checkIsDeclared(id)
    checkIsVar(id)
    val <- getVal id

    return val

eval (Eor  exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    if (not $ (isBool val1)) then
        error("Wyrażenie nie jest wyrażeniem logicznym: " ++ show(exp1))
    else if (not $ (isBool val2)) then
        error("Wyrażenie nie jest wyrażeniem logicznym: " ++ show(exp2))
    else
        return (VBool True)

eval (Eand  exp1 exp2) = do
    eval(Eor exp1 exp2)

eval (Eeq  exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    if (not $ (isInt val1 && isInt val2) || (isBool val1 && isBool val2)) then
        error("Wyrażenia mają niezgodne typy: " ++ show(exp1) ++ " oraz " ++ show(exp2))
    else return (VBool True)

eval (Egt  exp1 exp2) = do
    eval (Eeq exp1 exp2)

eval (Elt  exp1 exp2) = do
    eval (Eeq exp1 exp2)

eval (EAdd exp1 exp2) = do
    val1 <- eval exp1
    val2 <- eval exp2
    if (not $ isInt val1) then
        error("Wyrażenie nie jest wyrażeniem arytmetycznym: " ++ show(exp1))
    else if (not $ isInt val1) then
        error("Wyrażenie nie jest wyrażeniem arytmetycznym: " ++ show(exp1))
    else
        return (IVal 1)

eval (ESub exp1 exp2) = do
    eval (EAdd exp1 exp2)

eval (EMul exp1 exp2) = do
    eval (EAdd exp1 exp2)

eval (EDiv exp1 exp2) = do
    eval (EAdd exp1 exp2)

eval (EMinus exp) = do
    val <- eval exp
    return (val)

eval (Call id vals) = do
    checkIsDeclared(id)
    checkIsFunction(id)
    Just loc <-asks (M.lookup (evalId id))
    Just f <- gets (M.lookup loc)
    case f of
        Func env rtype args rblock -> do
            env' <- createEnv env args vals
            case rtype of
                TInt -> return (IVal 1)
                TBool -> return (VBool True)

    where
    createEnv env [] [] = return env
    createEnv env (Args ttype idd:args) (Cargs val:vals) = do
        val' <- evalE val
        case ttype of
            TInt -> if (not $ isInt val') then error("Błędny typ dla argumentu " ++ evalId(idd) ++ " przy wywołaniu funkcji " ++ evalId(id))
                else return ()
            TBool -> if (not $ isBool val') then error("Błędny typ dla argumentu " ++ evalId(idd) ++ " przy wywołaniu funkcji " ++ evalId(id))
                else return ()
        Just (IVal newLoc) <- gets (M.lookup 0)
        modify (M.insert newLoc val')
        modify (M.insert 0 (IVal (newLoc+1)))
        env' <- (return $ M.insert (evalId(idd)) newLoc env)
        createEnv env' args vals

    createEnv env (Args ttype idd:args) (Ref ref:vals) = do
        val' <- getVal(ref)
        case ttype of
            TInt -> if (not $ isInt val') then error("Błędny typ dla argumentu " ++ show(idd) ++ " przy wywołaniu funkcji " ++ evalId(id))
                else return ()
            TBool -> if (not $ isBool val') then error("Błędny typ dla argumentu " ++ show(idd) ++ " przy wywołaniu funkcji " ++ evalId(id))
                else return ()
        Just (IVal newLoc) <- gets (M.lookup 0)
        loc <-asks (M.lookup (evalId(ref)))
        case loc of
            Just loc -> do
                env' <- (return $ M.insert (evalId(idd)) loc env)
                createEnv env' args vals
            Nothing ->
                error ("Identyfikator nie jest zadeklarowany: " ++ evalId(idd))

eval (Anon ttype rblock) = do
    env <- ask
    local (const env) (evalRetBlock rblock)

eval (Etrue)  = return (VBool True)

eval (Efalse) = return (VBool False)

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
    val2 <- getVal(id)
    if ((isInt val && isInt val2) || (isBool val && isBool val2))
    then
        modify (M.insert loc val)
    else
        error("Niezgodność typów przy przypisaniu " ++ show(exp) ++ " na " ++ evalId(id))

interpretA (AArith id AAPlus exp) = do
    checkIsDeclared(id)
    checkIsNotConst(id)
    checkIsVar(id)
    val1 <- evalE exp
    if (not $ isInt val1) then
        error("Wyrażenie nie jest wyrażeniem arytmetycznym: " ++ show exp)
    else return ()
    Just loc <-asks (M.lookup (evalId id))
    Just val2 <- gets (M.lookup loc)
    if (not $ isInt val2) then
        error("Zły typ zmiennej dla przypisania arytmetycznego: " ++ evalId id)
    else return ()
    modify (M.insert loc val1)

interpretA (AArith id AAMinus exp) = do
    interpretA (AArith id AAPlus exp)

interpretA (AArith id AAMulti exp) = do
    interpretA (AArith id AAPlus exp)

interpretA (AArith id AADiv exp) = do
    interpretA (AArith id AAPlus exp)

interpretA (AIncDec id Increment) = do
    checkIsDeclared(id)
    checkIsNotConst(id)
    checkIsVar(id)
    Just loc <-asks (M.lookup (evalId id))
    Just val <- gets (M.lookup loc)
    if (not $ isInt val) then
        error("Zły typ zmiennej dla przypisania arytmetycznego: " ++ evalId id)
    else return ()
    modify (M.insert loc val)

interpretA (AIncDec id Decrement) = do
    interpretA(AIncDec id Increment)

-- *****

-- DECLARATIONS

evalDecl :: Decl -> Semantics Env
evalDecl (DAssign t id expr) = do
    checkRedeclared id
    val <- evalE expr
    case t of
        TInt  -> if (not $ isInt val)  then do error("Błędny typ dla deklaracji " ++ evalId(id) ++ " przy przypisaniu " ++ show(expr))
            else return ()
        TBool -> if (not $ isBool val) then do error("Błędny typ dla deklaracji " ++ evalId(id) ++ " przy przypisaniu " ++ show(expr))
            else return ()
    Just (IVal newLoc) <- gets (M.lookup 0)
    modify (M.insert newLoc val)
    modify (M.insert 0 (IVal (newLoc+1)))
    env <- ask
    return $ M.insert (evalId(id)) newLoc env

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
            case t of
                TInt -> do
                    if (not (isInt val)) then
                        error("Zły typ przypisania wyrażenia " ++ show(expr) ++ " na zmienną " ++ evalId(id))
                    else return ()
                TBool ->
                    if (not (isBool val)) then
                        error("Zły typ przypisania wyrażenia " ++ show(expr) ++ " na zmienną " ++ evalId(id))
                    else return ()
            modify (M.insert newLoc val)
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
            error ("Niepoprawny parametr dla guard, identyfikator jest stałą: " ++ evalId(id))

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
    if (not $ isBool bval) then
        error("Wyrażenie nie jest boolowskie: " ++ show(exp))
    else return ()
    interpretEIf eifs
    interpretB b

interpret (SIfE (If exp b eifs) belse) = do
    bval <- eval exp
    if (not $ isBool bval) then
        error("Wyrażenie nie jest boolowskie: " ++ show(exp))
    else return ()
    interpretEIfE eifs belse
    interpretB b

interpret this@(SWhile exp block) = do
    bval <- eval exp
    if (not $ isBool bval) then
        error("Wyrażenie nie jest boolowskie: " ++ show(exp))
    else return ()
    interpretB block


interpret (Sprint Etrue) = do
    return ()
interpret (Sprint Efalse) = do
    return ()
interpret (Sprint exp) = do
    val <- eval exp
    return ()
interpret (SprintS s) = do
    return ()

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
    checkRedeclared id
    from <- eval exp1
    to <- eval exp2
    if (not $ isInt from) then
        error("Wyrażenie nie jest arytmetyczne: " ++ show(exp1))
    else return ()
    if (not $ isInt to) then
        error("Wyrażenie nie jest arytmetyczne: " ++ show(exp2))
    else return ()
    IVal from <- eval exp1

    Just (IVal newLoc) <- gets (M.lookup 0)
    modify (M.insert newLoc (CVal from))
    modify (M.insert 0 (IVal (newLoc+1)))
    env <- ask
    env' <- (return $ M.insert (evalId(id)) newLoc env)

    local (const env') (interpretB block)

interpretEIfE :: [EIf] -> Block -> Semantics ()
interpretEIfE [] belse = interpretB belse

interpretEIfE ((SEIf exp b):eifs) belse = do
    bval <- eval exp
    if (not $ isBool bval) then
        error("Wyrażenie nie jest boolowskie: " ++ show(exp))
    else return ()
    interpretEIfE eifs belse
    interpretB b

interpretEIf :: [EIf] -> Semantics ()
interpretEIf [] = return ()

interpretEIf ((SEIf exp b):eifs) = do
    bval <- eval exp
    if (not $ isBool bval) then
        error("Wyrażenie nie jest boolowskie: " ++ show(exp))
    else return ()
    interpretEIf eifs
    interpretB b

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
                Just (CBool val) -> do
                    error ("Nielegalna próba przypisania do stałej " ++ (evalId id))
                Just (IVal val) ->
                    return ()
                Just (VBool val) ->
                    return ()
                _ -> do
                    error("Nielegalna próba przypisania do funkcji " ++ (evalId id))
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

isInt :: Val -> Bool
isInt (CVal _) = True
isInt (IVal _) = True
isInt _ = False

isBool :: Val -> Bool
isBool (VBool _) = True
isBool (CBool _) = True
isBool _ = False

-- *****
