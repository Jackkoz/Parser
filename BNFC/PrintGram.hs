{-# OPTIONS -fno-warn-incomplete-patterns #-}
module PrintGram where

-- pretty-printer generated by the BNF converter

import AbsGram
import Data.Char


-- the top-level printing method
printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : "," :ts -> showString t . space "," . rend i ts
    t  : ")" :ts -> showString t . showChar ')' . rend i ts
    t  : "]" :ts -> showString t . showChar ']' . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i   = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t = showString t . (\s -> if null s then "" else (' ':s))

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- the printer class does the job
class Print a where
  prt :: Int -> a -> Doc
  prtList :: [a] -> Doc
  prtList = concatD . map (prt 0)

instance Print a => Print [a] where
  prt _ = prtList

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j<i then parenth else id


instance Print Integer where
  prt _ x = doc (shows x)


instance Print Double where
  prt _ x = doc (shows x)


instance Print Ident where
  prt _ (Ident i) = doc (showString ( i))



instance Print Program where
  prt i e = case e of
   Prog decls functiondeclarations block -> prPrec i 0 (concatD [prt 0 decls , prt 0 functiondeclarations , doc (showString "main") , prt 0 block])


instance Print Block where
  prt i e = case e of
   SBlock decls stmts -> prPrec i 0 (concatD [doc (showString "{") , prt 0 decls , prt 0 stmts , doc (showString "}")])


instance Print RBlock where
  prt i e = case e of
   SRBlock decls stmts expression -> prPrec i 0 (concatD [doc (showString "{") , prt 0 decls , prt 0 stmts , doc (showString "return") , prt 0 expression , doc (showString ";") , doc (showString "}")])


instance Print Decl where
  prt i e = case e of
   Declr type' identifier -> prPrec i 0 (concatD [prt 0 type' , prt 0 identifier])
   DAssign type' identifier expression -> prPrec i 0 (concatD [prt 0 type' , prt 0 identifier , doc (showString "=") , prt 0 expression])
   DConstDec type' identifier expression -> prPrec i 0 (concatD [doc (showString "const") , prt 0 type' , prt 0 identifier , doc (showString "=") , prt 0 expression])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print FunctionDeclaration where
  prt i e = case e of
   FDec identifier argumentss type' rblock -> prPrec i 0 (concatD [doc (showString "function") , prt 0 identifier , doc (showString "(") , prt 0 argumentss , doc (showString ")") , doc (showString ":") , prt 0 type' , prt 0 rblock])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , prt 0 xs])

instance Print CallArgs where
  prt i e = case e of
   Cargs expression -> prPrec i 0 (concatD [prt 0 expression])
   Ref identifier -> prPrec i 0 (concatD [doc (showString "&") , prt 0 identifier])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])

instance Print Arguments where
  prt i e = case e of
   Args type' identifier -> prPrec i 0 (concatD [prt 0 type' , prt 0 identifier])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])

instance Print Stmt where
  prt i e = case e of
   SAssign assignment -> prPrec i 0 (concatD [prt 0 assignment , doc (showString ";")])
   SExp expression -> prPrec i 0 (concatD [prt 0 expression , doc (showString ";")])
   SWhile exp block -> prPrec i 0 (concatD [doc (showString "while") , doc (showString "(") , prt 0 exp , doc (showString ")") , prt 0 block])
   SFor exp0 exp identifier block -> prPrec i 0 (concatD [doc (showString "from") , prt 0 exp0 , doc (showString "to") , prt 0 exp , doc (showString "as") , prt 0 identifier , doc (showString "do") , prt 0 block])
   SGuard identifiers block -> prPrec i 0 (concatD [doc (showString "guard") , doc (showString "(") , prt 0 identifiers , doc (showString ")") , doc (showString "in") , prt 0 block])
   Sprint exp -> prPrec i 0 (concatD [doc (showString "print") , doc (showString "(") , prt 0 exp , doc (showString ")") , doc (showString ";")])
   SprintS str -> prPrec i 0 (concatD [doc (showString "print") , doc (showString "(") , prt 0 str , doc (showString ")") , doc (showString ";")])
   SIf if' -> prPrec i 0 (concatD [prt 0 if'])
   SIfE if' block -> prPrec i 0 (concatD [prt 0 if' , doc (showString "else") , prt 0 block])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , prt 0 xs])

instance Print If where
  prt i e = case e of
   If exp block eifs -> prPrec i 0 (concatD [doc (showString "if (") , prt 0 exp , doc (showString ")") , prt 0 block , prt 0 eifs])


instance Print EIf where
  prt i e = case e of
   SEIf exp block -> prPrec i 0 (concatD [doc (showString "else if (") , prt 0 exp , doc (showString ")") , prt 0 block])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , prt 0 xs])

instance Print Expression where
  prt i e = case e of
   Exp exp -> prPrec i 0 (concatD [prt 0 exp])
   ExpTer exp0 exp1 exp -> prPrec i 0 (concatD [prt 0 exp0 , doc (showString "?") , prt 0 exp1 , doc (showString ":") , prt 0 exp])


instance Print Exp where
  prt i e = case e of
   Eor exp0 exp -> prPrec i 0 (concatD [prt 0 exp0 , doc (showString "||") , prt 1 exp])
   Eand exp0 exp -> prPrec i 0 (concatD [prt 0 exp0 , doc (showString "&&") , prt 1 exp])
   Eeq exp0 exp -> prPrec i 1 (concatD [prt 1 exp0 , doc (showString "==") , prt 2 exp])
   Elt exp0 exp -> prPrec i 2 (concatD [prt 2 exp0 , doc (showString "<") , prt 3 exp])
   Egt exp0 exp -> prPrec i 2 (concatD [prt 2 exp0 , doc (showString ">") , prt 3 exp])
   EAdd exp0 exp -> prPrec i 3 (concatD [prt 3 exp0 , doc (showString "+") , prt 4 exp])
   ESub exp0 exp -> prPrec i 3 (concatD [prt 3 exp0 , doc (showString "-") , prt 4 exp])
   EMul exp0 exp -> prPrec i 4 (concatD [prt 4 exp0 , doc (showString "*") , prt 5 exp])
   EDiv exp0 exp -> prPrec i 4 (concatD [prt 4 exp0 , doc (showString "/") , prt 5 exp])
   EMinus exp -> prPrec i 5 (concatD [doc (showString "-") , prt 6 exp])
   Call identifier callargss -> prPrec i 6 (concatD [prt 0 identifier , doc (showString "(") , prt 0 callargss , doc (showString ")")])
   EVar identifier -> prPrec i 6 (concatD [prt 0 identifier])
   EInt n -> prPrec i 6 (concatD [prt 0 n])
   Etrue  -> prPrec i 6 (concatD [doc (showString "true")])
   Efalse  -> prPrec i 6 (concatD [doc (showString "false")])


instance Print Assignment where
  prt i e = case e of
   Assign identifier expression -> prPrec i 0 (concatD [prt 0 identifier , doc (showString "=") , prt 0 expression])
   AArith identifier arassign expression -> prPrec i 0 (concatD [prt 0 identifier , prt 0 arassign , prt 0 expression])
   AIncDec identifier incdec -> prPrec i 0 (concatD [prt 0 identifier , prt 0 incdec])


instance Print Type where
  prt i e = case e of
   TInt  -> prPrec i 0 (concatD [doc (showString "int")])
   TBool  -> prPrec i 0 (concatD [doc (showString "bool")])


instance Print Identifier where
  prt i e = case e of
   Id id -> prPrec i 0 (concatD [prt 0 id])

  prtList es = case es of
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])

instance Print ArAssign where
  prt i e = case e of
   AAPlus  -> prPrec i 0 (concatD [doc (showString "+=")])
   AAMinus  -> prPrec i 0 (concatD [doc (showString "-=")])
   AAMulti  -> prPrec i 0 (concatD [doc (showString "*=")])
   AADiv  -> prPrec i 0 (concatD [doc (showString "/=")])


instance Print IncDec where
  prt i e = case e of
   Increment  -> prPrec i 0 (concatD [doc (showString "++")])
   Decrement  -> prPrec i 0 (concatD [doc (showString "--")])



