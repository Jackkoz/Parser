import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )
import System.Directory (doesFileExist)

import LexGram
import ParGram
import SkelGram
import PrintGram
import AbsGram

import ErrM

import Interpreter

type ParseFun a = [Token] -> Err a

myLLexer = myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

runFile :: (Print a, Show a) => Verbosity -> ParseFun a -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: (Print a, Show a) => Verbosity -> ParseFun a -> String -> IO ()
run v p s = let ts = myLLexer s in case p ts of
           Bad s    -> do putStrLn "\nParse              Failed...\n"
                          putStrV v "Tokens:"
                          putStrV v $ show ts
                          putStrLn s
           Ok  tree -> do putStrLn "\nParse Successful!"
                          showTree v tree

showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

--main :: IO ()
--main = do args <- getArgs
--          case args of
--            [] -> hGetContents stdin >>= run 2 pProgram
--            "-s":fs -> mapM_ (runFile 0 pProgram) fs
--            fs -> mapM_ (runFile 2 pProgram) fs

main = do
  args <- getArgs
  if length args < 1
    then do
      putStrLn "you have to provide a source file name;"
    else do
      let fileName = args !! 0
      fileExists <- doesFileExist $ fileName
      if fileExists
        then do
          input <- readFile fileName
          case pProgram (myLexer input) of
            Bad s -> putStrLn s
            Ok  p -> execProgram p
        else do
          putStrLn $ "file `" ++ fileName ++ "` does not exist;"




