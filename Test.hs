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

main :: IO ()
main = do
    args <- getArgs
    if length args /= 1
        then do putStrLn "Please provide filename to interpret as the only argument"
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
                putStrLn $ fileName ++ " does not exist"

