module Main where

import System.Environment (getArgs)
import Language.Maude.Types
import Language.Maude.Parser.Outer

main :: IO ()
main = do (fName : _) <- getArgs
          readFile fName >>= putStrLn . process

process :: String -> String
process = id
