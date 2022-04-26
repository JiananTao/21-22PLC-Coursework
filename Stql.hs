import StqlTokens
import StqlGrammar
import StqlEval
import StqlTypes
import System.Environment
import Control.Exception
import System.IO
import Data.List

main :: IO ()
main = catch main' noParse

main' :: IO ()
main' = do (fileName : _ ) <- getArgs
           sourceSolution <- readFile fileName
           sourceBar <- readFile "bar.ttl"
           sourceFoo <- readFile "foo.ttl"
           
           putStrLn ("Parsing : " ++ sourceSolution)
           let resultAlex = alexScanTokens sourceSolution
           putStrLn ("Tokens as " ++ show resultAlex ++ "\n")
           
           let parsedProg = parseCalc resultAlex
           putStrLn ("Parsed as " ++ show parsedProg ++ "\n")
           
           putStrLn ("Type Checking...")
           let typedProg = typeOf' [] parsedProg
           putStrLn ("  Passed with type \"" ++ (unparseType typedProg) ++ "\"\n") 
           
           let result = unlines $ reverse (unparseAll (evalLoop sourceBar sourceFoo parsedProg))
           putStrLn ("Result as \n" ++ result)
           writeFile "out.ttl" result

noParse :: ErrorCall -> IO ()
noParse e = do let err =  show e
               hPutStr stderr err
               return ()
