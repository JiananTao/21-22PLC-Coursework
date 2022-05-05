import StqlTokens
import StqlGrammar
import StqlEval
import StqlTypes
import System.Environment
import Control.Exception
import System.IO
import Data.List
import System.Directory
main :: IO ()
main = catch main' noParse

main' :: IO ()
main' = do (fileName : _ ) <- getArgs
           sourceSolution <- readFile fileName
           let resultAlex = alexScanTokens sourceSolution
           
           let parsedProg = parseCalc resultAlex
           
           paths <- getCurrentDirectory >>= getDirectoryContents
           let fileNameList = filter (isInfixOf ".ttl") paths
           s <- return <$> mapM readFile (filter (isInfixOf ".ttl") paths)
           let fileList = head s

           let typedProg = typeLoop ([], [],[], parsedProg)
           let result = unlines $ (unparseAll (evalLoop (parsedProg,fileToEnv fileNameList fileList,[],[],[])))
           {-
           putStrLn ("Parsing : " ++ sourceSolution)   
           putStrLn ("Tokens as " ++ show resultAlex ++ "\n")
           putStrLn ("Parsed as " ++ show parsedProg ++ "\n")
           putStrLn ("Type Checking...")
           putStrLn ("  " ++ typedProg ++ "\n") 
           -}
           writeFile "out.txt" ("Result as \n" ++ result)
           
           putStrLn result
           
           
noParse :: ErrorCall -> IO ()
noParse e = do let err =  show e
               hPutStr stderr err
               return ()

fileToEnv :: [String] -> [String] -> [(String,Expr)]
fileToEnv na fi = [ (s1,TmString s2) | (s1,s2) <- (zip na fi) ]