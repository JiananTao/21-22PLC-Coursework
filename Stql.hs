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
           --putStrLn ("Parsing : " ++ sourceSolution)
           let resultAlex = alexScanTokens sourceSolution
           --putStrLn ("Tokens as " ++ show resultAlex ++ "\n")
           
           let parsedProg = parseCalc resultAlex
           --putStrLn ("Parsed as " ++ show parsedProg ++ "\n")
           
           paths <- getCurrentDirectory >>= getDirectoryContents
           let fileNameList = filter (isInfixOf ".ttl") paths
           s <- return <$> mapM readFile (filter (isInfixOf ".ttl") paths)
           let fileList = head s

           --putStrLn ("Type Checking...")
           --let typedProg = unlines $ reverse (unparseAllType (typeLoop ([], [], [],[], parsedProg)))
           --putStrLn ("  Passed with type \n" ++ typedProg ++ "\n") 

           let result = unlines $ (unparseAll (evalLoop (parsedProg,fileToEnv fileNameList fileList,[],[],[])))
           --putStrLn ("Result as \n" ++ result)
           putStrLn result
           

--("bar.ttl",TmString sourceBar),("foo.ttl",TmString sourceFoo)
noParse :: ErrorCall -> IO ()
noParse e = do let err =  show e
               hPutStr stderr err
               return ()

fileToEnv :: [String] -> [String] -> [(String,Expr)]
fileToEnv na fi = [ (s1,TmString s2) | (s1,s2)<- zip na fi ]