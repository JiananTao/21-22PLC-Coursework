import StqlTokens
import StqlGrammar
import StqlEval
import System.Environment
import Control.Exception
import System.IO

main :: IO ()
main = catch main' noParse

main' = do (fileName : _ ) <- getArgs
           sourceText <- readFile fileName
           putStrLn ("Parsing : " ++ sourceText)
           
           let resultAlex = alexScanTokens sourceText
           putStrLn ("Tokens as " ++ show resultAlex ++ "\n")

           let parsedProg = parseCalc resultAlex
           putStrLn ("Parsed as " ++ show parsedProg ++ "\n")

           let result = unparse (evalLoop parsedProg)
           writeFile "out.ttl" result

noParse :: ErrorCall -> IO ()
noParse e = do let err =  show e
               hPutStr stderr err
               return ()


