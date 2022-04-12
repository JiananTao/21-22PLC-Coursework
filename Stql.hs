import StqlTokens
import StqlGrammar
import StqlEval
import System.Environment
import Control.Exception
import System.IO
import Data.List



main :: IO ()
main = catch main' noParse

main' = do (fileName : _ ) <- getArgs
           sourceSolution <- readFile fileName
           sourceBar <- readFile "bar.ttl"
           sourceFoo <- readFile "foo.ttl"
           sourceInput <- readFile "input.ttl"
           putStrLn ("Parsing : " ++ sourceSolution)

           let resultAlex = alexScanTokens sourceSolution
           putStrLn ("Tokens as " ++ show resultAlex ++ "\n")
           let parsedProg = parseCalc resultAlex
           putStrLn ("Parsed as " ++ show parsedProg ++ "\n")

           let result = unlines (getResult (evalLoop sourceBar sourceFoo parsedProg))
           putStrLn ("Result as \n" ++ result)
           writeFile "out.ttl" (listToOut (allL (socToList sourceInput)) ++ show (cFom sourceInput))


noParse :: ErrorCall -> IO ()
noParse e = do let err =  show e
               hPutStr stderr err
               return ()

listToOut :: [String] -> String
listToOut = unlines

allL :: [String ] -> [String ]
allL l = vars l ++ nors l 

nors :: [String] -> [String]
nors l = [ x | x <- l, not (eqString x "@base") && not (eqString x "@prefix")]

vars :: [String] -> [String]
vars l = varBase l ++ varPrefix l ++ varPrefixBroken l
varBase :: [String] -> [String]
varBase l = [ "Var GlobalBase:" ++ (x \\ "@base") | x <- l, eqString x "@base"]
varPrefix :: [String] -> [String]
varPrefix l = [ "Var" ++ (x \\ "@prefix") | x <- l,  eqString x "@prefix" && isInfixOf "http://" x]
varPrefixBroken :: [String] -> [String]
varPrefixBroken l = [ "BrokenVar" ++ (x \\ "@prefix") | x <- l,  eqString x "@prefix" && not (isInfixOf "http://" x)]

socToList :: String -> [String]
socToList = wordsWhen (=='\n')

--map repl "  "



{-
-tools and check function


-}

repl :: Char -> Char
repl '<' = ' '
repl  c  = c


--Check the format
cFom :: String -> Int
cFom str = length (filter (== '<') str) - length (filter (== '>') str)

--print $ wordsWhen (=='.') "get.ttl.split"
wordsWhen     :: (Char -> Bool) -> String -> [String]
wordsWhen p s =  case dropWhile p s of
                      "" -> []
                      s' -> w : wordsWhen p s''
                            where (w, s'') = break p s'


--check if it is global vars
--eqString "@base <http://www.cw.org/> ." "@base"
eqString :: String -> String -> Bool
eqString (c1:cs1) (c2:cs2) = c1 == c2 && cs1 `eqString` cs2
eqString _        []       = True
eqString _        _        = False
