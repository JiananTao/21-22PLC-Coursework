-- Author: Julian Rathke, 2018
-- Provides a CEK implementation of the \Stql language from the lecture notes
module StqlEval where
import StqlGrammar
import Data.List ( isInfixOf, (\\), elemIndices, intercalate, nub )
import Data.Char ( isSpace, isDigit )
import GHC.OldList (elemIndex)
import Data.Maybe (isNothing)
import Data.List (isPrefixOf)
import Data.List (sort)


{-
data StqlType = TyInt | TyString 
   deriving (Show,Eq)
type Environment = [ (String,Expr) ]
data Expr = TmInt Int | TmString String 
            | TmAdd Expr Expr | TmVar String 
            | TmAddString Expr Expr
            | TmLet String StqlType Expr
            | TmList Expr | TmListSeg Expr Expr
            | TmPrint Expr | TmPlusVar Expr Expr
            | TmGetVar String | TmReadEnv | TmFormat Expr
            | TmFillBasePrefixReady String 
            | TmProcSemicComma String 
            | TmClear String StqlType | TmClearAll
            | TmLiteralsNum String
            | TmDelimit String Expr String 
            | TmCompare String String String String
            | TmEnd Expr Expr | TmEnd2 Expr
            | TmReadTTLFile String
    deriving (Show,Eq)
-}

data StrFrame = HPlusStr String | PlusHStr Str
              | HListStr String | ListHStr Str
data Frame =
           HAdd Expr Environment | AddH Expr
           | HPlus Expr Environment | PlusH Expr
           | Print | Format | List 
           | Processing Expr | HLet String StqlType
type Kontinuation = [ Frame ]
type Result = [Expr]
type Processing = [Frame]
type State = (Expr,Environment,Kontinuation,Result,Processing)

{-These interact with environment variables, and whether there is a value to output
--
--
--
-}
-- Look up a value in an environment and unpack it
getValueBinding :: String -> Environment -> Expr
getValueBinding x [] = error "Variable binding not found"
getValueBinding x ((y,e):env) | x == y    = e
                              | otherwise = getValueBinding x env
getValueBinding' :: Expr -> Environment -> Expr
getValueBinding' x [] = error "Variable binding not found"
getValueBinding' (TmVar x) ((y,e):env) | x == y    = e
                                       | otherwise = getValueBinding x env
getValueBinding' _ _ = error ""

update :: Environment -> String -> Expr -> Environment
update env x e1 = (x,e1) : [ (y,e2) | (y,e2) <- env, x /= y ]
-- Checks for terminated expressions
isValue :: Expr -> Bool
isValue (TmString _) = True
isValue (TmInt _) = True
isValue _ = False

whichExp :: Expr -> String
whichExp (TmString _) = "String"
whichExp (TmInt _) = "Int"
whichExp (TmVar _) = "Var"
whichExp _ = error ""

{-
--evalStr is one of the main functions, which used for '|'
--to make sure they just have String input
-}
evalStr :: (String, Str, [StrFrame]) -> String
evalStr (s,(TsListSeg s1 s2),k) = evalStr (s1, s2, (HListStr s):k)
evalStr (s1, (TsString s2), (HPlusStr s):k) = evalStr' ((TsString s1), (HPlusStr s2):((HPlusStr s):k)) 
evalStr (s1, (TsString s2), (HListStr s):k) = evalStr' ((TsString s1), (HListStr s2):((HListStr s):k))
evalStr' :: (Str, [StrFrame]) -> String
evalStr' (s1, (HPlusStr s):k) = evalStr' ((TsString (rmQuo (unparseStr s1) ++ rmQuo s)), k)
evalStr' (s1, (HListStr s):k) = evalStr' ((TsString (rmQuo (unparseStr s1) ++ "\n" ++ rmQuo s)), k)
evalStr' (s1, []) = unparseStr s1
{-
--eval1 is the main function, which is used to pattern match each grammar and make corresponding processing
--
--
-}
--Small step evaluation function
eval1 :: State -> State
-- Evaluation rules for plus and sort var
-- Only accept Var TmString plus
eval1 (TmPlusVar e1 e2,env,k,r,p) = (e1,env,HPlus e2 env:k,r,p)
eval1 (TmVar n,env1,(HPlus e env2):k,r,p) = if whichExp e' == "String" then (e,env2 ++ env1,PlusH e' : k,r,p) else error "PlusVar only accept String in Var now"
                                         where e' = getValueBinding n env1
eval1 (TmVar m,env,(PlusH (TmString n)):k,r,p) = (TmString (toListSort (unparse e' ++ "\n" ++ n)),env,k,r,p)
                                         where e'  = getValueBinding m env

-- Get var
eval1 (TmVar x,env,k,r,p) = (e',env,k,r,p)
                    where e' = getValueBinding x env


-- Rule for Print
eval1 (TmPrint e,env,k,r,p) = (e,env,k ++ [Print] ,r,p)

-- Evaluation rules for End operator
eval1 (TmEnd2 e,env,k,r,p) = (e,env,k,r,p)
eval1 (TmEnd e1 e2,env,k,r,p) = (e2,env,k,r,Processing e1:p)


-- Evaluation rules for Clear blocks
eval1 (TmClear x typ,env,k,r,p) = (TmString ("clear " ++ x),clear env x,k,r,p)
eval1 (TmClearAll,env,k,r,p) = (TmString "ClearAll excpet pre-load file",clearAll env,k,r,p)

-- Rule for read file evaluations Read a pre-stored file string
eval1 (TmReadTTLFile s,env,k,r,p) | s /= "\"bar.ttl\"" && s /= "\"foo.ttl\"" = error "Only supports reading foo.ttl and bar.ttl"
                                  | otherwise                                = (TmVar (rmQuo s),env,k,r,p)

-- Evaluation rules for plus number operator
eval1 (TmAdd e1 e2,env,k,r,p) = (e1,env,HAdd e2 env:k,r,p)
eval1 (TmInt n,env1,(HAdd e env2):k,r,p) = (e,env2 ++ env1,AddH (TmInt n) : k,r,p)
eval1 (TmInt m,env,(AddH (TmInt n)):k,r,p) = (TmInt (n + m),env,k,r,p)

-- Evaluation rules for plus string operator
eval1 (TmAddString e1 e2,env,k,r,p) = (e1,env,HPlus e2 env:k,r,p)
eval1 (TmString n,env1,(HPlus e env2):k,r,p) = (e,env2 ++ env1,PlusH (TmString (rmQuo n)) : k,r,p)
eval1 (TmString m,env,(PlusH (TmString n)):k,r,p) = (TmString (n ++ rmQuo m),env,k,r,p)


-- Evaluation rules for List operator
eval1 (TmList e1 e2,env,k,r,p) = (TmString (evalStr (e1, e2, [])),env,k ++ [List],r,p)


-- Evaluation rules for GetVar blocks
eval1 (TmGetVar s,env,k,r,p) = (TmString "loaded var",env',k,r,p)
                           where env' = getVarFromFile (varStr s env) env
-- Evaluation rules for ReadEnv blocks
eval1 (TmReadEnv, env,k,r,p) = (TmString (listEnv env),env,k,r,p)
-- Evaluation rules for Format Function blocks
eval1 (TmFormat e, env,k,r,p) = (e,env,Format:k,r,p)
eval1 (TmString s,env,Format:k,r,p) = (TmString s',env,k,r,p)
                           where s' = unlines $ formatResultF (socToList s)
-- Evaluation rules for ProcSemicComma Function blocks
eval1 (TmProcSemicComma s, env,k,r,p) = (TmString (s' ++ s''),env,k,r,p)
                           where s' = unlines ( procProcComma (getNeedProcComma (socToList (varStr s env)))
                                                ++ getNeedProcComma' (socToList (varStr s env)))
                                 s'' = unlines ( procProcSemic (getNeedProcSemic (socToList (varStr s env)))
                                                ++ getNeedProcSemic' (socToList (varStr s env)))
-- Evaluation rules for FillBasePrefixReady Function blocks
eval1 (TmFillBasePrefixReady s, env,k,r,p) = (TmString s',env,k,r,p)
                           where s' = procFillPr (unlines (getNeedFillPr (socToList (varStr s env)))) env ""
                                   ++ "\n" ++ procFillBa (unlines (getNeedFillBa (socToList (varStr s env)))) env
                                   ++ "\n" ++ unlines (getNeedReady (socToList (varStr s env)))

-- Evaluation rules for Delimit blocks
eval1 (TmDelimit pos s x, env,k,r,p) | rmQuo pos == "Subj" && whichExp s == "String" =
                        let s' = pcDelimit 1 (rmQuo (unparse s) ) (socToList (varStr x env)) in (TmString s',env,k,r,p)
                                     | rmQuo pos == "Subj" && whichExp s == "Var"    =
                        let s' = pcDelimit 1 (rmQuo (unparse (getValueBinding' s env))) (socToList (varStr x env)) in (TmString s',env,k,r,p)
                                     | rmQuo pos == "Pred" && whichExp s == "String"    =
                        let s' = pcDelimit 2 (rmQuo (unparse s) ) (socToList (varStr x env)) in (TmString s',env,k,r,p)
                                     | rmQuo pos == "Pred" && whichExp s == "Var"    =
                        let s' = pcDelimit 2 (rmQuo (unparse (getValueBinding' s env))) (socToList (varStr x env)) in (TmString s',env,k,r,p)
                                     | rmQuo pos == "Obj" && whichExp s == "String"    =
                        let s' = pcDelimit 3 (rmQuo (unparse s) ) (socToList (varStr x env)) in (TmString s',env,k,r,p)
                                     | rmQuo pos == "Obj" && whichExp s == "Var"    =
                        let s' = pcDelimit 3 (rmQuo (unparse (getValueBinding' s env))) (socToList (varStr x env)) in (TmString s',env,k,r,p)
                                     | otherwise = error "Delimit must obey this rule: Delimit ""Pred""Subj""Obj""(3 choose 1) Var/String In Var"

-- Evaluation rules for Compare blocks
eval1 (TmCompare s1 f1 s2 f2, env,k,r,p) = (TmString s', env,k,r,p)
                           where s' = pcCompare (rmQuo s1) (socToList (varStr f1 env)) (rmQuo s2) (socToList (varStr f2 env))
-- Evaluation rules for LiteralsNum blocks
eval1 (TmLiteralsNum s, env,k,r,p) = (TmString s', env,k,r,p)
                           where s' = pcLiteralsNum (socToList (varStr s env))

-- Evaluation rules for Let blocks
eval1 (TmLet x typ e,env,k,r,p) | isValue e = (e,update env x e,k,r,p)
                                | otherwise = (e,env,HLet x typ:k,r,p)
eval1 (v,env,(HLet x typ):k,r,p) | isValue v = (TmLet x typ v,env,k,r,p)
                                 | otherwise = error "Only support type String and Int in Let Block"

-- Rule for terminated evaluations
--eval1 (v,env,[],r,[]) | isValue v = (v,env,[],v:r,[])
eval1 (v,env,[],r,[]) | isValue v = (v,env,[],r,[])
--eval1 (v,env,[],r,(Processing e):p) | isValue v = (e,env,[],v:r,p)
eval1 (v,env,[],r,(Processing e):p) | isValue v = (e,env,[],r,p)
eval1 (v,env,Print:k,r,(Processing e):p) | isValue v = (e,env,[],v:r,p)
                                         | otherwise = error "Print can only output functions which result is Int or String"
eval1 (v,env,Print:k,r,p) | isValue v = (v,env,[],v:r,p)
                          | otherwise = error "Print can only output functions which result is Int or String"
eval1 (v,env,List:k,r,p) | isValue v = (v,env,[],r,p)
                         | otherwise = error "[xxx|yyy|zzz] xxx、yyy and zzz must be String Type"
-- Rule for runtime errors
eval1 (e,env,k,r,p) = error "Unknown Evaluation Error"



{-------------------------------------------------------------------------------------------
--*The GetVars function must be run in advance to fill in the parameters in the file
--These are the ways to get the fill ttl file incomplete
--
--
-}
pcDelimit :: Int -> String -> [String] -> String
pcDelimit i s l | "\n" `isInfixOf` s = unlines $ nub [ r | r <- l , r' <- wordsWhen (=='\n') s, r' `isInfixOf` r]
                | otherwise = unlines [ rr | (r1,r2,r3,rr) <- splitTriples l , case i of
                                                  1 -> s `isInfixOf` r1
                                                  2 -> s `isInfixOf` r2
                                                  3 -> s `isInfixOf` r3
                                                  _ -> error "The error occurs in the pcDelimit function in StqlEval.hs, this is a developer error"]
--For Compare Function
--Because it has been verified that there are 3, so! ! no error is thrown
pcCompare :: String -> [String] -> String -> [String] -> String
pcCompare s1 f1 s2 f2 | s1 == "Obj" && s2 == "Subj" = unlines $ nub $ [r1 |
                                                      r1 <- f1, length (filter (== '<') r1) == 3,
                                                      r2 <- f2, length (filter (== '<') r2) == 3,
                                                      wordsWhen (== '>') r1 !! 2 == head (wordsWhen (== '>') r2)]
                      | otherwise = "Only support s1 about Obj, s2 about Subj"
--For LiteralsNum Function
pcLiteralsNum :: [String] -> String
pcLiteralsNum s = (unlines $ sort $ [ r'' |
                  (r1,r2,r3,r') <- splitTriples s, ifAllDigit r3,
                  readInt r3 < 0 || readInt r3 > 99,
                  let r'' = r1 ++ " <http://www.cw.org/problem5/#inRange> false ."
                  ]) ++ (
                  unlines $ sort $ [ r'' |
                  (r1,r2,r3,r') <- splitTriples s, ifAllDigit r3,
                  readInt r3 >= 0 && readInt r3 <= 99,
                  let r'' = r1 ++ r2 ++ show (readInt r3 + 1) ++ "\n" ++ r1 ++ " <http://www.cw.org/problem5/#inRange> true ."
                  ])
--Applies to the Format function to remove spaces, format trailing edges, and remove duplicates
--And determine whether the ending is semantically repeated
-- * Except for 50, 20, 10, other numbers have unknown bugs, maybe the space is wrong
--fromResult will return perfectly formatted results, fromResult' is the processing of semantically identical items
--   .
formatResultF :: [String] -> [String]
formatResultF l = [ r' | r <- formatType' (formatType (formatResult' (formatResult l))),
                        let r' = replace "  " " " r]
formatResult :: [String] -> [String]
formatResult l = nub [ s'' | s <- l, let s' = replace ". " "" (filter (/=' ') s ++ "  ."),
                                     let s'' = replace "  " " " $ reverse (replaceFirst  '>' " >" (reverse s'))]
typeSort :: String -> String
typeSort s | isInfixOf "\"" s = "4"
           | isInfixOf "http://" s = "1"
           | isInfixOf "true" s = "3"
           | isInfixOf "false" s = "3"
           | ifAllDigit s = "2"
           | otherwise = s
formatType :: [String] -> [String]
formatType l =  sort $ nub $ [ r' | (r1,r2,r3,rr) <- splitTriples l,let r' = if isInfixOf "<http://" r3 then r1 ++ r2 ++ typeSort r3 ++ r3 ++ " ." else   r1 ++ r2  ++ typeSort r3 ++ " " ++ r3 ++ " ." ]                                                              
formatType' :: [String] -> [String]                                                                   
formatType' l = [ r' | r <- l, let r' = (replace ">4" ">" (replace ">3" ">" (replace ">2" ">" (replace ">1" ">" r))))]
--let r' = r1 ++ r2 ++ " " ++ r3 ++ " ."
--let r3' = replace ". ." "" r3
--for something like +50 and 50 same means
formatResult' :: [String] -> [String]
formatResult' l =  sort $ [ r' | (r1,r2,r3,rr) <- splitTriples l, ifAllDigit r3, let r' = r1 ++ r2 ++ " " ++ show (readInt r3) ++ " ."]
                   ++ [ rr | (r1,r2,r3,rr) <- splitTriples l, not $ ifAllDigit r3]
--formatResult' l =  sort $ [ r' | (r1,r2,r3,rr) <- splitTriples l, ifAllDigit r3, let r' = r1 ++ r2 ++ show (readInt r3)] ++ [ rr | (r1,r2,r3,rr) <- splitTriples l, not $ ifAllDigit r3]



--TODO: delete Duplicates
--ProcComma Part，example: <testSubA> <testObjList> -5 , 10 , 20 .
getNeedProcComma :: [String] -> [String]
getNeedProcComma l = [ s | s <- l, isInfixOf "," s]
getNeedProcComma' :: [String] -> [String]
getNeedProcComma' l = [ s | s <- l, not ( isInfixOf "," s) && not ( isInfixOf ";" s)]
procProcComma :: [String] -> [String]
procProcComma l = concat $ procProcComma' [ (s1,s2) | s <- l, let s' = s \\ " ", let s1 = fst $ break isSpace s', let s2 = snd $ break isSpace s']
procProcComma' :: [(String,String)] -> [[String]]
procProcComma' l = [ s | (s1,s2) <- l, let s = map (s1++) (split "," s2)]
--ProcSemic part, example: <testSubA> <testPredList> -5 ; <testPredList> 10 ; <testPredList> 20 .
getNeedProcSemic :: [String] -> [String]
getNeedProcSemic l = [ s | s <- l, isInfixOf ";" s]
getNeedProcSemic' :: [String] -> [String]
getNeedProcSemic' l = [ s | s <- l, not ( isInfixOf "," s) && not ( isInfixOf ";" s)]
procProcSemic :: [String] -> [String]
procProcSemic l = concat $ procProcSemic' [ (s1,s2) | s <- l, let s1 = fst $ break isSpace s, let s2 = snd $ break isSpace s]
procProcSemic' :: [(String,String)] -> [[String]]
procProcSemic' l = [ s | (s1,s2) <- l, let s = map (s1++) (split ";" s2)]

--For FillBasePrefixReady Function
--Ready Part example: <http://www.cw.org/subjectA> <http://www.cw.org/predicateA> <http://www.cw.org/objectA> . 
getNeedReady :: [String] -> [String]
getNeedReady l = [ s | s <- l, length (split "http://" s) == 4]
--For FillBase Part, example: <prob4B> <testPredA> <prob4C> .
--example: <http://www.cw.org/#problem2> <testPredA> true .
getNeedFillBa :: [String] -> [String]
getNeedFillBa l = [ s | s <- l, (length (split "http://" s) <= 2) && (isInfixOf ">") s && (not ("/>" `isInfixOf` s))]
procFillBa :: String -> Environment -> String
procFillBa s env = filter (/=' ') (procFillBa' s env)
procFillBa' :: String -> Environment -> String
procFillBa' s env = concat [ r' | r <- split "<" s, let r'
                                                          | "http://" `isInfixOf` r = "<" ++ r
                                                          | not ("http://" `isInfixOf` r) && isInfixOf ">" r = (varStr "BaseVar" env \\ ">") ++ r
                                                          | otherwise = r]
--Applicable to FillPrefix Part, example: p:subjectC
--s is a string for an entire file
getNeedFillPr :: [String] -> [String]
getNeedFillPr l = [ s | s <- l, not ("http://" `isInfixOf` s) && isInfixOf ":" s && not ("@" `isInfixOf` s)]
procFillPr :: [Char] -> Environment -> String -> String
procFillPr s env sum | s == "" = ""
                     | isNothing (elemIndex ':' (s \\ ":"))  = (init $ init (replace ".>" ">.\n" (filter (/=' ') (sum ++ beFill i i' s env)))) ++ ">."
                     | otherwise  = procFillPr s' env (sum ++ beFill i i' s env)
                where
                  s' = drop (rmMaybe i') s
                  i  = elemIndex ':' s
                  i' = elemIndex ':' (s \\ ":")
beFill :: Maybe Int -> Maybe Int -> String -> Environment -> String
beFill (Just 1) (Just i') s env = let s' = take (i'-1) s in (varStr ((s !! 0):"") env \\ ">") ++ drop 2 s' ++ ">"
beFill (Just i) (Just i') s env = let s' = take (i'-1) s in (varStr ((s !! (i-1)):"") env \\ ">") ++ drop (i + 1) s'
beFill (Just i) Nothing s env  = (varStr ((s !! (i-1)):"") env \\ ">") ++ drop (i+1) s
beFill _ _ s env = error "FillPrefix函数出错"

{-
--Here is the function to merge sort the TTL output files
--
--
-}
toListSort :: String -> String
toListSort s = unlines (sort (split "\n" s))

{-------------------------------------------------------------------------------------------
--These are the methods to get the variables in the file
--Applies to the GetVars function
--
--
--}
getVarFromFile :: String -> Environment -> Environment
getVarFromFile s env = env ++ varBase (socToList s) ++ varPrefix (socToList s) ++ varPrefixBroken (socToList s)
--TODO：Whether it is empty or not is not detected here, that is, the default input ttl has @base
varBase :: [String] -> Environment
varBase l = [("BaseVar",TmString (varBaseStr l))]
varBaseStr :: [String] -> String
varBaseStr l = head [ init (filter  (\x -> x /= ' ') (s \\ "@base")) | s <- l, eqString s "@base"]
varPrefix :: [String] -> Environment
varPrefix l = [ procPre (s \\ "@prefix") " "  | s <- l,  eqString s "@prefix" && isInfixOf "http://" s]
varPrefixBroken :: [String] -> Environment
varPrefixBroken l = [ procPre (s \\ "@prefix") (varBaseStr l) | s <- l,  eqString s "@prefix" && not (isInfixOf "http://" s)]
procPre :: String -> String -> (String , Expr)
procPre s a = (filter (\x -> x /= ' ' && x /= ':') (head (wordsWhen (=='<') s)),
               if a /= " " then TmString ((a \\ ">") ++ (filter  (\x -> x /= ' ' && x /= '.' ) ((wordsWhen (=='<') s !! 1))))
               else TmString (init (filter  (\x -> x /= ' ') ("<" ++ (wordsWhen (=='<') s !! 1)))))

{------------------------------------------------------------------------------------------------
--These are some of the functions used by the simple function
--
--
-}
rmLast :: Eq a => [a] -> [a] -> [a]
rmLast s x = reverse $ reverse s \\ x
--For ReadEnv Function
--TODO：Can only detect strings, other formats throw errors
listEnv :: Environment -> String
listEnv env = unlines [ s ++ " is " ++ unparse e | (s,e) <- env, s /= "foo.ttl" && s /= "bar.ttl"]
--for Clear Function
clear :: Environment -> String -> Environment
clear env x = [ (y,e2) | (y,e2) <- env, x /= y ]
--for ClearAll Function
clearAll :: Environment -> Environment
clearAll env = [ (y,e2) | (y,e2) <- env, y == "foo.ttl" || y == "bar.ttl" ]

{-------------------------------------------------------------------------------------------
--tools and check function
--These are the generic little functions that use
--
--
-}
splitTriples :: [String] -> [(String,String,String,String)]
splitTriples l = [ (r1, replace ">." ">" r2,replace ".<" "<" r3,r') | s <- l, let s' = filter (/=' ') s,
                                         let i3 = if length ((elemIndices '>' (reverse s'))) == 2 then (elemIndices '>' (reverse s')) !! 0 else ((elemIndices '>' (reverse s')) !! 1),
                                         let r3 = init $ reverse ( take i3 (reverse s')),
                                         let i1 = rmMaybe (elemIndex '>' s'),
                                         let r1 = init $ take (i1+2) s',
                                         let r2 = filter (/=' ') (init $ reverse ((reverse (replace r1 "" s)) \\ (reverse r3))),
                                         let r' = r1 ++ r2 ++ " " ++ r3 ++ " ."]

rmQuo :: String -> String
rmQuo [] = ""
rmQuo s =  if (head s == '\"') && (last s == '\"') then init (tail s) else s

replaceFirst :: Char -> String -> String -> String
replaceFirst old new s = take (i) s ++ new ++ snd (splitAt (i+1) s)
                        where i = rmMaybe (elemIndex old s)
ifHasDigit :: String  -> Bool
ifHasDigit s = not $ null [ r | r <- s, isDigit r]
ifAllDigit :: String  -> Bool
ifAllDigit s = not (null [ r | r <- s]) && (length [ r | r <- s]) == length ([ r | r <- s, isDigit r || (r == '+') || (r == '-')])
--TODO: use filter to remove space
readInt :: String -> Int
readInt s | eqString s "+" = read (tail s)
          | eqString s "-" = negate (read (tail s))
          | otherwise      = read s
          where s' = filter (==' ') s
rmMaybe :: Maybe a -> a
rmMaybe (Just a) = a
rmMaybe Nothing = error "error in reMaybe function which means something has Nothing in Maybe a"
varStr :: String -> Environment -> String
varStr s env = unparse (getValueBinding (s \\ ['\"','\"']) env)

--Convert String to List
socToList :: String -> [String]
socToList = wordsWhen (=='\n')
--example: print $ wordsWhen (=='.') "get.ttl.split"
--["get","ttl","split"]
wordsWhen     :: (Char -> Bool) -> String -> [String]
wordsWhen p s =  case dropWhile p s of
                      "" -> []
                      s' -> w : wordsWhen p s''
                            where (w, s'') = break p s'
--Check the format
cFom :: String -> Int
cFom str = length (filter (== '<') str) - length (filter (== '>') str)
--check if it is variables
--example: eqString "@base <http://www.cw.org/> ." "@base"
eqString :: String -> String -> Bool
eqString (c1:cs1) (c2:cs2) = c1 == c2 && cs1 `eqString` cs2
eqString _        []       = True
eqString _        _        = False

{-
--The following is from the external missingH package
--import Data.List.Utils
--https://hackage.haskell.org/package/MissingH-1.5.0.1/docs/src/Data.List.Utils.html#startswith
--
-}
-------
merge ::  (Ord a) => [a] -> [a] -> [a]
merge = mergeBy (compare)
mergeBy :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
mergeBy _   [] ys = ys
mergeBy _   xs [] = xs
mergeBy cmp (allx@(x:xs)) (ally@(y:ys))
    | (x `cmp` y) <= EQ = x : mergeBy cmp xs ally
    | otherwise = y : mergeBy cmp allx ys

--------
replace :: Eq a => [a] -> [a] -> [a] -> [a]
replace old new l = intercalate new . split old $ l
spanList :: ([a] -> Bool) -> [a] -> ([a], [a])
spanList _ [] = ([],[])
spanList func list@(x:xs) =
    if func list
       then (x:ys,zs)
       else ([],list)
    where (ys,zs) = spanList func xs
breakList :: ([a] -> Bool) -> [a] -> ([a], [a])
breakList func = spanList (not . func)
split :: Eq a => [a] -> [a] -> [[a]]
split _ [] = []
split delim str =
    let (firstline, remainder) = breakList (isPrefixOf delim) str
        in
        firstline : case remainder of
                                   [] -> []
                                   x -> if x == delim
                                        then [] : []
                                        else split delim
                                                 (drop (length delim) x)

{-------------------------------------------------------------------------------------------
--These are the function main programs
--Responsible for docking with the main method in Stql.hs
--
-}
--Function to iterate the small step reduction to termination
evalLoop :: String -> String -> Expr -> [Expr]
evalLoop bar foo e = eval (e,[("bar.ttl",TmString bar),("foo.ttl",TmString foo)],[],[],[])
eval :: (Expr, Environment, Kontinuation, Result, Processing) -> [Expr]
eval (e,env,k,r,p) | e' == e && isValue e' && null k && null p  = r'
                   | otherwise                                  = eval (e',env',k',r',p')
            where (e',env',k',r',p') = eval1 (e,env,k,r,p)
--Function to unparse underlying values from the AST term
unparse :: Expr -> String
unparse (TmString n) = n
unparse (TmInt n) = show n
unparse _ = "Unknown"
unparseStr :: Str -> String
unparseStr (TsString n) = n
unparseAll :: [Expr] -> [String]
unparseAll = map unparse
{-------------------------------------------------------------------------------------------
--These are the some useless function
--May be use in funture
--
-}
-- | HList Expr Environment | ListH Expr
--           | HIf Expr Expr Environment
--           | HPair Expr Environment | PairH Expr
--           | FstH | SndH 
--isValue TmTrue = True
--isValue TmFalse = True
--isValue TmUnit = True
--isValue (TmPair e1 e2) = isValue e1 && isValue e2
--unparse TmTrue = "true"
--unparse TmFalse = "false"
--unparse TmUnit = "()"
--unparse (TmPair e1 e2) = "( " ++ unparse e1 ++ " , " ++ unparse e2 ++ " )"
{-
-- Evaluation rules for projections
eval1 (TmFst e1,env,k,r,p) = (e1,env, FstH : k,r,p)
eval1 (TmSnd e1,env,k,r,p) = (e1,env, SndH : k,r,p)
eval1 (TmPair v w,env, FstH:k,r,p) | isValue v && isValue w = ( v , env , k,r,p)
eval1 (TmPair v w,env, SndH:k,r,p) | isValue v && isValue w = ( w , env , k,r,p)
-- Evaluation rules for if-then-else
eval1 (TmIf e1 e2 e3,env,k,r,p) = (e1,env,HIf e2 e3 env:k,r,p)
eval1 (TmTrue,env1,(HIf e2 e3 env2):k,r,p) = (e2,env2 ++ env1,k,r,p)
eval1 (TmFalse,env1,(HIf e2 e3 env2):k,r,p) = (e3,env2 ++ env1,k,r,p)
-- Evaluation rules for pairs
eval1 (TmPair e1 e2,env,k,r,p) = (e1,env,HPair e2 env:k,r,p)
eval1 (v,env1,(HPair e env2):k,r,p) | isValue v = (e,env2 ++ env1,PairH v : k,r,p)
eval1 (w,env,(PairH v):k,r,p) | isValue w = ( TmPair v w,env,k,r,p)
--eval1 (TmListSeg e1 e2,env,k,r,p) = (e2,env,HList e1 env:k,r,p)
--eval1 (TmString n,env1,(HList e env2):k,r,p) = (e,env2 ++ env1,ListH (TmString (rmQuo n)) : k,r,p)
--eval1 (TmString m,env,(ListH (TmString n)):k,r,p) = (TmString (n ++ "\n" ++ rmQuo m),env,k,r,p)

-}
