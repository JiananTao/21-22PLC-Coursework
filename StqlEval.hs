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
data StqlType = TyInt | TyString | TyBool | TyUnit | TyPair StqlType StqlType | TyFun StqlType StqlType
   deriving (Show,Eq)

type Environment = [ (String,Expr) ]

data Expr = TmInt Int | TmString String | TmTrue | TmFalse | TmUnit 
            | TmPair Expr Expr | TmAdd Expr Expr | TmVar String 
            | TmFst Expr | TmSnd Expr | TmAddString Expr Expr
            | TmIf Expr Expr Expr | TmLet String StqlType Expr
            | TmPrint Expr | TmPlusASort Expr Expr
            | TmGetVar String | TmReadEnv | TmFormat Expr
            | TmFillPrefix String | TmFillBase String | TmReady String
            | TmProcSemic String | TmProcComma String 
            | TmClear String StqlType | TmClearAll
            | TmEnd Expr Expr | TmEnd2 Expr
            | TmReadTTLFile String
    deriving (Show,Eq)

-}

data Frame =
           HAdd Expr Environment | AddH Expr
           | HPlus Expr Environment | PlusH Expr
--           | HPair Expr Environment | PairH Expr
--           | FstH | SndH 
           | Print | Format
           | List | HList Expr Environment | ListH Expr
--           | HIf Expr Expr Environment
           | Processing Expr | HLet String StqlType
type Kontinuation = [ Frame ]
type Result = [Expr]
type Processing = [Frame]
type State = (Expr,Environment,Kontinuation,Result,Processing)

{-这些与环境变量交互，以及是否有值可供输出有关
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

update :: Environment -> String -> Expr -> Environment
update env x e1 = (x,e1) : [ (y,e2) | (y,e2) <- env, x /= y ]
-- Checks for terminated expressions
isValue :: Expr -> Bool
isValue (TmString _) = True
isValue (TmInt _) = True
--isValue TmTrue = True
--isValue TmFalse = True
--isValue TmUnit = True
--isValue (TmPair e1 e2) = isValue e1 && isValue e2
isValue _ = False

whichExp :: Expr -> String
whichExp (TmString _) = "String"
whichExp (TmInt _) = "Int"
whichExp (TmVar _) = "Var"
whichExp _ = error ""

{-
--eval1是主要函数，用于模式匹配各个语法，并做出对应处理
--
--
-}
--Small step evaluation function
eval1 :: State -> State
-- Evaluation rules for plus and sort string
-- 只接受Var TmString相加
eval1 (TmPlusASort e1 e2,env,k,r,p) = (e1,env,HPlus e2 env:k,r,p)
eval1 (TmVar n,env1,(HPlus e env2):k,r,p) = (e,env2 ++ env1,PlusH e' : k,r,p)
                                         where e' = getValueBinding n env1
eval1 (TmVar m,env,(PlusH (TmString n)):k,r,p) = (TmString (toListSort (unparse e' ++ "\n" ++ n)),env,k,r,p)
                                         where e'  = getValueBinding m env

-- 获取变量
eval1 (TmVar x,env,k,r,p) = (e',env,k,r,p)
                    where e' = getValueBinding x env

-- Rule for terminated evaluations
--eval1 (v,env,[],r,[]) | isValue v = (v,env,[],v:r,[])
eval1 (v,env,[],r,[]) | isValue v = (v,env,[],r,[])
--eval1 (v,env,[],r,(Processing e):p) | isValue v = (e,env,[],v:r,p)
eval1 (v,env,[],r,(Processing e):p) | isValue v = (e,env,[],r,p)
eval1 (v,env,Print:k,r,p) | isValue v = (v,env,[],v:r,p)
--TODO:未考虑v不是value的情况
eval1 (v,env,Print:k,r,(Processing e):p) | isValue v = (e,env,[],v:r,p)

--
eval1 (v,env,List:k,r,p) | isValue v = (v,env,[],r,p)
-- Rule for Print
eval1 (TmPrint e,env,k,r,p) = (e,env,k ++ [Print] ,r,p)

-- Evaluation rules for End operator
eval1 (TmEnd2 e,env,k,r,p) = (e,env,k,r,p)
eval1 (TmEnd e1 e2,env,k,r,p) = (e2,env,k,r,Processing e1:p)

-- Evaluation rules for Let blocks
eval1 (TmLet x typ e,env,k,r,p) | isValue e = (e,update env x e,k,r,p)
eval1 (TmLet x typ e,env,k,r,p) = (e,env,(HLet x typ):k,r,p)
eval1 (v,env,(HLet x typ):k,r,p) | isValue v = (TmLet x typ v,env,k,r,p)


-- Evaluation rules for Clear blocks
eval1 (TmClear x typ,env,k,r,p) = (TmString ("clear " ++ x),clear env x,k,r,p)
eval1 (TmClearAll,env,k,r,p) = (TmString ("ClearAll excpet pre-load file"),clearAll env,k,r,p)

-- Rule for read file evaluations Read a pre-stored file string
eval1 (TmReadTTLFile s,env,k,r,p) = (TmVar (s),env,k,r,p)

-- Evaluation rules for plus number operator
eval1 (TmAdd e1 e2,env,k,r,p) = (e1,env,HAdd e2 env:k,r,p)
eval1 (TmInt n,env1,(HAdd e env2):k,r,p) = (e,env2 ++ env1,AddH (TmInt n) : k,r,p)
eval1 (TmInt m,env,(AddH (TmInt n)):k,r,p) = (TmInt (n + m),env,k,r,p)

-- Evaluation rules for plus string operator
eval1 (TmAddString e1 e2,env,k,r,p) = (e1,env,HPlus e2 env:k,r,p)
eval1 (TmString n,env1,(HPlus e env2):k,r,p) = (e,env2 ++ env1,PlusH (TmString (rmQuo n)) : k,r,p)
eval1 (TmString m,env,(PlusH (TmString n)):k,r,p) = (TmString (n ++ (rmQuo m)),env,k,r,p)

-- Evaluation rules for List operator
eval1 (TmList e,env,k,r,p) = (e,env,k ++ [List],r,p)
eval1 (TmListSeg e1 e2,env,k,r,p) = (e2,env,HList e1 env:k,r,p)
eval1 (TmString n,env1,(HList e env2):k,r,p) = (e,env2 ++ env1,ListH (TmString (rmQuo n)) : k,r,p)
eval1 (TmString m,env,(ListH (TmString n)):k,r,p) = (TmString (n ++ "\n" ++ rmQuo m),env,k,r,p)
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
-}




-- Evaluation rules for Let blocks
eval1 (TmGetVar s,env,k,r,p) = (TmString "已导入var",env',k,r,p)
                           where env' = getVarFromFile (varStr s env) env

eval1 (TmReadEnv, env,k,r,p) = (TmString (listEnv env),env,k,r,p)
-- Evaluation rules for Format Function blocks
eval1 (TmFormat e, env,k,r,p) = (e,env,Format:k,r,p)
eval1 (TmString s,env,Format:k,r,p) = (TmString s',env,k,r,p)
                           where s' = unlines $ formatResultF (socToList s)

eval1 (TmProcComma s, env,k,r,p) = (TmString s',env,k,r,p)
                           where s' = unlines ( procProcComma (getNeedProcComma (socToList (varStr s env)))
                                                ++ getNeedProcComma' (socToList (varStr s env)))
eval1 (TmProcSemic s, env,k,r,p) = (TmString s',env,k,r,p)
                           where s' = unlines ( procProcSemic (getNeedProcSemic (socToList (varStr s env)))
                                                ++ getNeedProcSemic' (socToList (varStr s env)))
eval1 (TmFillPrefix s, env,k,r,p) = (TmString s',env,k,r,p)
                           where s' = procFillPr (unlines (getNeedFillPr (socToList (varStr s env)))) env ""
eval1 (TmFillBase s, env,k,r,p) = (TmString s',env,k,r,p)
                           where s' = procFillBa (unlines (getNeedFillBa (socToList (varStr s env)))) env
eval1 (TmReady s, env,k,r,p) = (TmString s',env,k,r,p)
                           where s' = unlines (getNeedReady (socToList (varStr s env)))
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
                                     | otherwise   = error ""
                        
-- Evaluation rules for Compare blocks
eval1 (TmCompare s1 f1 s2 f2, env,k,r,p) = (TmString s', env,k,r,p)
                           where s' = pcCompare (rmQuo s1) (socToList (varStr f1 env)) (rmQuo s2) (socToList (varStr f2 env))
-- Evaluation rules for LiteralsNum blocks
eval1 (TmLiteralsNum s, env,k,r,p) = (TmString s', env,k,r,p)
                           where s' = pcLiteralsNum (socToList (varStr s env))

-- Rule for runtime errors
eval1 (e,env,k,r,p) = error "Unknown Evaluation Error"



{-------------------------------------------------------------------------------------------
--*必须提前运行GetVars函数，将文件中的参数填入
--这些是为了获得填充ttl文件不全的方法
--
--
-}
pcDelimit :: Int -> String -> [String] -> String
pcDelimit i s l | "\n" `isInfixOf` s = unlines $ nub [ r | r <- l , r' <- wordsWhen (=='\n') s, r' `isInfixOf` r]
                | otherwise = unlines [ rr | (r1,r2,r3,rr) <- splitTriples l , case i of 
                                                                                  1 -> s `isInfixOf` r1
                                                                                  2 -> s `isInfixOf` r2
                                                                                  3 -> s `isInfixOf` r3]
{-
--适用于Delimit "Subj"函数
pcDefineSubj :: String -> [String] -> String
pcDefineSubj subj s | "\n" `isInfixOf` subj = unlines $ nub [ r | r <- s , r' <- wordsWhen (=='\n') subj, r' `isInfixOf` r]
                    | otherwise = unlines [ rr | (r1,r2,r3,rr) <- splitTriples s , subj `isInfixOf` r1]
--适用于Delimit "Pred"函数
pcDefinePred :: String -> [String] -> String
pcDefinePred pred s | "\n" `isInfixOf` pred = unlines $ nub [ r | r <- s , r' <- wordsWhen (=='\n') pred, r' `isInfixOf` r]
                    | otherwise = unlines [ rr | (r1,r2,r3,rr) <- splitTriples s , pred `isInfixOf` r2]
--适用于Delimit "Obj"函数
pcDefineObj :: String -> [String] -> String
pcDefineObj obj s | "\n" `isInfixOf` obj = unlines $ nub [ r | r <- s , r' <- wordsWhen (=='\n') obj, r' `isInfixOf` r]
                  | otherwise = unlines [ rr | (r1,r2,r3,rr) <- splitTriples s , obj `isInfixOf` r3]
-}
--适用于Compare函数
--因为已经验证过了有3个，所以！！不会抛出错误
pcCompare :: String -> [String] -> String -> [String] -> String
pcCompare s1 f1 s2 f2 | s1 == "Obj" && s2 == "Subj" = unlines $ nub $ [r1 |
                                                      r1 <- f1, length (filter (== '<') r1) == 3,
                                                      r2 <- f2, length (filter (== '<') r2) == 3,
                                                      wordsWhen (== '>') r1 !! 2 == head (wordsWhen (== '>') r2)]
                      | otherwise = "暂未匹配此功能"
--适用于LiteralsNum函数
pcLiteralsNum :: [String] -> String
pcLiteralsNum s = (unlines $ sort $ [ r'' |
                  (r1,r2,r3,r') <- splitTriples s, ifHasDigit r3,
                  readInt r3 < 0 || readInt r3 > 99,
                  let r'' = r1 ++ " <http://www.cw.org/problem5/#inRange> false ."
                  ]) ++ (
                  unlines $ sort $ [ r'' |
                  (r1,r2,r3,r') <- splitTriples s, ifHasDigit r3,
                  readInt r3 >= 0 && readInt r3 <= 99,
                  let r'' = r1 ++ r2 ++ show (readInt r3 + 1) ++ "\n" ++ r1 ++ " <http://www.cw.org/problem5/#inRange> true ."
                  ])
--适用于Format函数，用于去除空格，格式化结尾，以及去除重复
--还有判断结尾是否语义重复
-- *除了50，20，10外其他数字有未知bug，可能是空格不对
--fromResult会返回完美格式的结果，fromResult‘是对语义相同项的处理
--   .
formatResultF :: [String] -> [String]
formatResultF l = sort $ nub $ [ r' | r <- formatResult' (formatResult l),
                        let r' = replace "  " " " r]
formatResult :: [String] -> [String]
formatResult l = nub [ s'' | s <- l, let s' = replace ". " "" (filter (/=' ') s ++ "  ."),
                                     let s'' = replace "  " " " $ reverse (replaceFirst  '>' " >" (reverse s'))]

formatResult' :: [String] -> [String]
formatResult' l =  sort $ [ r' | (r1,r2,r3,rr) <- splitTriples l, ifAllDigit r3, let r' = r1 ++ r2 ++ " " ++ show (readInt r3) ++ " ."] 
                   ++ [ rr | (r1,r2,r3,rr) <- splitTriples l, not $ ifAllDigit r3]
--formatResult' l =  sort $ [ r' | (r1,r2,r3,rr) <- splitTriples l, ifAllDigit r3, let r' = r1 ++ r2 ++ show (readInt r3)] ++ [ rr | (r1,r2,r3,rr) <- splitTriples l, not $ ifAllDigit r3]



--可优化
--适用于ProcComma函数，会处理例: <testSubA> <testObjList> -5 , 10 , 20 .
getNeedProcComma :: [String] -> [String]
getNeedProcComma l = [ s | s <- l, isInfixOf "," s]
getNeedProcComma' :: [String] -> [String]
getNeedProcComma' l = [ s | s <- l, not ( isInfixOf "," s)]
procProcComma :: [String] -> [String]
procProcComma l = concat $ procProcComma' [ (s1,s2) | s <- l, let s' = s \\ " ", let s1 = fst $ break isSpace s', let s2 = snd $ break isSpace s']
procProcComma' :: [(String,String)] -> [[String]]
procProcComma' l = [ s | (s1,s2) <- l, let s = map (s1++) (split "," s2)]
--适用于ProcSemic函数, 会处理例: <testSubA> <testPredList> -5 ; <testPredList> 10 ; <testPredList> 20 .
getNeedProcSemic :: [String] -> [String]
getNeedProcSemic l = [ s | s <- l, isInfixOf ";" s]
getNeedProcSemic' :: [String] -> [String]
getNeedProcSemic' l = [ s | s <- l, not ( isInfixOf ";" s)]
procProcSemic :: [String] -> [String]
procProcSemic l = concat $ procProcSemic' [ (s1,s2) | s <- l, let s1 = fst $ break isSpace s, let s2 = snd $ break isSpace s]
procProcSemic' :: [(String,String)] -> [[String]]
procProcSemic' l = [ s | (s1,s2) <- l, let s = map (s1++) (split ";" s2)]

--适用于Ready函数, 例: <http://www.cw.org/subjectA> <http://www.cw.org/predicateA> <http://www.cw.org/objectA> . 
getNeedReady :: [String] -> [String]
getNeedReady l = [ s | s <- l, length (split "http://" s) == 4]
--适用于FillBase函数, 例: <prob4B> <testPredA> <prob4C> .
--例: <http://www.cw.org/#problem2> <testPredA> true .
getNeedFillBa :: [String] -> [String]
getNeedFillBa l = [ s | s <- l, (length (split "http://" s) <= 2) && (isInfixOf ">") s && (not ("/>" `isInfixOf` s))]
procFillBa :: String -> Environment -> String
procFillBa s env = filter (/=' ') (procFillBa' s env)
procFillBa' :: String -> Environment -> String
procFillBa' s env = concat [ r' | r <- split "<" s, let r' = case isInfixOf "http://" r of
                                                                     True  -> "<" ++ r
                                                                     _     -> case not (isInfixOf "http://" r) && (isInfixOf ">" r) of
                                                                         True -> (varStr "BaseVar" env \\ ">") ++ r
                                                                         False -> r]

--适用于FillPrefix函数, 例: p:subjectC
--s 为一整个文件的字符串, 通过在
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
--这里是将TTL输出文件合并排序的函数
--
--
-}
toListSort :: String -> String
toListSort s = unlines (sort (split "\n" s))

{-------------------------------------------------------------------------------------------
--这些是为了获得文件里变量的方法
--适用于GetVars函数
--
--
--}
getVarFromFile :: String -> Environment -> Environment
getVarFromFile s env = env ++ varBase (socToList s) ++ varPrefix (socToList s) ++ varPrefixBroken (socToList s)
--TODO：此处未检测是否为空,即默认输入的ttl有@base
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
--这些是部分简单语法用到的函数
--
--
-}
rmLast :: Eq a => [a] -> [a] -> [a]
rmLast s x = reverse $ reverse s \\ x
--用于ReadEnv语法
--TODO：只能检测字符串，其他格式抛出错误
listEnv :: Environment -> String
listEnv env = unlines [ s ++ "是" ++ unparse e | (s,e) <- env, s /= "foo.ttl" && s /= "bar.ttl"]
--用于Clear语法
clear :: Environment -> String -> Environment
clear env x = [ (y,e2) | (y,e2) <- env, x /= y ]
--用于ClearAll语法
clearAll :: Environment -> Environment
clearAll env = [ (y,e2) | (y,e2) <- env, y == "foo.ttl" || y == "bar.ttl" ]

{-------------------------------------------------------------------------------------------
--tools and check function
--这些是用的通用小函数
--
--
-}
splitTriples :: [String] -> [(String,String,String,String)]
splitTriples l = [ (r1,r2,r3,r') | s <- l, let s' = filter (/=' ') s,
                                         let i3 = rmMaybe (elemIndex '>' (reverse s')),
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
ifAllDigit s = not (null ([ r | r <- s])) && (length [ r | r <- s]) == length ([ r | r <- s, isDigit r || (r == '+') || (r == '-')])
--TODO:bug不能用filter
readInt :: String -> Int
readInt s | eqString s "+" = read (tail s)
          | eqString s "-" = negate (read (tail s))
          | otherwise      = read s
          where s' = filter (==' ') s
rmMaybe :: Maybe a -> a
rmMaybe (Just a) = a
rmMaybe Nothing = error "强制去除Maybe错误"
varStr :: String -> Environment -> String
varStr s env = unparse (getValueBinding (s \\ ['\"','\"']) env)

--TODO: 去除2个“符号,防止引入的String带有“

--将String转为List
socToList :: String -> [String]
socToList = wordsWhen (=='\n')
--例:print $ wordsWhen (=='.') "get.ttl.split"
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
--例:eqString "@base <http://www.cw.org/> ." "@base"
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
--这些是函数主程序
--负责与Stql.hs中的main方法对接
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
unparse (TmString n) =  n
unparse (TmInt n) = show n
--unparse TmTrue = "true"
--unparse TmFalse = "false"
--unparse TmUnit = "()"
--unparse (TmPair e1 e2) = "( " ++ unparse e1 ++ " , " ++ unparse e2 ++ " )"
unparse _ = "Unknown"
unparseAll :: [Expr] -> [String]
unparseAll = map unparse