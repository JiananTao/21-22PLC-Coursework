module StqlTypes where
import StqlGrammar

import Data.Typeable
import Data.List
type TypeEnvironment = [ (String, StqlType) ]
data Frame =
           HAdd Expr | Int
           | HPlus Expr | String 
           | HPlusVar Expr | Delimit |HMinusVar Expr
           | FillBasePrefixReady | ProcSemicComma
           | Print | Format | List 
           | Processing Expr | HLet String StqlType
type Kontinuation = [ Frame ]
type Processing = [Frame]
type TypeState = (Processing,Kontinuation,TypeEnvironment,Expr)

getBinding :: String -> TypeEnvironment -> StqlType
getBinding x [] = error "Variable binding not found"
getBinding x ((s,t):tenv) | x == s = t
                          | otherwise = getBinding x tenv

addBinding :: String -> StqlType -> TypeEnvironment -> TypeEnvironment
addBinding x t tenv = (x,t):tenv

clearBinding :: String -> TypeEnvironment -> TypeEnvironment
clearBinding x [] = error "Variable binding not found"
clearBinding x tenv = [ (s,t) | (s,t) <- tenv, s /= x]

isValue :: Expr -> Bool
isValue (TmString _) = True
isValue (TmInt _) = True
isValue (TmVar _) = True
isValue _ = False

typeOfStr ::  Str -> Expr
typeOfStr (TsListSeg e1 e2) | not (isString e1) = error ("  Error in Tokens  '[' '|' ']' \n" ++ 
                                              "  ListSeg only seg [string | .. | string]\n")
                            | otherwise = typeOfStr e2
typeOfStr (TsString e) = TmString "Correct"


typeOf' :: TypeState -> TypeState

-- Exp: int
typeOf' ([],[],tenv, e@(TmInt _)) = ([],[],tenv,e)
typeOf' ((Processing e):p,[],tenv, (TmInt _)) = (p,[],tenv,e)
-- Exp: string
typeOf' ([],[],tenv, e@(TmString _)) = ([],[],tenv,e)
typeOf' ((Processing e):p,[],tenv, (TmString _)) = (p,[],tenv,e)
-- Exp: [ | ]
typeOf' (p,k,tenv, (TmList e1 e2)) | not (isString e1) = error ("  Error in Tokens '[' '|' ']' \n" ++ 
                                              "  ListSeg only seg [string | .. | string]\n")
                                   | otherwise = (p,k,tenv, typeOfStr e2) 

--Exp: ++
typeOf' (p,k,tenv, (TmAddString e1 e2)) = (p,HPlus e2:k,tenv,e1)

--Exp: PlusVar
typeOf' (p,k,tenv, (TmPlusVar e1 e2)) = (p,HPlusVar e2:k,tenv,e1)
typeOf' (p,(HPlusVar e):k,tenv, TmVar x ) = (p,(typeToK (getBinding x tenv)):k,tenv,e)
typeOf' (p,(HPlusVar e):k,tenv, _ ) = error ("  Error in Token 'PlusVar' \n" ++
                                                 "  Expr 'PlusVar' Expr,  \n")

--Exp: MinusVar
typeOf' (p, k, tenv, (TmMinusVar e1 e2)) = (p, HMinusVar e2:k, tenv, e1)
typeOf' (p, (HMinusVar e): k,tenv, TmVar x ) = (p,(typeToK (getBinding x tenv)):k,tenv,e)
typeOf' (p, (HMinusVar e): k,tenv, _ ) = error ("Error in Token 'MinusVar' \n" ++
                                                 " Expr 'MinusVar' Expr, \n")

--Exp: var
typeOf' (p,k,tenv, (TmVar x)) = (p,k,tenv,getExpr(getBinding x tenv))
                            
--Exp: +
typeOf' (p,k,tenv, (TmAdd e1 e2)) = (p,HAdd e2:k,tenv,e1)
typeOf' (p,(HAdd e):k,tenv,TmInt _ ) = (p,Int:k,tenv,e)
typeOf' (p,(HAdd e):k,tenv, _ ) = error ("  Error in Token '+' \n" ++
                                                 "  Expr '+' Expr,  \n")
--Exp: int
typeOf' (p,Int:k,tenv,TmString _) = error "  token '+' only accept Int type\n"

--Exp: string
typeOf' (p,String:k,tenv,TmInt _) = error "  token '++' only accept String type\n"
typeOf' ( p, String:k, tenv, e) = ( p, k, tenv, e)
typeOf' ( p, Int:k, tenv, e) = ( p, k, tenv, e)
--Exp: Let
typeOf' (p,k,tenv, (TmLet x t e)) = (p,(HLet x t):k,tenv, e)
      
--Exp: Clear (used to test our program, avoid the memory overflow)
typeOf' (p,k,tenv, TmClear x t) | getBinding x tenv == TyInt || getBinding x tenv == TyString = (p,k,clearBinding x tenv, TmString "Clear")
                                | otherwise = error "Unknown error in Clear Function"
 
--Exp: ClearAll (used to test our program, avoid the memory overflow)
typeOf' (p,k,tenv, TmClearAll) =  (p,k,tenv, TmString "Clear All")

--Exp: ';'
--typeOf' (p,k,tenv,TmEnd2 e) = (p,k,tenv,e)
typeOf' (p,k,tenv,TmEnd e1 e2) = (Processing e1:p,k,tenv,e2)

--Exp: Print
typeOf' (p,k,tenv,TmPrint e) = (p,k,tenv,e)
--Exp: ReadFile
typeOf' (p,k,tenv,TmReadTTLFile s) | (isString s) && (isInfixOf ".ttl" s) = (p,k,tenv,TmString "read file")
                                   | isString s = error ("  Error in Tokens 'ReadFile' '*.ttl' \n" ++ "  must be a *.ttl File")
                                   | otherwise  = error "  Error in Tokens 'ReadFile' '*.ttl'"
--Exp: GetVars (get the variables(label in turtle file) and store them in Environemnt )
typeOf' (p,k,tenv,TmGetVar s) | isVar s = (p,k,tenv,TmString "get Var")
                              | otherwise  = error "  Error in Token 'GetVars'"

--Exp: ReadEnv (using to test the existence of variables, might useful in the later problem)
typeOf' (p,k,tenv,TmReadEnv) = (p,k,tenv,TmString "functional function")

      
--Exp: Format (make our program as perfect output)
typeOf' (p,k,tenv,TmFormat e) = (p,Format:k,tenv,e)

--TODO:
--typeOf' (p,k,tenv,TmFillBasePrefixReady (TmVar x)) = (p,k,tenv,(getBinding x tenv))
typeOf' (p,k,tenv,TmFillBasePrefixReady e) | isVar e = (p,FillBasePrefixReady:k,tenv,TmString "")
                                           | otherwise = error ("  Error in Token FillBasePrefixReady\n" ++ "  FillBasePrefixReady only address String")
--Exp: ProcSemicComma
typeOf' (p,k,tenv,TmProcSemicComma e) | isVar e = (p,ProcSemicComma:k,tenv,TmString "")
                                      | otherwise  = error ("  Error in Token ProcSemicComma\n" ++ "  ProcSemicComma only address String")
--Exp: Delimit
typeOf' (p,k,tenv,TmDelimit s1 e s2) | not (isString s1) || not (isVar s2) = error ("  Error in Token Delimit\n" ++ "  Delimit")
                                     | otherwise = (p,Delimit:k,tenv,e)
--Exp: Compare
typeOf' (p,k,tenv,TmCompare s1 v1 s2 v2) | not (isString s1 || isString s2) = error ("  Error in Token Compare\n" ++ "  Compare only handle String")
                                         | getBinding v1 tenv == getBinding v2 tenv =  (p,k,tenv,TmString"Compare")
--Exp: LiteralsNum
typeOf' (p,k,tenv,TmLiteralsNum s) | not (isVar s) = error ("  Error in Token LiteralsNum\n" ++ "  LiteralsNum")
                                   | otherwise = (p,k,tenv,TmString "LiteralsNum")

--Exp: ProcObj
typeOf' (p,k,tenv,TmProcObj s1 s2 s3 s4 v1 v2 ) | not (isString s1 || isString s2 || isString s3 || isString s4) = error ("  Error in Token ProcObj\n" ++ "  ProcObj only handle String")
                                         | getBinding v1 tenv == getBinding v2 tenv =  (p,k,tenv,TmString"ProcObj")

--something must be in back
typeOf' (p,Delimit:k,tenv,e) | getType e == TyString = (p,k,tenv,e)
                             | otherwise = error ("  Error in Token Delimit\n" ++ "  Delimit olny handle variables bound to type String")
typeOf' (p,Format:k,tenv,s) | getType s  == TyString = (p,k,tenv,s)
                            | otherwise             = error ("  Error in Token Format\n" ++ "  Format can olny handle variables bound to type String")
typeOf' (p,FillBasePrefixReady:k,tenv,s) | getType s == TyString = (p,k,tenv,s)
                                         | otherwise             = error ("  Error in Token FillBasePrefixReady\n" ++ "  FillBasePrefixReady only handle String")

typeOf' (p,ProcSemicComma:k,tenv,s) | getType s == TyString = (p,k,tenv,s)
                                    | otherwise             = error ("  Error in Token ProcSemicComma\n" ++ "  ProcSemicComma only handle String")
typeOf' (p,(HLet x t):k,tenv, v) | isValue v && (getType v) == t = (p,k,addBinding x t tenv,v)
                                 | otherwise = error ("  Error in Tokens 'Let' 'In' \n" ++
                                                 "  Let '(' var ':' Type ')' '=' Expr ,  \n")
typeOf' (p,(HPlus e):k,tenv,TmString _ ) = (p,String:k,tenv,e)
typeOf' (p,(HPlus e):k,tenv, _ ) = error ("  Error in Token '++' \n" ++
                                                       "  Expr '++' Expr,  \n")
                                    
typeOf' ( _, _, _, _) = error "Type Error"
{-
--helper function to recognize type
--
-}
isVar :: String -> Bool
isVar n | (isString n) && (not (isInfixOf "\"" n)) = True
        | otherwise = False
isString :: (Typeable a) => a -> Bool
isString n = typeOf n == typeOf "a"

getExpr :: StqlType -> Expr
getExpr TyString = TmString ""
getExpr TyInt = TmInt 0
getType :: Expr -> StqlType
getType (TmString _) = TyString
getType (TmInt _ ) = TyInt

typeToK :: StqlType -> Frame
typeToK TyString = String
typeToK TyInt = Int



typeLoop :: TypeState -> String
typeLoop (p,k,tenv, TmEnd2 e) | e == e' && null p  = "All type correct"
                              | otherwise          = typeLoop (p',k',tenv',TmEnd2 e')
            where (p',k',tenv',e') = typeOf' (p,k,tenv,e)
typeLoop (p,k,tenv, _) = error "  each line must have‘;’as terminated symbol"
-- Function for printing the results of the TypeCheck
{-
unparseType :: StqlType  -> String
unparseType TyInt = "Int"
unparseType TyString = "String"
unparseAllType :: [StqlType]  -> [String]
unparseAllType = map unparseType
-}