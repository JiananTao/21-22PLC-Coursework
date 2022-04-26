module StqlTypes where
import StqlGrammar

import Data.Typeable

type TypeEnvironment = [ (String, StqlType) ]
data Frame =
           HAdd Expr | Int
           | HPlus Expr | String 
           | Print | Format | List 
           | Processing Expr | HLet String StqlType
type Kontinuation = [ Frame ]
type Result = [ StqlType ]
type Processing = [Frame]
type TypeState = (Result,Processing,Kontinuation,TypeEnvironment,Expr)
getBinding :: String -> TypeEnvironment -> StqlType
getBinding x [] = error "Variable binding not found"
getBinding x ((s,t):tenv) | x == s = t
                          | otherwise = getBinding x tenv

addBinding :: String -> StqlType -> TypeEnvironment -> TypeEnvironment
addBinding x t tenv = (x,t):tenv

typeOfStr ::  Str -> Expr
typeOfStr (TsListSeg e1 e2) | not (isString e1) = error ("  Error in Tokens  '[' '|' ']' \n" ++ 
                                              "  ListSeg only seg [string | .. | string]\n")
                            | otherwise = typeOfStr e2
typeOfStr (TsString e) = TmString "Correct"


typeOf' :: TypeState -> TypeState
typeOf' (r,p,k,tenv,TmEnd2 e) = (r,p,k,tenv,e)
typeOf' (r,p,k,tenv,TmEnd e1 e2) = (r,Processing e1:p,k,tenv,e2)

-- Exp: int
typeOf' (r,[],[],tenv, e@(TmInt _)) = (TyInt:r,[],[],tenv,e)
typeOf' (r,(Processing e):p,[],tenv, (TmInt _)) = (TyInt:r,p,[],tenv,e)
-- Exp: string
typeOf' (r,[],[],tenv, e@(TmString _)) = (TyString:r,[],[],tenv,e)
typeOf' (r,(Processing e):p,[],tenv, (TmString _)) = (TyString:r,p,[],tenv,e)
-- Exp: var 
typeOf' (r,[],[],tenv, e@(TmVar x)) = ((getBinding x tenv):r,[],[],tenv,e)
typeOf' (r,(Processing e):p,[],tenv, (TmVar x)) = ((getBinding x tenv):r,p,[],tenv,e)

typeOf' (r,p,k,tenv, (TmList e1 e2)) | not (isString e1) = error ("  Error in Tokens '[' '|' ']' \n" ++ 
                                              "  ListSeg only seg [string | .. | string]\n")
                                     | otherwise = (r,p,k,tenv, typeOfStr e2) 


typeOf' (r,p,k,tenv, (TmAddString e1 e2)) = (r,p,HPlus e2:k,tenv,e1)
typeOf' (r,p,(HPlus e):k,tenv,TmString _ ) = (r,p,String:k,tenv,e)
typeOf' (r,p,(HPlus e):k,tenv, _ ) = error ("  Error in Token '++' \n" ++
                                                       "  Expr '++' Expr,  \n")
typeOf' (r,p,String:k,tenv,e@(TmInt _)) = error "  token '++' 不可连接String和Int,也可能是其他token\n"
{-
typeOf' (r,p,k,tenv, (TmPlusVar e1 e2)) | typeOf' k,tenv e1 == typeOf' k,tenv e2 = typeOf' k,tenv e1
                                        | otherwise = error ("  Error in Token 'PlusVar' \n" ++
                                                 "  Expr 'PlusVar' Expr,  \n")
eval1 (TmPlusVar e1 e2,env,k,r,p) = (e1,env,HPlus e2 env:k,r,p)
eval1 (TmVar n,env1,(HPlus e env2):k,r,p) = if whichExp e' == "String" then (e,env2 ++ env1,PlusH e' : k,r,p) else error "PlusVar only accept String in Var now"
                                         where e' = getValueBinding n env1
eval1 (TmVar m,env,(PlusH (TmString n)):k,r,p) = (TmString (toListSort (unparse e' ++ "\n" ++ n)),env,k,r,p)
                                         where e'  = getValueBinding m env
-}

typeOf' (r,p,k,tenv, (TmAdd e1 e2)) = (r,p,HAdd e2:k,tenv,e1)
typeOf' (r,p,(HAdd e):k,tenv,TmInt _ ) = (r,p,Int:k,tenv,e)
typeOf' (r,p,(HAdd e):k,tenv, _ ) = error ("  Error in Token '+' \n" ++
                                                 "  Expr '+' Expr,  \n")
typeOf' (r,p,Int:k,tenv,e@(TmString _)) = error "  token '+' 不可连接Int和String,也可能是其他token\n"
{-
typeOf' (r,p,k,tenv, (TmLet x t e)) | typeOf' k,tenv e == t = typeOf' (addBinding x t k,tenv) e
                               | otherwise = error ("  Error in Tokens 'Let' 'In' \n" ++
                                                 "  Let '(' var ':' Type ')' '=' Exp ,  \n")
--这里比较特殊，因为这里如果没有可消除的绑定变量，会自动在取出getValueBinding的error进行报错
typeOf' (r,p,k,tenv, (TmClear x t)) = getValueBinding x t
--这里tyoeCheck不可能报错
typeOf' (r,p,k,tenv, TmClearAll) = TyString

--typeOf' k,tenv (TmEnd e1 e2) r 
-}
typeOf' (r, p, String:k, tenv, e) = (r, p, k, tenv, e)
typeOf' (r, p, Int:k, tenv, e) = (r, p, k, tenv, e)
typeOf' (_, _, _, _, _) = error "Type Error"
{-
--some small function to help recognize type
--
-}
isString :: (Typeable a) => a -> Bool
isString n = typeOf n == typeOf "a"
getFifth (a,b,c,d,e) = e
typeLoop :: TypeState -> [ StqlType ]
typeLoop (r,p,k,tenv, e) | e == e' && null p    = r'
                         | otherwise            = typeLoop (r',p',k',tenv',e')
            where (r',p',k',tenv',e') = typeOf' (r,p,k,tenv,e)




-- Function for printing the results of the TypeCheck
unparseType :: StqlType  -> String
unparseType TyInt = "Int"
unparseType TyString = "String"
unparseAllType :: [StqlType]  -> [String]
unparseAllType = map unparseType