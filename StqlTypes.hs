module StqlTypes where
import StqlGrammar

import Data.Typeable

type TypeEnvironment = [ (String, StqlType) ]

getBinding :: String -> TypeEnvironment -> StqlType
getBinding x [] = error "Variable binding not found"
getBinding x ((s,t):tenv) | x == s = t
                          | otherwise = getBinding x tenv

addBinding :: String -> StqlType -> TypeEnvironment -> TypeEnvironment
addBinding x t tenv = (x,t):tenv

typeOfStr :: TypeEnvironment -> Str -> StqlType
typeOfStr tenv (TsListSeg e1 e2) | not (isString e1) = error "ListSeg only seg [string | .. | string]2"
                                 | otherwise = typeOfStr tenv e2
typeOfStr tenv (TsString e) = TyString

typeOf' :: TypeEnvironment -> Expr -> StqlType
typeOf' tenv (TmInt _) = TyInt 

typeOf' tenv (TmString _) = TyString

typeOf' tenv (TmVar x) = getBinding x tenv

typeOf' tenv (TmList e1 e2) | not (isString e1) = error "ListSeg only seg [string | .. | string]1"
                            | otherwise = typeOfStr tenv e2 


typeOf' tenv (TmAdd e1 e2) | (TyInt,TyInt) == (typeOf' tenv e1, typeOf' tenv e2) = TyInt
                           | otherwise = error ("  Error in Token '+' \n" ++ "  Expr + Expr, where the final result only contains Integer \n")

typeOf' tenv (TmAddString e1 e2) | (TyString, TyString) == (typeOf' tenv e1, typeOf' tenv e2) = TyString
{-
typeOf tenv (TmLet x t e) | t == t1 = typeOf (addBinding x t tenv) e
    where t1 = typeOf tenv e
-}
typeOf' _ _ = error "Type Error"
{-
--some small function to help recognize type
--
isTurtle :: Expr -> Bool
isTurtle e
        | typeOf == 

isList :: Expr -> Bool
isList e
    | (isList e) == TmInt || TmString = True
    | otherwise = False
-}
isString :: (Typeable a) => a -> Bool
isString n = typeOf n == typeOf "a"

-- Function for printing the results of the TypeCheck
unparseType :: StqlType  -> String
unparseType TyInt = "Int"
unparseType TyString = "String"
unparseType _ = error "Unknown Type"