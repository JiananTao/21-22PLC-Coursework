-- Author: Julian Rathke, 2018
-- Provides a CEK implementation of the \Stql language from the lecture notes
module StqlEval where
import StqlGrammar
{-
data StqlType = TyInt | TyString | TyBool | TyUnit | TyPair StqlType StqlType | TyFun StqlType StqlType
   deriving (Show,Eq)

type Environment = [ (String,Expr) ]

data Expr = TmInt Int | TmString String | TmTrue | TmFalse | TmUnit 
            | TmPair Expr Expr | TmAdd Expr Expr | TmVar String 
            | TmFst Expr | TmSnd Expr | TmAddString Expr Expr
            | TmIf Expr Expr Expr | TmLet String StqlType Expr Expr
            | TmLambda String StqlType Expr | TmApp Expr Expr 
            | TmEnd Expr Expr | TmEnd2 Expr
            | Cl String StqlType Expr Environment
    deriving (Show,Eq)
-}

data Frame =
           HAdd Expr Environment | AddH Expr 
           | HPlus Expr Environment | PlusH Expr
           | HPair Expr Environment | PairH Expr
           | FstH | SndH
           | HIf Expr Expr Environment | HLet String StqlType Expr Environment
           | HApp Expr Environment | AppH Expr
           | Processing Expr
type Kontinuation = [ Frame ]
type Result = [Expr]
type Processing = [Frame]
type State = (Expr,Environment,Kontinuation,Result,Processing)

-- Function to unpack a closure to extract the underlying lambda term and environment
unpack :: Expr -> (Expr,Environment)
unpack (Cl x t e env1) = (TmLambda x t e , env1)
unpack e = (e,[])

-- Look up a value in an environment and unpack it
getValueBinding :: String -> Environment -> (Expr,Environment)
getValueBinding x [] = error "Variable binding not found"
getValueBinding x ((y,e):env) | x == y  = unpack e
                              | otherwise = getValueBinding x env

update :: Environment -> String -> Expr -> Environment
update env x e = (x,e) : env

-- Checks for terminated expressions
isValue :: Expr -> Bool
isValue (TmString _) = True 
isValue (TmInt _) = True
isValue TmTrue = True
isValue TmFalse = True
isValue TmUnit = True
isValue (TmPair e1 e2) = isValue e1 && isValue e2
isValue (Cl {}) = True
isValue _ = False


--Small step evaluation function
eval1 :: State -> State
eval1 (TmVar x,env,k,r,p) = (e',env',k,r,p)
                    where (e',env') = getValueBinding x env

-- Rule for terminated evaluations
eval1 (v,env,[],r,[]) | isValue v = (v,env,[],v:r,[])
eval1 (v,env,[],r,(Processing e):p) | isValue v = (e,env,[],v:r,p) 

-- Evaluation rules for End operator
eval1 (TmEnd2 e,env,k,r,p) = (e,env,k,r,p)
eval1 (TmEnd e1 e2,env,k,r,p) = (e1,env,k,r,Processing e2:p)

-- Evaluation rules for plus number operator
eval1 (TmAdd e1 e2,env,k,r,p) = (e1,env,HAdd e2 env:k,r,p)
eval1 (TmInt n,env1,(HAdd e env2):k,r,p) = (e,env2,AddH (TmInt n) : k,r,p)
eval1 (TmInt m,env,(AddH (TmInt n)):k,r,p) = (TmInt (n + m),[],k,r,p)

-- Evaluation rules for plus string operator
eval1 (TmAddString e1 e2,env,k,r,p) = (e1,env,HPlus e2 env:k,r,p)
eval1 (TmString n,env1,(HPlus e env2):k,r,p) = (e,env2,PlusH (TmString n) : k,r,p)
eval1 (TmString m,env,(PlusH (TmString n)):k,r,p) = (TmString (n ++ m),[],k,r,p)

-- Evaluation rules for projections
eval1 (TmFst e1,env,k,r,p) = (e1,env, FstH : k,r,p)
eval1 (TmSnd e1,env,k,r,p) = (e1,env, SndH : k,r,p)
eval1 (TmPair v w,env, FstH:k,r,p) | isValue v && isValue w = ( v , [] , k,r,p)
eval1 (TmPair v w,env, SndH:k,r,p) | isValue v && isValue w = ( w , [] , k,r,p)

-- Evaluation rules for pairs
eval1 (TmPair e1 e2,env,k,r,p) = (e1,env,HPair e2 env:k,r,p)
eval1 (v,env1,(HPair e env2):k,r,p) | isValue v = (e,env2,PairH v : k,r,p)
eval1 (w,env,(PairH v):k,r,p) | isValue w = ( TmPair v w,[],k,r,p)

-- Evaluation rules for if-then-else
eval1 (TmIf e1 e2 e3,env,k,r,p) = (e1,env,HIf e2 e3 env:k,r,p)
eval1 (TmTrue,env1,(HIf e2 e3 env2):k,r,p) = (e2,env2,k,r,p)
eval1 (TmFalse,env1,(HIf e2 e3 env2):k,r,p) = (e3,env2,k,r,p)

-- Evaluation rules for Let blocks
eval1 (TmLet x typ e1 e2,env,k,r,p) = (e1,env,HLet x typ e2 env:k,r,p)
eval1 (v,env1,(HLet x typ e env2):k,r,p) | isValue v = (e, update env2 x v , k,r,p)

--  Rule to make closures from lambda abstractions.
eval1 (TmLambda x typ e,env,k,r,p) = (Cl x typ e env, [], k,r,p)

-- Evaluation rules for application
eval1 (TmApp e1 e2,env,k,r,p) = (e1,env, HApp e2 env : k,r,p)
eval1 (v,env1,(HApp e env2):k ,r,p) | isValue v = (e, env2, AppH v : k,r,p)
eval1 (v,env1,(AppH (Cl x typ e env2) ) : k ,r,p)  = (e, update env2 x v, k,r,p)

-- Rule for runtime errors
eval1 (e,env,k,r,p) = error "Evaluation Error"

-- Function to iterate the small step reduction to termination
{-
evalLoop :: Expr -> Expr 
evalLoop e = evalLoop' (e,[],[])
  where evalLoop' (e,env,k) = if (e' == e) && (isValue e') && (null k) then e' else evalLoop' (e',env',k')
                       where (e',env',k') = eval1 (e,env,k) 
-}

evalLoop :: Expr -> [Expr]
evalLoop e = eval (e,[],[],[],[])

eval :: (Expr, Environment, Kontinuation, Result, Processing) -> [Expr]
eval (e,env,k,r,p) | e' == e && isValue e' && null k && null p  = r'
                   | otherwise                                  = eval (e',env',k',r',p')
            where (e',env',k',r',p') = eval1 (e,env,k,r,p)

-- Function to unparse underlying values from the AST term
unparse :: Expr -> String
unparse (TmString n) = n
unparse (TmInt n) = show n
unparse TmTrue = "true"
unparse TmFalse = "false"
unparse TmUnit = "()"
unparse (TmPair e1 e2) = "( " ++ unparse e1 ++ " , " ++ unparse e2 ++ " )"
unparse (Cl {}) = "Function Value"
unparse _ = "Unknown"

getResult :: [Expr] -> [String]
getResult r = map unparse r
