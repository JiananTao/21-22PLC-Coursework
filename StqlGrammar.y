{ 
module StqlGrammar where 
import StqlTokens 
}

%name parseCalc 
%tokentype { StqlToken } 
%error { parseError }
%token 
    Bool   { TokenTypeBool _ } 
    Int    { TokenTypeInt _ } 
    Unit   { TokenTypeUnit _ }
    arr    { TokenTypeArr _ } 
    int    { TokenInt _ $$ } 
    true   { TokenTrue _ }
    false  { TokenFalse _ }
    '+'    { TokenPlus _ }
    var    { TokenVar _ $$ }
    if     { TokenIf _ }
    then   { TokenThen _ }
    else   { TokenElse _ }
    fst    { TokenFst _ }
    snd    { TokenSnd _ }
    lam    { TokenLambda _}
    let    { TokenLet _ }
    ':'    { TokenHasType _}
    '='    { TokenEq _ }
    in     { TokenIn _ }
    '('    { TokenLParen _ } 
    ')'    { TokenRParen _ } 
    ','    { TokenComma _ }
    '.'    { TokenEnd _}

%left '.'
%left arr
%right let
%right in
%nonassoc if
%nonassoc then
%nonassoc else
%left fst snd
%left '+'
%left ','
%nonassoc int true false var '(' ')'
%left lam
%left APP



%% 
Exp : int                                       { TmInt $1 } 
    | var                                       { TmVar $1 }
    | true                                      { TmTrue }
    | false                                     { TmFalse } 
    | '('')'                                    { TmUnit }
    | '(' Exp ',' Exp ')'                       { TmPair $2 $4 }
    | Exp '+' Exp                               { TmAdd $1 $3 }
    | fst Exp                                   { TmFst $2 }
    | snd Exp                                   { TmSnd $2 }
    | if Exp then Exp else Exp                  { TmIf $2 $4 $6 } 
    | lam '(' var ':' Type ')' Exp              { TmLambda $3 $5 $7 }
    | let '(' var ':' Type ')' '=' Exp in Exp   { TmLet $3 $5 $8 $10 }
    | Exp Exp %prec APP                         { TmApp $1 $2 } 
    | '(' Exp ')'                               { $2 }
    | Exp '.' Exp                               { TmEnd $3 $1}
    | Exp '.'                                   { TmEnd2 $1 }

Type : Bool                     { TyBool } 
     | Int                      { TyInt } 
     | Unit                     { TyUnit }
     | '(' Type ',' Type ')'    { TyPair $2 $4 }
     | Type arr Type            { TyFun $1 $3 } 


{ 
parseError :: [StqlToken] -> a
parseError [] = error "Unknown Parse Error" 
parseError (t:ts) = error ("Parse error at line:column " ++ (tokenPosn t))

data StqlType = TyInt | TyBool | TyUnit | TyPair StqlType StqlType | TyFun StqlType StqlType
   deriving (Show,Eq)

type Environment = [ (String,Expr) ]

data Expr = TmInt Int | TmTrue | TmFalse | TmUnit 
            | TmPair Expr Expr | TmAdd Expr Expr | TmVar String 
            | TmFst Expr | TmSnd Expr
            | TmIf Expr Expr Expr | TmLet String StqlType Expr Expr
            | TmLambda String StqlType Expr | TmApp Expr Expr 
            | TmEnd Expr Expr | TmEnd2 Expr
            | Cl String StqlType Expr Environment
    deriving (Show,Eq)
} 