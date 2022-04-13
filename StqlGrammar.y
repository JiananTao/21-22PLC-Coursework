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
    String { TokenTypeString _ }
    Unit   { TokenTypeUnit _ }
    arr    { TokenTypeArr _ } 
    int    { TokenInt _ $$ }
    string { TokenString _ $$ } 
    true   { TokenTrue _ }
    false  { TokenFalse _ }
    '++'   { TokenPlusString _ }
    '+'    { TokenPlus _ }
    var    { TokenVar _ $$ }
    if     { TokenIf _ }
    then   { TokenThen _ }
    else   { TokenElse _ }
    fst    { TokenFst _ }
    snd    { TokenSnd _ }
    let    { TokenLet _ }
    ':'    { TokenHasType _}
    '='    { TokenEq _ }
    '('    { TokenLParen _ } 
    ')'    { TokenRParen _ } 
    ','    { TokenComma _ }
    '.'    { TokenEnd _}
    path             {TokenFilePath _ $$}
    READFILE         {TokenReadFile _ }

%left '.'
%left arr
%right let
%right '='
%nonassoc if
%nonassoc then
%nonassoc else
%left fst snd
%left '+'
%left '++'
%left ','
%nonassoc int true false var '(' ')'



%% 
Exp : int                                       { TmInt $1 } 
    | string                                    { TmString $1 } 
    | var                                       { TmVar $1 }
    | true                                      { TmTrue }
    | false                                     { TmFalse } 
    | '('')'                                    { TmUnit }
    | '(' Exp ',' Exp ')'                       { TmPair $2 $4 }
    | Exp '++' Exp                              { TmAddString $1 $3 }
    | Exp '+' Exp                               { TmAdd $1 $3 }
    | fst Exp                                   { TmFst $2 }
    | snd Exp                                   { TmSnd $2 }
    | if Exp then Exp else Exp                  { TmIf $2 $4 $6 } 
    | let '(' var ':' Type ')' '=' Exp          { TmLet $3 $5 $8 }
    | '(' Exp ')'                               { $2 }
    | Exp '.' Exp                               { TmEnd $3 $1}
    | Exp '.'                                   { TmEnd2 $1 }


Type : Bool                     { TyBool } 
     | Int                      { TyInt } 
     | String                   { TyString }
     | Unit                     { TyUnit }
     | '(' Type ',' Type ')'    { TyPair $2 $4 }
     | Type arr Type            { TyFun $1 $3 } 

Function : READFILE path        {TmReadTTLFile $2}


{ 
parseError :: [StqlToken] -> a
parseError [] = error "Unknown Parse Error" 
parseError (t:ts) = error ("Parse error at line:column " ++ (tokenPosn t))

data StqlType = TyInt | TyString | TyBool | TyUnit | TyPair StqlType StqlType | TyFun StqlType StqlType
   deriving (Show,Eq)

type Environment = [ (String,Expr) ]

data Expr = TmInt Int | TmString String | TmTrue | TmFalse | TmUnit 
            | TmPair Expr Expr | TmAdd Expr Expr | TmVar String 
            | TmFst Expr | TmSnd Expr | TmAddString Expr Expr
            | TmIf Expr Expr Expr | TmLet String StqlType Expr
            | TmEnd Expr Expr | TmEnd2 Expr
            | Cl String StqlType Expr Environment
            | TmReadTTLFile String
    deriving (Show,Eq)
--TmFile 仅在此处出现

} 