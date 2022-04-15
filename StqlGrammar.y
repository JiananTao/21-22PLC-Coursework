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
    PlusASort { TokenPlusASort _ }
    '+'    { TokenPlus _ }
    var    { TokenVar _ $$ }
    If     { TokenIf _ }
    Then   { TokenThen _ }
    Else   { TokenElse _ }
    fst    { TokenFst _ }
    snd    { TokenSnd _ }
    Let    { TokenLet _ }
    Print  { TokenPrint _ }
    Clear  { TokenClear _ }
    ClearAll  { TokenClearAll _ }
    ':'    { TokenHasType _}
    '='    { TokenEq _ }
    '('    { TokenLParen _ } 
    ')'    { TokenRParen _ } 
    ','    { TokenComma _ }
    ';'    { TokenEnd _}
    path             {TokenFilePath _ $$}
    ReadFile         {TokenReadFile _ }
    GetVars           {TokenGetVar _ }
    ReadEnv          { TokenReadEnv _ }
    FillPrefix       { TokenFillPrefix _ }
    FillBase         { TokenFillBase _ }
    Ready            { TokenReady _ }

%left ';'
%left arr
%right Let
%right ClearAll
%right Clear
%right ReadFile
%right Print
%right '='
%nonassoc If
%nonassoc Then
%nonassoc Else
%left fst snd
%left '+'
%left PlusASort
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
    | Exp PlusASort Exp                         { TmPlusASort $1 $3 }
    | Exp '+' Exp                               { TmAdd $1 $3 }
    | fst Exp                                   { TmFst $2 }
    | snd Exp                                   { TmSnd $2 }
    | If Exp Then Exp Else Exp                  { TmIf $2 $4 $6 } 
    | Let '(' var ':' Type ')' '=' Exp          { TmLet $3 $5 $8 }
    | Clear '(' var ':' Type ')'                { TmClear $3 $5 }
    | ClearAll               { TmClearAll }
    | '(' Exp ')'                               { $2 }
    | Exp ';' Exp                               { TmEnd $3 $1}
    | Exp ';'                                   { TmEnd2 $1 }
    | Print Exp                                 { TmPrint $2 }
    | ReadFile path                             { TmReadTTLFile $2 }
    | GetVars var                               { TmGetVar $2 }
    | ReadEnv                                   { TmReadEnv }
    | FillPrefix var                            { TmFillPrefix $2}
    | FillBase var                              { TmFillBase $2}
    | Ready var                                 { TmReady $2}


Type : Bool                     { TyBool } 
     | Int                      { TyInt } 
     | String                   { TyString }
     | Unit                     { TyUnit }
     | '(' Type ',' Type ')'    { TyPair $2 $4 }
     | Type arr Type            { TyFun $1 $3 } 



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
            | TmPrint Expr | TmPlusASort Expr Expr
            | TmGetVar String | TmReadEnv 
            | TmFillPrefix String | TmFillBase String | TmReady String
            | TmClear String StqlType | TmClearAll
            | TmEnd Expr Expr | TmEnd2 Expr
            | TmReadTTLFile String
    deriving (Show,Eq)

} 