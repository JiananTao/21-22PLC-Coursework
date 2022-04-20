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
--    Unit   { TokenTypeUnit _ }
    int    { TokenInt _ $$ }
    string { TokenString _ $$ } 
    true   { TokenTrue _ }
    false  { TokenFalse _ }
    '++'   { TokenPlusString _ }
    PlusASort { TokenPlusASort _ }
    '+'    { TokenPlus _ }
    var    { TokenVar _ $$ }
--    If     { TokenIf _ }
--    Then   { TokenThen _ }
--    Else   { TokenElse _ }
--    fst    { TokenFst _ }
--    snd    { TokenSnd _ }
    Let    { TokenLet _ }
    Print  { TokenPrint _ }
    Clear  { TokenClear _ }
    ClearAll  { TokenClearAll _ }
    ':'    { TokenHasType _}
    '='    { TokenEq _ }
    '('    { TokenLParen _ } 
    ')'    { TokenRParen _ } 
    '['    { TokenLList _ } 
    ']'    { TokenRList _ }
    '|'    { TokenListSeg _ }
    ','    { TokenComma _ }
    ';'    { TokenEnd _}
    path             {TokenFilePath _ $$}
    ReadFile         {TokenReadFile _ }
    GetVars          {TokenGetVar _ }
    ReadEnv          { TokenReadEnv _ }
    Format           { TokenFormat _ }
    FillPrefix       { TokenFillPrefix _ }
    FillBase         { TokenFillBase _ }
    Ready            { TokenReady _ }
    ProcSemic        { TokenProcSemic _ }
    ProcComma        { TokenProcComma _ }
    DefineSubj       { TokenDefineSubj _ }
    DefineObj        { TokenDefineObj _ }
    DefinePred       { TokenDefinePred _ }
    Compare          { TokenCompare _ }
    In               { TokenIn _ }
    LiteralsNum      { TokenLiteralsNum _ }

%left ';'
%left '['
%right Let
%right ClearAll
%right Clear
%right ReadFile
%right Format
%right Print
%right '='
--%nonassoc If
--%nonassoc Then
--%nonassoc Else
--%left fst snd
%left '+'
%left '++'
%left PlusASort
%left ','
%nonassoc int true false var '(' ')'




%% 
Exp : int                                       { TmInt $1 } 
    | string                                    { TmString $1 } 
    | var                                       { TmVar $1 }
    | true                                      { TmTrue }
    | false                                     { TmFalse } 
--    | '('')'                                    { TmUnit }
    | '(' Exp ',' Exp ')'                       { TmPair $2 $4 }
    | '[' Exp ']'                               { TmList $2 }
    | Exp '|' Exp                               { TmListSeg $1 $3 }
    | Exp '++' Exp                              { TmAddString $1 $3 }
    | Exp PlusASort Exp                         { TmPlusASort $1 $3 }
    | Exp '+' Exp                               { TmAdd $1 $3 }
--    | fst Exp                                   { TmFst $2 }
--    | snd Exp                                   { TmSnd $2 }
--    | If Exp Then Exp Else Exp                  { TmIf $2 $4 $6 } 
    | Let '(' var ':' Type ')' '=' Exp          { TmLet $3 $5 $8 }
    | Clear '(' var ':' Type ')'                { TmClear $3 $5 }
    | ClearAll                                  { TmClearAll }
    | '(' Exp ')'                               { $2 }
    | Exp ';' Exp                               { TmEnd $3 $1}
    | Exp ';'                                   { TmEnd2 $1 }
    | Print Exp                                 { TmPrint $2 }
    | ReadFile path                             { TmReadTTLFile $2 }
    | GetVars var                               { TmGetVar $2 }
    | ReadEnv                                   { TmReadEnv }
    | Format Exp                                { TmFormat $2 }
    | FillPrefix var                            { TmFillPrefix $2}
    | FillBase var                              { TmFillBase $2}
    | Ready var                                 { TmReady $2}
    | ProcSemic var                             { TmProcSemic $2}
    | ProcComma var                             { TmProcComma $2}
    | DefineSubj Exp In var                     { TmDefineSubj $2 $4 }
    | DefineObj string In var                   { TmDefineObj $2 $4 }
    | DefinePred string In var                  { TmDefinePred $2 $4 }
    | Compare string var In string var          { TmCompare $2 $3 $5 $6 }
    | LiteralsNum var                           { TmLiteralsNum $2 }


Type : Bool                     { TyBool } 
     | Int                      { TyInt } 
     | String                   { TyString }
--     | Unit                     { TyUnit }
--     | '(' Type ',' Type ')'    { TyPair $2 $4 }

--只支持string目前
--List : string '|' string                               { TmListSeg $1 $3 }


{ 
parseError :: [StqlToken] -> a
parseError [] = error "Unknown Parse Error" 
parseError (t:ts) = error ("Parse error at line:column " ++ (tokenPosn t))
-- | TyUnit
data StqlType = TyInt | TyString | TyBool | TyPair StqlType StqlType | TyFun StqlType StqlType
   deriving (Show,Eq)

type Environment = [ (String,Expr) ]
data Expr = TmInt Int | TmString String | TmTrue | TmFalse 
--          | TmUnit 
            | TmPair Expr Expr | TmAdd Expr Expr | TmVar String 
--            | TmFst Expr | TmSnd Expr 
            | TmAddString Expr Expr
--            | TmIf Expr Expr Expr 
            | TmLet String StqlType Expr
            | TmList Expr | TmListSeg Expr Expr
            | TmPrint Expr | TmPlusASort Expr Expr
            | TmGetVar String | TmReadEnv | TmFormat Expr
            | TmFillPrefix String | TmFillBase String | TmReady String
            | TmProcSemic String | TmProcComma String
            | TmClear String StqlType | TmClearAll
            | TmLiteralsNum String
            | TmDefineSubj Expr String | TmDefineObj String String | TmDefinePred String String
            | TmCompare String String String String
            | TmEnd Expr Expr | TmEnd2 Expr
            | TmReadTTLFile String
    deriving (Show,Eq)
--data Test = TmListSeg String String 
--    deriving (Show,Eq)

} 