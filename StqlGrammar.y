{ 
module StqlGrammar where 
import StqlTokens 
}

%name parseCalc 
%tokentype { StqlToken } 
%error { parseError }
%token 
    Int    { TokenTypeInt _ } 
    String { TokenTypeString _ }
    int    { TokenInt _ $$ }
    string { TokenString _ $$ } 
    '++'   { TokenPlusString _ }
    PlusVar { TokenPlusVar _ }
    '+'    { TokenPlus _ }
    var    { TokenVar _ $$ }
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
    ';'    { TokenEnd _}
    ReadFile         {TokenReadFile _ }
    GetVars          {TokenGetVar _ }
    ReadEnv          { TokenReadEnv _ }
    Format           { TokenFormat _ }
    FillBasePrefixReady       { TokenFillBasePrefixReady _ }
    ProcSemicComma        { TokenProcSemicComma _ }
    Delimit          { TokenDelimit _ }
    Compare          { TokenCompare _ }
    In               { TokenIn _ }
    LiteralsNum      { TokenLiteralsNum _ }
--    ','    { TokenComma _ }
--    Bool   { TokenTypeBool _ } 
--    Unit   { TokenTypeUnit _ }
--    true   { TokenTrue _ }
--    false  { TokenFalse _ }
--    If     { TokenIf _ }
--    Then   { TokenThen _ }
--    Else   { TokenElse _ }
--    fst    { TokenFst _ }
--    snd    { TokenSnd _ }

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
%left PlusVar
%nonassoc int true false var '(' ')'




%% 
Exp : int                                       { TmInt $1 } 
    | string                                    { TmString $1 } 
    | var                                       { TmVar $1 }
    | '[' Exp ']'                               { TmList $2 }
    | Exp '|' Exp                               { TmListSeg $1 $3 }
    | Exp '++' Exp                              { TmAddString $1 $3 }
    | Exp PlusVar Exp                         { TmPlusVar $1 $3 }
    | Exp '+' Exp                               { TmAdd $1 $3 }
    | Let '(' var ':' Type ')' '=' Exp          { TmLet $3 $5 $8 }
    | Clear '(' var ':' Type ')'                { TmClear $3 $5 }
    | ClearAll                                  { TmClearAll }
    | '(' Exp ')'                               { $2 }
    | Exp ';' Exp                               { TmEnd $3 $1}
    | Exp ';'                                   { TmEnd2 $1 }
    | Print Exp                                 { TmPrint $2 }
    | ReadFile string                           { TmReadTTLFile $2 }
    | GetVars var                               { TmGetVar $2 }
    | ReadEnv                                   { TmReadEnv }
    | Format Exp                                { TmFormat $2 }
    | FillBasePrefixReady var                            { TmFillBasePrefixReady $2}
    | ProcSemicComma var                             { TmProcSemicComma $2}
    | Delimit string Exp In var                 { TmDelimit $2 $3 $5 }
    | Compare string var In string var          { TmCompare $2 $3 $5 $6 }
    | LiteralsNum var                           { TmLiteralsNum $2 }
--    | true                                      { TmTrue }
--    | false                                     { TmFalse } 
--    | '('')'                                    { TmUnit }
--    | '(' Exp ',' Exp ')'                       { TmPair $2 $4 }
--    | fst Exp                                   { TmFst $2 }
--    | snd Exp                                   { TmSnd $2 }
--    | If Exp Then Exp Else Exp                  { TmIf $2 $4 $6 } 

Type : 
     Int                      { TyInt } 
     | String                   { TyString }
--   | Bool                     { TyBool } 
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
--          | TmTrue | TmFalse 
--          | TmUnit 
--            | TmPair Expr Expr 
--            | TmIf Expr Expr Expr 
--            | TmFst Expr | TmSnd Expr 
    deriving (Show,Eq)
--data Test = TmListSeg String String 
--    deriving (Show,Eq)

} 