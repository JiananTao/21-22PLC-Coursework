{ 
module StqlTokens where 
}

%wrapper "posn" 
-- digits 
$digit = 0-9     
-- alphabetic characters
$alpha = [a-zA-Z]   
$algit = [a-zA-Z0-9\#\:\/\.]


tokens :-
$white+       ; 
  "--".*        ; 
  Bool           { tok (\p s -> TokenTypeBool p)} 
  Int            { tok (\p s -> TokenTypeInt p) }
  String         { tok (\p s -> TokenTypeString p) }
  Unit           { tok (\p s -> TokenTypeUnit p)}
  "->"           { tok (\p s -> TokenTypeArr p) }
  \,             { tok (\p s -> TokenComma p) }
  $digit+        { tok (\p s -> TokenInt p (read s)) }
  true           { tok (\p s -> TokenTrue p) }
  false          { tok (\p s -> TokenFalse p) }
  "++"           { tok (\p s -> TokenPlusString p) }    
  PlusASort      { tok (\p s -> TokenPlusASort p )}      
  \+             { tok (\p s -> TokenPlus p) }
  If             { tok (\p s -> TokenIf p) }
  Then           { tok (\p s -> TokenThen p) }
  Else           { tok (\p s -> TokenElse p) }
  fst            { tok (\p s -> TokenFst p) }
  snd            { tok (\p s -> TokenSnd p) }
  \\             { tok (\p s -> TokenLambda p) }
  \:             { tok (\p s -> TokenHasType p) }
  ClearAll       { tok (\p s -> TokenClearAll p )}
  Clear          { tok (\p s -> TokenClear p )}
  Let            { tok (\p s -> TokenLet p )}
  =              { tok (\p s -> TokenEq p )}
  \(             { tok (\p s -> TokenLParen p) }
  \)             { tok (\p s -> TokenRParen p) }
  \[             { tok (\p s -> TokenLList p) }
  \]             { tok (\p s -> TokenRList p) }
  \|             { tok (\p s -> TokenListSeg p) }
  [$alpha $digit \_ \']*.ttl    { tok (\p s -> TokenFilePath p s) }
  \;             { tok (\p s -> TokenEnd p) }
  Print          { tok (\p s -> TokenPrint p )}
  ReadFile       { tok (\p s -> TokenReadFile p) }
  GetVars        { tok (\p s -> TokenGetVar p) }
  ReadEnv        { tok (\p s -> TokenReadEnv p) }
  Format         { tok (\p s -> TokenFormat p) }
  FillPrefix     { tok (\p s -> TokenFillPrefix p) }
  FillBase       { tok (\p s -> TokenFillBase p) }
  Ready          { tok (\p s -> TokenReady p) }
  ProcSemic      { tok (\p s -> TokenProcSemic p) }
  ProcComma      { tok (\p s -> TokenProcComma p) }
  DefineSubj     { tok (\p s -> TokenDefineSubj p) }
  DefineObj      { tok (\p s -> TokenDefineObj p) }
  DefinePred     { tok (\p s -> TokenDefinePred p) }
  In             { tok (\p s -> TokenIn p) }
  Compare        { tok (\p s -> TokenCompare p) }
  $alpha [$alpha $digit \_ \’]*      { tok (\p s -> TokenVar p s) }
  \"$algit*\"    { tok (\p s -> TokenString p s) }


{ 
-- Each action has type :: AlexPosn -> String -> MDLToken 

-- Helper function
tok f p s = f p s

-- The token type: 
data StqlToken = 
  TokenEnd AlexPosn              |
  TokenTypeBool AlexPosn         | 
  TokenTypeInt  AlexPosn         | 
  TokenTypeString  AlexPosn      |
  TokenTypeUnit AlexPosn         |
  TokenTypeArr  AlexPosn         |
  TokenInt AlexPosn Int          | 
  TokenString AlexPosn String    |
  TokenTrue AlexPosn             |
  TokenFalse AlexPosn            |
  TokenPlus AlexPosn             |
  TokenPlusString AlexPosn       |
  TokenPlusASort AlexPosn        |
  TokenIf AlexPosn               |
  TokenThen AlexPosn             |
  TokenElse AlexPosn             |
  TokenFst AlexPosn              |
  TokenSnd AlexPosn              |
  TokenLambda AlexPosn           |
  TokenHasType AlexPosn          |
  TokenLet AlexPosn              |
  TokenPrint AlexPosn            |
  TokenClear AlexPosn            |
  TokenClearAll AlexPosn         |
  TokenEq AlexPosn               |
  TokenLParen AlexPosn           |
  TokenRParen AlexPosn           |
  TokenLList AlexPosn            |
  TokenRList AlexPosn            |
  TokenListSeg AlexPosn          |
  TokenComma AlexPosn            | 
  TokenVar AlexPosn String       |
  TokenReadFile AlexPosn         |
  TokenGetVar AlexPosn           |
  TokenFilePath AlexPosn String  |
  TokenFillPrefix AlexPosn       |
  TokenFillBase AlexPosn         |
  TokenReady AlexPosn            |
  TokenProcSemic AlexPosn        | 
  TokenProcComma AlexPosn        | 
  TokenFormat AlexPosn           |
  TokenDefineSubj AlexPosn       |
  TokenDefineObj AlexPosn        |
  TokenDefinePred AlexPosn       |
  TokenCompare AlexPosn          |
  TokenIn AlexPosn               |
  TokenReadEnv AlexPosn
  deriving (Eq,Show) 

tokenPosn :: StqlToken -> String
tokenPosn (TokenTypeBool (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenTypeInt  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenTypeString  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenTypeUnit  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenTypeArr  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenInt  (AlexPn a l c) _) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenString  (AlexPn a l c) _) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenTrue  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenFalse  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenPlus  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenPlusString  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenPlusASort  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenIf (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenThen (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenElse (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenFst (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenSnd (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenHasType (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenLet (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenGetVar (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenPrint (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenClear (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenClearAll (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenEq  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenLParen (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenRParen (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenLList (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenRList (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenListSeg (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenComma (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenVar (AlexPn a l c) _) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenEnd (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenReadEnv (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenFormat (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenFillPrefix (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenFillBase (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenReady (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenProcSemic (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenProcComma (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenDefineSubj (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenDefineObj (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenDefinePred (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenCompare (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenIn (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenReadFile (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenFilePath (AlexPn a l c) _) = show(l) ++ ":" ++ show(c)
}