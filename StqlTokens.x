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
  Int            { tok (\p s -> TokenTypeInt p) }
  String         { tok (\p s -> TokenTypeString p) }
  $digit+        { tok (\p s -> TokenInt p (read s)) }
  "++"           { tok (\p s -> TokenPlusString p) }    
  PlusVar        { tok (\p s -> TokenPlusVar p )}      
  \+             { tok (\p s -> TokenPlus p) }
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
  \;             { tok (\p s -> TokenEnd p) }
  Print          { tok (\p s -> TokenPrint p )}
  ReadFile       { tok (\p s -> TokenReadFile p) }
  GetVars        { tok (\p s -> TokenGetVar p) }
  ReadEnv        { tok (\p s -> TokenReadEnv p) }
  Format         { tok (\p s -> TokenFormat p) }
  ProcSemicComma { tok (\p s -> TokenProcSemicComma p) }
  Delimit        { tok (\p s -> TokenDelimit p) }
  In             { tok (\p s -> TokenIn p) }
  Compare        { tok (\p s -> TokenCompare p) }
  LiteralsNum    { tok (\p s -> TokenLiteralsNum p) }
  FillBasePrefixReady     { tok (\p s -> TokenFillBasePrefixReady p) }
  [$alpha $digit \_ \']*.ttl    { tok (\p s -> TokenFilePath p s) }
  \"$algit*\"    { tok (\p s -> TokenString p s) }
  $alpha+ [$alpha $digit \_ \’ ]*      { tok (\p s -> TokenVar p s) }

{ 
-- Each action has type :: AlexPosn -> String -> MDLToken 

-- Helper function
tok f p s = f p s

-- The token type: 
data StqlToken = 
  TokenEnd AlexPosn              |
  TokenTypeInt  AlexPosn         | 
  TokenTypeString  AlexPosn      |
  TokenInt AlexPosn Int          | 
  TokenString AlexPosn String    |
  TokenPlus AlexPosn             |
  TokenPlusString AlexPosn       |
  TokenPlusVar AlexPosn          |
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
  TokenVar AlexPosn String       |
  TokenReadFile AlexPosn         |
  TokenGetVar AlexPosn           |
  TokenFilePath AlexPosn String  |
  TokenFillBasePrefixReady AlexPosn |
  TokenProcSemicComma AlexPosn   | 
  TokenFormat AlexPosn           |
  TokenDelimit AlexPosn          |
  TokenCompare AlexPosn          |
  TokenIn AlexPosn               |
  TokenLiteralsNum AlexPosn      |
  TokenReadEnv AlexPosn
  deriving (Eq,Show) 

tokenPosn :: StqlToken -> String
tokenPosn (TokenTypeInt  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenTypeString  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenInt  (AlexPn a l c) _) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenString  (AlexPn a l c) _) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenPlus  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenPlusString  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenPlusVar  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
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
tokenPosn (TokenVar (AlexPn a l c) _) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenEnd (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenReadEnv (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenFormat (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenFillBasePrefixReady (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenProcSemicComma (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenDelimit (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenCompare (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenIn (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenLiteralsNum (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenReadFile (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenFilePath (AlexPn a l c) _) = show(l) ++ ":" ++ show(c)
}


--something useless now but may be use in future
--  Bool           { tok (\p s -> TokenTypeBool p)} 
--  Unit           { tok (\p s -> TokenTypeUnit p)}
--  \,             { tok (\p s -> TokenComma p) }
--  true           { tok (\p s -> TokenTrue p) }
--  false          { tok (\p s -> TokenFalse p) }
--  If             { tok (\p s -> TokenIf p) }
--  Then           { tok (\p s -> TokenThen p) }
--  Else           { tok (\p s -> TokenElse p) }
--  fst            { tok (\p s -> TokenFst p) }
--  snd            { tok (\p s -> TokenSnd p) }
--  TokenTypeBool AlexPosn         | 
--  TokenTypeUnit AlexPosn         |
--  TokenTrue AlexPosn             |
--  TokenFalse AlexPosn            |
--  TokenIf AlexPosn               |
--  TokenThen AlexPosn             |
--  TokenElse AlexPosn             |
--  TokenFst AlexPosn              |
--  TokenSnd AlexPosn              |
--  TokenComma AlexPosn            | 
--tokenPosn (TokenTypeUnit  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
--tokenPosn (TokenTypeUnit  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
--tokenPosn (TokenTrue  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
--tokenPosn (TokenFalse  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
--tokenPosn (TokenIf (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
--tokenPosn (TokenThen (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
--tokenPosn (TokenElse (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
--tokenPosn (TokenFst (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
--tokenPosn (TokenSnd (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
--tokenPosn (TokenComma (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
