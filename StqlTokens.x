{ 
module StqlTokens where 
}

%wrapper "posn" 
$digit = 0-9     
-- digits 
$alpha = [a-zA-Z]    
-- alphabetic characters

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
  \+             { tok (\p s -> TokenPlus p) }
  if             { tok (\p s -> TokenIf p) }
  then           { tok (\p s -> TokenThen p) }
  else           { tok (\p s -> TokenElse p) }
  fst            { tok (\p s -> TokenFst p) }
  snd            { tok (\p s -> TokenSnd p) }
  \\             { tok (\p s -> TokenLambda p) }
  \:             { tok (\p s -> TokenHasType p) }
  clear          { tok (\p s -> TokenClear p )}
  let            { tok (\p s -> TokenLet p )}
  =              { tok (\p s -> TokenEq p )}
  SPLIT          { tok (\p s -> TokenSplit p )}
  WHEN           { tok (\p s -> TokenWhen p )}
  \(             { tok (\p s -> TokenLParen p) }
  \)             { tok (\p s -> TokenRParen p) }
  [$alpha $digit \_ \']*.ttl    { tok (\p s -> TokenFilePath p s) }
  \;             { tok (\p s -> TokenEnd p) }
  READFILE       { tok (\p s -> TokenReadFile p) }
  GETVAR         { tok (\p s -> TokenGetVar p) }
  READENV        { tok (\p s -> TokenReadEnv p) }
  $alpha [$alpha $digit \_ \’]*      { tok (\p s -> TokenVar p s) }
  \"$alpha [$alpha $digit \_ \’]*\"  { tok (\p s -> TokenString p s) }


{ 
-- Each action has type :: AlexPosn -> String -> MDLToken 

-- Helper function
tok f p s = f p s

-- The token type: 
data StqlToken = 
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
  TokenIf AlexPosn               |
  TokenThen AlexPosn             |
  TokenElse AlexPosn             |
  TokenFst AlexPosn              |
  TokenSnd AlexPosn              |
  TokenLambda AlexPosn           |
  TokenHasType AlexPosn          |
  TokenLet AlexPosn              |
  TokenSplit AlexPosn            |
  TokenWhen AlexPosn             |
  TokenClear AlexPosn            |
  TokenEq AlexPosn               |
  TokenLParen AlexPosn           |
  TokenRParen AlexPosn           |
  TokenComma AlexPosn            | 
  TokenVar AlexPosn String       |
  TokenReadFile AlexPosn         |
  TokenGetVar AlexPosn           |
  TokenFilePath AlexPosn String  |
  TokenEnd AlexPosn              |
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
tokenPosn (TokenIf (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenThen (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenElse (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenFst (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenSnd (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenHasType (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenLet (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenGetVar (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenSplit (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenWhen (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenClear (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenEq  (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenLParen (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenRParen (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenComma (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenVar (AlexPn a l c) _) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenEnd (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenReadEnv (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenReadFile (AlexPn a l c)) = show(l) ++ ":" ++ show(c)
tokenPosn (TokenFilePath (AlexPn a l c) _) = show(l) ++ ":" ++ show(c)
}