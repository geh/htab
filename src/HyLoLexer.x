{
{-# OPTIONS_GHC -w #-}
module HyLoLexer (hyloLexer, HyLoToken(..), FilePos, line, col) where

}

%wrapper "posn"

$digit = [0-9]                  -- digits
$alpha = [a-zA-Z]               -- alphabetic characters
$alphaNum = [$alpha$digit]

@relName = [Rr]$digit+

hyloTokens :-
  $white+                               ;       -- strip whitspaces
  \%.*                                  ;       -- strip comments
  \{ (~\} | \n)* \}                     ;       -- strip multiple line comments

  begin                          { discardValue TokenBegin }
  end                            { discardValue TokenEnd }

  true                           { discardValue TokenTrue }
  false                          { discardValue TokenFalse }
  [Pp]$digit+                    { storeValue (TokenProp . tail) }
  [Nn]$digit+                    { storeValue (TokenNom . tail) }

  \<$white*@relName?$white*\>    { storeValue (TokenDia . relName . unenclose) }
  dia                            { discardValue (TokenDia anonRelName) }

  \[$white*@relName?$white*\]    { storeValue (TokenBox . relName . unenclose) }
  box                            { discardValue (TokenBox anonRelName) }

  \:                             { discardValue TokenAt }
  \@                             { discardValue TokenAt2 }

  A                              { discardValue TokenUBox }
  E                              { discardValue TokenUDia }

  [v\|]                          { discardValue TokenOr }
  [&\^]                          { discardValue TokenAnd }
  [\!\-\~]                       { discardValue TokenNeg }
  "<->"                          { discardValue TokenDimp }
  "->"                           { discardValue TokenImp }

  "("                            { discardValue TokenOB }
  ")"                            { discardValue TokenCB }

  \;                             { discardValue TokenSC }

{
data HyLoToken = TokenBegin       | TokenEnd           |
                 TokenAt          | TokenAt2           |
                 TokenImp         | TokenDimp          |
                 TokenNeg         | TokenAnd           | TokenOr         |
                 TokenProp String | TokenNom String    |
                 TokenTrue        | TokenFalse         |
                 TokenBox String  |
                 TokenDia String  |
                 TokenSC          | TokenOB            | TokenCB |
                 TokenUBox | TokenUDia
  deriving (Eq, Show, Read)

data FilePos = FP{line :: Int, col :: Int} deriving (Eq, Show)

makeFilePos (AlexPn _ l c) = FP{line = l, col = c}

hyloLexer :: String -> [(HyLoToken, FilePos)]
hyloLexer str = go (alexStartPos,'\n',str)
    where go inp@(pos,_,str) = case alexScan inp 0 of
                                    AlexEOF                       -> []
                                    AlexError (AlexPn _ l c, _,_) -> error ("Unknown token at line: " ++ (show l) ++ " col: " ++ (show c))
                                    AlexSkip  inp' len            -> go inp'
                                    AlexToken inp' len act        -> act pos (take len str) : go inp'

storeValue     token alexPos v = (token v, makeFilePos alexPos)   -- for building tokens which need the parsed string
discardValue   token alexPos _ = (token, makeFilePos alexPos)     -- for building tokens which discard the parsed string

unenclose = init . tail
anonRelName = "1"
relName r = if null r then anonRelName else (tail $ removeSpaces r)
removeSpaces = filter (/= ' ')
}