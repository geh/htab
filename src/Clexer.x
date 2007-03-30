{
{-# OPTIONS_GHC -w #-}
module Clexer (cLexer, Token(..), PosToken) where


}

%wrapper "posn"

$digit = 0-9                    -- digits
$alpha = [a-zA-Z]               -- alphabetic characters

tokens :-

  $white+                               ;
  \%.*                                  ;

  [Tt]rue                        { tok (TF "True") }
  [Ff]alse                       { tok (TF "False") }

  \=                             { tok Eq }

  [Ff]ile                        { tok File }
  [Tt]imeout                     { tok Timeout }
  [Ss]how[Rr]ules                { tok ShowR }
  [Ss]how[Ss]tate                { tok ShowS }
  [Ss]ave[Ss]at                  { tok SaveSat }

  [Ss]election[Ff]unction        { tok SFunction }
  [Lnaodb]+                      { \p s -> tok' (SFValue s) p }

  [$digit]+                      { \p s -> tok' (Num s) p }

  [!$white]+                     { \p s -> tok' (FileName s) p }


{
data Token =
    Eq | TF String | Num String | FileName String | File | Timeout |
    SFunction | SFValue String |
    ShowR | ShowS | SaveSat
  deriving (Eq, Show, Read)

type PosToken = (Token, Int, Int)

cLexer :: String -> [(Token, Int, Int)]
cLexer = alexScanTokens

-- Token builder:
tok  t p s = tok' t p             -- discards the s (this is sugar)
tok' t (AlexPn _ l c) = (t, l, c) -- used when you need to access the s
}