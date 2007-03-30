{
{-# OPTIONS_GHC -w #-}
module Cparser
 
where 

import Clexer (Token(..), PosToken)
}
%name cParser
%tokentype { PosToken }

%token 
    '='                       {(Eq,          _, _)} 
    bool                      {(TF $$,_,_)}
    number                    {(Num $$,    _, _)} 

    filename                  {(FileName $$,_,_)}
    file                      {(File,_,_)}
    timeout                   {(Timeout,_,_)}
    selectionfunction         {(SFunction,_,_)}
    selectionfunctionvalue    {(SFValue $$,_,_)}
    showrules                 {(ShowR,_,_)}
    showstate                 {(ShowS,_,_)}
    savesat                   {(SaveSat,_,_)}
%%

Input : 
   {[]}
 | file '=' filename Input
   {("file",$3):$4}
 | timeout '=' number Input
   {("timeout",$3):$4}
 | selectionfunction '=' selectionfunctionvalue  Input
   {("sf",$3):$4}
 | showrules '=' bool Input  
   {("sr",$3):$4}
 | showstate '=' bool Input
   {("ss",$3):$4}
 | savesat '=' bool Input
   {("savesat",$3):$4}

{
happyError = parserError

parserError :: [PosToken] -> a
parserError [] = error "Parser error because input file ended unexpectantly."
parserError ((t, l, c):cs) =
    let {
        mess = if (l == 0)
               then "Parse error in arguments near col. " ++ show c
               else "Parse error in input file near line " ++
                                   show l ++
                                   ", col. " ++
                                   show c
    } in
    error (mess)

}

