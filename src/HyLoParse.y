----------------------------------------------------
--                                                --
-- HyLoParse.y:                                   --
-- Hybrid Logic Syntax, parser file for Happy     --
--                                                --
----------------------------------------------------

{
{-# OPTIONS_GHC -w #-}
{-
Copyright (C) HyLoRes 2002-2005

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307,
USA.
-}

module HyLoParse (parse)

where

import HyLo.InputFile.Lexer ( Token(..), FilePos, line, col )

import Formula
}

%name parse
%tokentype { (Token, FilePos) }

%token
             begin           { (TokenBegin    , _) }
             end             { (TokenEnd      , _) }
             at              { (TokenAt       , _) }
             at2             { (TokenAt2      , _) }
             prop            { (TokenProp $$  , _) }
             nom             { (TokenNom $$   , _) }
             true            { (TokenTrue     , _) }
             false           { (TokenFalse    , _) }
             neg             { (TokenNeg      , _) }
             and             { (TokenAnd      , _) }
             or              { (TokenOr       , _) }
             dimp            { (TokenDimp     , _) }
             imp             { (TokenImp      , _) }
             box             { (TokenBox $$   , _) }
             dia             { (TokenDia $$   , _) }
             '('             { (TokenOB       , _) }
             ')'             { (TokenCB       , _) }
             ';'             { (TokenSC       , _) }

%left ';'
%right imp
%right dimp
%left or
%left and
%left box dia neg
%right at

%%

Input :: {Formula}
Input :
  begin Formula end          { $2 }

Formula :: { Formula }
Formula :
  true                        {taut}
| false                       {neg taut}
| nom                         {nom $1}
| prop                        {prop $1}
| neg  Formula                {neg $2}
| dia  Formula                {diamond $1 $2}
| box  Formula                {box $1 $2}
| Formula dimp Formula        {dimp $1 $3}
| Formula imp Formula         {imp $1 $3}
| Formula and Formula         {conj $1 $3}
| Formula or Formula          {disj $1 $3}
| nom at Formula              {at $1 $3}
| at2 nom Formula             {at $2 $3}
| '(' Formula ')'             {$2}
|  Formula ';' Formula        {conj $1 $3}


{
happyError :: [(Token, FilePos)] -> a
happyError []          = error "Unexpected end of file!"
happyError ((_, fp):_) = error ("Parse error near line " ++
                                   (show $ line fp) ++
                                   ", col. " ++
                                   (show $ col fp))

}

