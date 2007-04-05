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
Carlos Areces     - areces@loria.fr      - http://www.loria.fr/~areces
Daniel Gorin      - dgorin@dc.uba.ar
Juan Heguiabehere - juanh@inf.unibz.it - http://www.inf.unibz.it/~juanh/

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

module HyLoParse

where

import HyLoLexer(HyLoToken(..), FilePos, line, col)

import Branch
import Formula
}

%name parse
%tokentype { (HyLoToken, FilePos) }

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

%%

Input :
  begin Formulas end               { $2 }

Formula :
  dia Formula
{let f = $2 in (diamond (read $1) f)}

| box Formula
{let f = $2 in (box (read $1) f)}

| Formula dimp Formula
{let {
    f1 = $1;
    f2 = $3;
} in (conj (disj (neg f1) f2) (disj (neg f2) f1))}

| Formula imp Formula
{ let {
    f1 = $1;
    f2 = $3;
} in (disj (neg f1) f2)}

| neg Formula
{ let f = $2 in (neg f) }

| Formula and Formula
{ let {
    f1 = $1;
    f2 = $3;
} in (conj f1 f2)}

| Formula or Formula
{ let {
    f1 = $1;
    f2 = $3;
} in (disj f1 f2)}

| nom at Formula
{ let f = $3 in (at (read $1) f) }

| at2 nom Formula
{ let f = $3 in (at (read $2) f) }

| nom
{ (nom (read $1)) }

| prop
{ (prop (read $1)) }

| true
{ (taut) }

| false
{ (neg taut) }

| '(' Formula ')'
{ $2 }

|  Formula ';' Formula
{let {
    fs = $1;
    f = $3;
} in (conj fs f) }

Formulas :
 Formula
{let f = $1 in (addFormula emptyBranch (prefix 0 f))} -- prefix and add the
                                                      -- main formula


{
happyError :: [(HyLoToken, FilePos)] -> a
happyError []          = error "Unexpected end of file!"
happyError ((_, fp):_) = error ("Parse error near line " ++
                                   (show $ line fp) ++
                                   ", col. " ++
                                   (show $ col fp))

}

