----------------------------------------------------
--                                                --
-- FormulaFamily.hs:                              --
-- A (partial) classification of formulas         --
-- according to their structure.                  --
--                                                --
----------------------------------------------------
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

module FormulaFamily(FormulaFamily(..), fullRange,
                     isAtNegLit, isInLIT_P, isABox, isAComplexDia)

where

import Data.Ix

data FormulaFamily = AtnP          -- @n p
                   | AtnNotP       -- @n -p
                   | Eqnm          -- @n m   for  n \neq m
                   | Neqnm         -- @n -m  for  n \neq m
                   | Relnm         -- @n<r>m
                   | AtnDiaF       -- @n<r>F   (F is not a nominal)
                   | RelInvnm      -- @n<r->m
                   | AtnDiaInvF    -- @n<r->F  (F is not a nominal)
                   | AtnBoxF       -- @n[r]F
                   | AtnBoxInvF    -- @n[r-]F
                   | AtnDownF      -- @n down x . F(x)
                   | AtnDisjF      -- @n (F_1 v ... v F_k)
                   | AtnConjF      -- @n (F_1 ^ ... ^ F_k)
                   | TrivTrue      -- @n T, @n n
                   | TrivFalse     -- @n -T, @n -n
        deriving (Eq, Ord, Ix, Show)

fullRange :: (FormulaFamily, FormulaFamily)
fullRange = (AtnP, TrivFalse)

isAtNegLit :: FormulaFamily -> Bool
isAtNegLit AtnNotP = True
isAtNegLit Neqnm   = True
isAtNegLit _       = False

isABox :: FormulaFamily -> Bool
isABox AtnBoxF    = True
isABox AtnBoxInvF = True
isABox _          = False

isAComplexDia :: FormulaFamily -> Bool
isAComplexDia AtnDiaF    = True
isAComplexDia AtnDiaInvF = True
isAComplexDia _          = False

{- isInLIT_P: Given

  - a formula f

  returns True iff f is in the set LIT-P (i.e. if f is of the form
  @_i a, for a (positive) literal, or of the form @_i<r>j)
-}
isInLIT_P :: FormulaFamily -> Bool
isInLIT_P Eqnm     = True
isInLIT_P AtnP     = True
isInLIT_P Relnm    = True
isInLIT_P RelInvnm = True
isInLIT_P _        = False
