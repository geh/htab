----------------------------------------------------
--                                                --
-- RuleMetadata.hs:                               --
-- Miscelaneous rule data/info, that probably     --
-- should go in Rules.hs but didn't work due to   --
-- mutually recursive modules and the 'deriving'  --
-- clause....                                     --
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

module HTab.RuleMetadata(RuleId(..))

where

import Data.Ix

data RuleId = R_Dia     -- Diamond <r>
            | R_DiaX    -- DiamondX <r*>
            | R_Disj    -- Disjunction
            | R_SemBr   -- Semantic Branching
            | R_At      -- Satisfaction operator (@) rule
            | R_Down    -- Down-arrow rule
            | R_NegNom  -- Negation before nominal rule
            | R_Exist   -- Existential modality
            | R_Diff    -- Difference modality
            | R_Discard -- Discarding a formula
            | R_Clash   -- Branch clash
            | R_UBlocking -- Unrestricted Blocking
            | R_Merge   -- Equivalence classes merge
        deriving(Eq, Ord, Ix, Show)
