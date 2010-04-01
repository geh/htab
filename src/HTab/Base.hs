----------------------------------------------------
--                                                --
-- Base.hs                                        --
-- General use functions                          --
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

module HTab.Base

where
import Control.Monad ( when )
import qualified Data.Map as Map
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IntMap
import Data.List ( sort )
import qualified Data.Set as Set

vPutStrLn :: String -> Bool -> IO ()
vPutStrLn s b = when b $ putStrLn s

intToBool :: Int -> Bool
intToBool i | i == 0 = False
intToBool _          = True

almostCartesianProduct :: [a] -> [b] -> [(a,b)]
-- example:
-- acp [a1,a2,a3] [b1,b2,b3] = [(a1,b2),(a1,b3),(a2,b1),(a2,b3),(a3,b1),(a3,b2)]
--
-- require : as and bs must be of the same size
almostCartesianProduct [] _  = error "almostCartesianProduct: first list empty"
almostCartesianProduct _  [] = error "almostCartesianProduct: second list empty"
almostCartesianProduct as bs = [(a,b) | (idxA,a) <- zip [(0::Int)..] as,
                                        (idxB,b) <- zip [(0::Int)..] bs,
                                        idxA /= idxB]


moveInMap :: IntMap b -> Int -> Int -> (b -> b -> b) -> IntMap b
moveInMap m origKey destKey mergeF
 = result
   where mOrigValue = IntMap.lookup origKey m
         prunedM    = IntMap.delete origKey m
         result = case mOrigValue of
                   Nothing -> m
                   Just origValue -> IntMap.insertWith mergeF destKey origValue prunedM

doMemoize :: Ord a => (a -> b) -> a -> Map.Map a b -> (b, Map.Map a b)
doMemoize f e m = case Map.lookup e m of
                   Nothing     -> let result = f e in (result, Map.insert e result m)
                   Just result -> (result, m)

permutationOf :: Ord a => [a] -> [a] -> Bool
permutationOf l1 l2 = sort l1 == sort l2

set :: Ord a => [a] -> Set.Set a
set = Set.fromList

list :: Ord a => Set.Set a -> [a]
list = Set.toList

invertMap :: (Ord a, Ord b) => Map.Map a b -> Map.Map b a
invertMap = Map.fromList . map (\(a,b) -> (b,a)) . Map.assocs
