module HTab.DMap
(DMap, empty, flatten,
 delete, insert, insertWith, (!),
 insert1, lookup, lookup1, lookupInter,
 moveInnerPlusDeps, moveInnerPlusDeps3 )

where

import Data.IntMap ( IntMap )
import qualified Data.IntMap as I

import HTab.Formula(DependencySet, dsUnion)

import Prelude hiding ( lookup )

{- a DMap , or double map, is a nesting of two Maps -}

type DMap c = IntMap (IntMap c)

empty :: DMap c
empty = I.empty

insert1 :: Int -> IntMap c -> DMap c -> DMap c
insert1 k1 v m = I.insert k1 v m

insert :: Int -> Int -> c -> DMap c -> DMap c
insert k1 k2 v m
 = case I.lookup k1 m of
    Nothing     -> I.insert k1 (I.singleton k2 v) m
    Just innerM -> I.insert k1 (I.insert k2 v innerM) m


insertWith :: (c -> c -> c) -> Int -> Int -> c -> DMap c -> DMap c
insertWith f k1 k2 v m
 = case I.lookup k1 m of
    Nothing     -> I.insert k1 (I.singleton k2 v) m
    Just innerM -> I.insert k1 (I.insertWith f k2 v innerM) m

flatten :: DMap c -> [((Int,Int),c)]
flatten m
 = let ambcs = I.assocs m  in --  [(a,IntMap c)]
    concatMap (\(a_,innerM_) ->  map  (\(b_,c_) -> ((a_,b_),c_))  (I.assocs innerM_ )) ambcs

infixl 9 !

(!) :: DMap c -> Int -> Int -> c
(!) m k1 k2 = (I.!) ( (I.!) m k1 ) k2


lookup :: Int -> Int -> DMap c -> Maybe c
lookup k1 k2 m = do innerMap <- I.lookup k1 m
                    I.lookup k2 innerMap

lookup1 :: Int -> DMap c -> Maybe (IntMap c)
lookup1 k1 m = I.lookup k1 m

delete ::  Int -> DMap c -> DMap c
delete k1 m = I.delete k1 m

lookupInter :: Int -> DMap c -> [Int]
lookupInter k1 m = case I.lookup k1 m of
                    Nothing -> []
                    Just innerMap -> I.keys innerMap

-- provided two keys of the DMap and a merge function, merge the inner maps of
-- both keys using the merge function when needed for inner values
-- delete the first inner map
-- and add the given dependencies
moveInnerPlusDeps :: DependencySet -> DMap [(c,DependencySet)] -> Int -> Int
                        -> DMap [(c,DependencySet)]
moveInnerPlusDeps newDeps m origKey destKey
 = case I.lookup origKey m of
     Nothing  -> m
     Just origInnerMap
        -> let origInnerMapPlusDeps = I.map (addDeps newDeps) origInnerMap
               prunedM = I.delete origKey m
               addDeps newBps = map (\(el,oldBps) -> (el,dsUnion newBps oldBps))
           in case I.lookup destKey m of
                Nothing -> I.insert destKey origInnerMapPlusDeps prunedM
                Just destInnerMap
                   -> let mergedInnerMap = I.unionWith (++) origInnerMapPlusDeps destInnerMap
                      in  I.insert destKey mergedInnerMap prunedM

moveInnerPlusDeps3 :: DependencySet -> DMap [(c1,c2,DependencySet)] -> Int -> Int
                        -> DMap [(c1,c2,DependencySet)]
moveInnerPlusDeps3 newDeps m origKey destKey
 = case I.lookup origKey m of
     Nothing  -> m
     Just origInnerMap
        -> let origInnerMapPlusDeps = I.map (addDeps newDeps) origInnerMap
               prunedM = I.delete origKey m
               addDeps newBps = map (\(el1,el2,oldBps) -> (el1,el2,dsUnion newBps oldBps))
           in case I.lookup destKey m of
                Nothing -> I.insert destKey origInnerMapPlusDeps prunedM
                Just destInnerMap
                   -> let mergedInnerMap = I.unionWith (++) origInnerMapPlusDeps destInnerMap
                      in  I.insert destKey mergedInnerMap prunedM

