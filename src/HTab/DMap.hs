module HTab.DMap where

import qualified Data.Map as Map
import HTab.Formula(BranchingPrefixes, bps_union)


{- a DMap , or double map, is a nesting of two Maps -}

type DMap a b c = Map.Map a (Map.Map b c)

flattenDMap :: DMap a b c -> [((a,b),c)]
flattenDMap m
 = let ambcs = Map.assocs m  in --  [(a,Map.Map b c)]
    concatMap (\(a_,innerM_) ->  map  (\(b_,c_) -> ((a_,b_),c_))  (Map.assocs innerM_  {- [(b,c)] -} )) ambcs


-- provided two keys of the DMap and a merge function, merge the inner maps of
-- both keys using the merge function when needed for inner values
-- and delete the first inner map
moveInnerDataDMap :: (Ord a, Ord b) => DMap a b c -> a -> a -> (c -> c -> c) -> DMap a b c 
moveInnerDataDMap m origKey destKey innerInnerMergeF
 = result
   where mOrigInnerMap = Map.lookup origKey m
         mDestInnerMap = Map.lookup destKey m
         prunedM = Map.delete origKey m
         result = case (mOrigInnerMap, mDestInnerMap) of
                      (Nothing, _) -> m
                      (Just origInnerMap, Nothing) -> Map.insert destKey origInnerMap prunedM
                      (Just origInnerMap, Just destInnerMap)
                            -> let mergedInnerMap = Map.unionWith innerInnerMergeF origInnerMap destInnerMap in
                                Map.insert destKey mergedInnerMap prunedM


-- a specialised version of the previous function, that handles dependencies merging and adding
moveInnerDataDMapPlusDeps :: (Ord a, Ord b) => BranchingPrefixes -> DMap a b [(BranchingPrefixes,c)] -> a -> a -> DMap a b [(BranchingPrefixes,c)]
moveInnerDataDMapPlusDeps newDeps m origKey destKey
 = result
   where mOrigInnerMap = Map.lookup origKey m
         mDestInnerMap = Map.lookup destKey m
         innerInnerMergeF = (++)
         prunedM = Map.delete origKey m
         addDepsToMap :: BranchingPrefixes -> Map.Map k [(BranchingPrefixes,c)] -> Map.Map k [(BranchingPrefixes,c)]
         addDepsToMap newBps = Map.map (addDeps newBps)
         addDeps :: BranchingPrefixes -> [(BranchingPrefixes,k)] -> [(BranchingPrefixes,k)]
         addDeps newBps = map (\(oldBps,el) -> (bps_union oldBps newBps,el))
         result = case (mOrigInnerMap, mDestInnerMap) of
                      (Nothing, _) -> m
                      (Just origInnerMap, Nothing) -> let origInnerMapPlusDeps = addDepsToMap newDeps origInnerMap
                                                      in
                                                       Map.insert destKey origInnerMapPlusDeps prunedM
                      (Just origInnerMap, Just destInnerMap)
                            -> let origInnerMapPlusDeps = addDepsToMap newDeps origInnerMap
                                   mergedInnerMap       = Map.unionWith innerInnerMergeF origInnerMapPlusDeps destInnerMap
                               in
                                Map.insert destKey mergedInnerMap prunedM

