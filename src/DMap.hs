module DMap where

import qualified Data.Map as Map
import Formula(BranchingPrefixes, bps_union)



flattenDMap :: Map.Map a (Map.Map b c) -> [((a,b),c)]
flattenDMap m
 = let ambcs = Map.assocs m  in --  [(a,Map.Map b c)]
    concatMap (\(a_,innerM_) ->  map  (\(b_,c_) -> ((a_,b_),c_))  (Map.assocs innerM_  {- [(b,c)] -} )) ambcs

moveInnerDataDMap :: (Ord a, Ord b) => Map.Map a (Map.Map b c) -> a -> a -> (c -> c -> c) -> Map.Map a (Map.Map b c) 
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


-- same, but add dependencies to the copied formulas
moveInnerDataDMapPlusDeps :: (Ord a, Ord b) => BranchingPrefixes -> Map.Map a (Map.Map b [(BranchingPrefixes,c)]) -> a -> a -> Map.Map a (Map.Map b [(BranchingPrefixes,c)]) 
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


