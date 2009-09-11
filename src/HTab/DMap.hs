module HTab.DMap where

-- import Test.QuickCheck       ( Arbitrary(..), Gen, Property,
--                                forAll, oneof, variant, sized, resize )
-- import HyLo.Test             ( UnitTest, runTest )
-- import Control.Monad ( liftM )

import Data.Map ( Map )
import qualified Data.Map as Map

import HTab.Formula(DependencySet, dsUnion)

import Prelude hiding ( lookup )

{- a DMap , or double map, is a nesting of two Maps -}

data DMap a b c = DMap (Map a (Map b c))

instance (Show a, Show b, Show c) =>  Show (DMap a b c) where
        show (DMap m) = show m

toMap :: DMap a b c -> Map a (Map b c)
toMap (DMap m) = m

empty :: DMap a b c
empty = DMap $ Map.empty


insert1 :: (Ord a, Ord b) => a -> (Map b c) -> DMap a b c -> DMap a b c
insert1 k1 v (DMap m) = DMap $ Map.insert k1 v m

insert :: (Ord a, Ord b) => a -> b -> c -> DMap a b c -> DMap a b c
insert k1 k2 v (DMap m)
 = case Map.lookup k1 m of
    Nothing     -> DMap $ Map.insert k1 (Map.singleton k2 v) m
    Just innerM -> DMap $ Map.insert k1 (Map.insert k2 v innerM) m


insertWith :: (Ord a, Ord b) => (c -> c -> c) -> a -> b -> c -> DMap a b c -> DMap a b c
insertWith f k1 k2 v (DMap m)
 = case Map.lookup k1 m of
    Nothing     -> DMap $ Map.insert k1 (Map.singleton k2 v) m
    Just innerM -> DMap $ Map.insert k1 (Map.insertWith f k2 v innerM) m

flatten :: DMap a b c -> [((a,b),c)]
flatten (DMap m)
 = let ambcs = Map.assocs m  in --  [(a,Map.Map b c)]
    concatMap (\(a_,innerM_) ->  map  (\(b_,c_) -> ((a_,b_),c_))  (Map.assocs innerM_  {- [(b,c)] -} )) ambcs

infixl 9 !

(!) :: (Ord a, Ord b) => DMap a b c -> a -> b -> c
(!) (DMap m) k1 k2 = (Map.!) ( (Map.!) m k1 ) k2


lookup :: (Ord a, Ord b) => a -> b -> DMap a b c -> Maybe c
lookup k1 k2 (DMap m) = do innerMap <- Map.lookup k1 m
                           Map.lookup k2 innerMap

lookup1 :: (Ord a) => a -> DMap a b c -> Maybe (Map b c)
lookup1 k1 (DMap m) = Map.lookup k1 m

delete :: (Ord a) => a -> DMap a b c -> DMap a b c
delete k1 (DMap m) = DMap $ Map.delete k1 m

lookupInter :: (Ord a) => a -> DMap a b c -> [b]
lookupInter k1 (DMap m) = case Map.lookup k1 m of
                           Nothing -> []
                           Just innerMap -> Map.keys innerMap 

-- provided two keys of the DMap and a merge function, merge the inner maps of
-- both keys using the merge function when needed for inner values
-- and delete the first inner map
moveInnerDataDMap :: (Ord a, Ord b) => DMap a b c -> a -> a -> (c -> c -> c) -> DMap a b c 
moveInnerDataDMap (DMap m) origKey destKey innerInnerMergeF
 = DMap result
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
moveInnerDataDMapPlusDeps :: (Ord a, Ord b) => DependencySet -> DMap a b [(DependencySet,c)] -> a -> a -> DMap a b [(DependencySet,c)]
moveInnerDataDMapPlusDeps newDeps (DMap m) origKey destKey
 = DMap result
   where mOrigInnerMap = Map.lookup origKey m
         mDestInnerMap = Map.lookup destKey m
         innerInnerMergeF = (++)
         prunedM = Map.delete origKey m
         addDepsToMap :: DependencySet -> Map.Map k [(DependencySet,c)] -> Map.Map k [(DependencySet,c)]
         addDepsToMap newBps = Map.map (addDeps newBps)
         addDeps :: DependencySet -> [(DependencySet,k)] -> [(DependencySet,k)]
         addDeps newBps = map (\(oldBps,el) -> (dsUnion oldBps newBps,el))
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

