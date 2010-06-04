module HTab.DMap
(DMap(..), empty, toMap, flatten,
 delete, insert, insertWith, (!),
 insert1, lookup, lookup1, lookupInter,
 moveInnerDataDMap, moveInnerDataDMapPlusDeps )

where

-- import Test.QuickCheck       ( Arbitrary(..), Gen, Property,
--                                forAll, oneof, variant, sized, resize )
-- import HyLo.Test             ( UnitTest, runTest )
-- import Control.Monad ( liftM )

import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM

import HTab.Formula(DependencySet, dsUnion)

import Prelude hiding ( lookup )

{- a DMap , or double map, is a nesting of two Maps -}

data DMap c = DMap (IntMap (IntMap c))

instance (Show c) =>  Show (DMap c) where
        show (DMap m) = show m

toMap :: DMap c -> IntMap (IntMap c)
toMap (DMap m) = m

empty :: DMap c
empty = DMap IM.empty

insert1 :: Int -> IntMap c -> DMap c -> DMap c
insert1 k1 v (DMap m) = DMap $ IM.insert k1 v m

insert :: Int -> Int -> c -> DMap c -> DMap c
insert k1 k2 v (DMap m)
 = case IM.lookup k1 m of
    Nothing     -> DMap $ IM.insert k1 (IM.singleton k2 v) m
    Just innerM -> DMap $ IM.insert k1 (IM.insert k2 v innerM) m


insertWith :: (c -> c -> c) -> Int -> Int -> c -> DMap c -> DMap c
insertWith f k1 k2 v (DMap m)
 = case IM.lookup k1 m of
    Nothing     -> DMap $ IM.insert k1 (IM.singleton k2 v) m
    Just innerM -> DMap $ IM.insert k1 (IM.insertWith f k2 v innerM) m

flatten :: DMap c -> [((Int,Int),c)]
flatten (DMap m)
 = let ambcs = IM.assocs m  in --  [(a,IntMap c)]
    concatMap (\(a_,innerM_) ->  map  (\(b_,c_) -> ((a_,b_),c_))  (IM.assocs innerM_ )) ambcs

infixl 9 !

(!) :: DMap c -> Int -> Int -> c
(!) (DMap m) k1 k2 = (IM.!) ( (IM.!) m k1 ) k2


lookup :: Int -> Int -> DMap c -> Maybe c
lookup k1 k2 (DMap m) = do innerMap <- IM.lookup k1 m
                           IM.lookup k2 innerMap

lookup1 :: Int -> DMap c -> Maybe (IntMap c)
lookup1 k1 (DMap m) = IM.lookup k1 m

delete ::  Int -> DMap c -> DMap c
delete k1 (DMap m) = DMap $ IM.delete k1 m

lookupInter :: Int -> DMap c -> [Int]
lookupInter k1 (DMap m) = case IM.lookup k1 m of
                           Nothing -> []
                           Just innerMap -> IM.keys innerMap 

-- provided two keys of the DMap and a merge function, merge the inner maps of
-- both keys using the merge function when needed for inner values
-- and delete the first inner map
moveInnerDataDMap :: DMap c -> Int -> Int -> (c -> c -> c) -> DMap c 
moveInnerDataDMap (DMap m) origKey destKey innerInnerMergeF
 = DMap result
   where mOrigInnerMap = IM.lookup origKey m
         mDestInnerMap = IM.lookup destKey m
         prunedM = IM.delete origKey m
         result = case (mOrigInnerMap, mDestInnerMap) of
                      (Nothing, _) -> m
                      (Just origInnerMap, Nothing) -> IM.insert destKey origInnerMap prunedM
                      (Just origInnerMap, Just destInnerMap)
                            -> let mergedInnerMap = IM.unionWith innerInnerMergeF origInnerMap destInnerMap in
                                IM.insert destKey mergedInnerMap prunedM


moveInnerDataDMapPlusDeps :: DependencySet -> DMap [(c,DependencySet)] -> Int -> Int -> DMap [(c,DependencySet)]
moveInnerDataDMapPlusDeps newDeps (DMap m) origKey destKey
 = DMap
    $ case IM.lookup origKey m of
        Nothing  -> m
        Just origInnerMap
            -> let origInnerMapPlusDeps = IM.map (addDeps newDeps) origInnerMap
                   prunedM = IM.delete origKey m
                   addDeps newBps = map (\(el,oldBps) -> (el,dsUnion newBps oldBps))
               in case IM.lookup destKey m of
                    Nothing -> IM.insert destKey origInnerMapPlusDeps prunedM
                    Just destInnerMap
                       -> let mergedInnerMap = IM.unionWith (++) origInnerMapPlusDeps destInnerMap
                          in  IM.insert destKey mergedInnerMap prunedM

