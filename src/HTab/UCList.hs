module HTab.UCList
(UCList,subset_matching_list,superset_matching_list)
where

import Data.Maybe()

import Data.List()

--import Debug.Trace(trace)


--the list that will represent the cache
type UCListRow = [Int]
type UCList = [UCListRow]

----------subset matching------------------------------
--if indexes is a subset of any row
subset_matching_list :: Int -> [Int] -> UCList -> Maybe Int
subset_matching_list counter indexes (hd:tai) =
        if subset_matching_list_ indexes hd
         then Just counter
         else (subset_matching_list (counter + 1) indexes tai)
subset_matching_list _ _ [] = Nothing

subset_matching_list_ :: [Int] -> UCListRow -> Bool
subset_matching_list_ (i:ri) (l:rl) = 
        if i==l
         then subset_matching_list_ ri rl
         else if i<l 
                then False
                else subset_matching_list_ (i:ri) rl 
subset_matching_list_ [] _ = True
subset_matching_list_ (_:_) [] = False

----------superset matching------------------------------
--if index is a superset of any row
superset_matching_list :: Int -> [Int] -> UCList -> Maybe Int
superset_matching_list counter indexes (hd:tai) =
        if superset_matching_list_ indexes hd
         then Just counter
         else superset_matching_list (counter + 1) indexes tai
superset_matching_list _ _ [] = Nothing

superset_matching_list_ :: [Int] -> UCListRow -> Bool
superset_matching_list_ (i:ri) (l:rl) = 
        if i==l
         then superset_matching_list_ ri rl
         else if i>l 
                then False
                else superset_matching_list_ ri (l:rl)
superset_matching_list_ _ [] = True
superset_matching_list_ [] (_:_) = False



-------------debug-------------
--debug :: Show a => a -> a
--debug x = trace (show x) x
