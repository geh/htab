module HTab.UCList
(UCList,subset_matching_list,superset_matching_list,
 update_list)
where

import Data.Maybe()

import Data.List()
import Data.IntSet as IntSet

--import Debug.Trace(trace)


--the list that will represent the cache
type UCListRow = IntSet
type UCList = [UCListRow]


isEmpty :: UCListRow -> Bool
isEmpty is = if is == IntSet.empty then True
                                   else False

----------subset matching------------------------------
--if indexes is a subset of any row
subset_matching_list :: Int -> [Int] -> UCList -> Maybe Int
subset_matching_list counter indexes (hd:tai) =
        if subset_matching_list_ indexes hd
         then Just counter
         else (subset_matching_list (counter + 1) indexes tai)
subset_matching_list _ _ [] = Nothing



subset_matching_list_ :: [Int] -> UCListRow -> Bool
subset_matching_list_ [] _ = True
--subset_matching_list_ (_:_) isEmpty = False
subset_matching_list_ _ row | isEmpty row = False
subset_matching_list_ indexes row = 
        let ind_set= fromList indexes
        in isSubsetOf ind_set row





----------superset matching------------------------------
--if index is a superset of any row
superset_matching_list :: Int -> [Int] -> UCList -> Maybe [Int]
superset_matching_list counter indexes (hd:tai) =
        if superset_matching_list_ indexes hd
         then Just (toList hd)
         else superset_matching_list (counter + 1) indexes tai
superset_matching_list _ _ [] = Nothing

superset_matching_list_ :: [Int] -> UCListRow -> Bool
superset_matching_list_ [] _ = False
superset_matching_list_ _ row | isEmpty row= True
superset_matching_list_ indexes row = 
        let ind_set= fromList indexes
        in isSubsetOf row ind_set 





update_list:: [Int] -> UCList -> UCList
update_list indexes li = 
        case (subset_matching_list 0 indexes li) of
          Just i -> (update_row_list i indexes li)
          Nothing -> case superset_matching_list 0 indexes li of
                        Just _ -> li --if indexes is a superset of a row, don't update
                        Nothing -> (add_row_list indexes li)

update_row_list::Int -> [Int] -> UCList -> UCList
update_row_list ind indexes li = 
        let pre = take ind li
            suf = drop (ind + 1) li
            new_li = pre ++ suf
            ind_set = fromList indexes
        in (ind_set:new_li)

add_row_list :: [Int] -> UCList -> UCList
add_row_list indexes li = 
                let ind_set = fromList indexes
                in (ind_set:li)


-------------debug-------------
--debug :: Show a => a -> a
--debug x = trace (show x) x



