module HTab.UCList
(UCList,
 superset_matching,
 update)
where

import Data.List
import Data.IntSet as IntSet

type UCList = [UCListRow]
type UCListRow = IntSet

----------subset matching------------------------------
--if indexes is a subset of any row
subset_matching :: Int -> [Int] -> UCList -> Maybe Int
subset_matching counter indexes (hd:tai) =
        if subset_matching_ indexes hd
         then Just counter
         else subset_matching (counter + 1) indexes tai
subset_matching _ _ [] = Nothing


subset_matching_ :: [Int] -> UCListRow -> Bool
subset_matching_ [] _ = True
subset_matching_ _ row | isEmpty row = False
subset_matching_ indexes row = (fromList indexes) `isSubsetOf` row

isEmpty :: UCListRow -> Bool
isEmpty = IntSet.null


----------superset matching------------------------------
--if index is a superset of any row
superset_matching :: Int -> [Int] -> UCList -> Maybe [Int]
superset_matching counter indexes (hd:tai) =
        if superset_matching_ indexes hd
         then Just (toList hd)
         else superset_matching (counter + 1) indexes tai
superset_matching _ _ [] = Nothing

superset_matching_ :: [Int] -> UCListRow -> Bool
superset_matching_ [] _ = False
superset_matching_ _ row | isEmpty row= True
superset_matching_ indexes row = row `isSubsetOf` ( fromList indexes )

update:: [Int] -> UCList -> UCList
update indexes li = 
        case subset_matching 0 indexes li of
          Just i -> update_row_list i indexes li
          Nothing -> case superset_matching 0 indexes li of
                        Just _  -> li --if indexes is a superset of a row, don't update
                        Nothing -> add_row_list indexes li

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

