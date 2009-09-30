module HTab.UCList
(UCList,
 superset_matching,
 update)
where

import Data.List
import Data.IntSet as IntSet
import Data.Set ( Set )
import qualified Data.Set as Set

type UCList = [UCListRow]
type UCListRow = IntSet

----------subset matching------------------------------
--if indexes is a subset of any row
subset_matching :: [Int] -> UCList -> Maybe Int
subset_matching idxs listCache =
  go 0 idxs listCache
 where go :: Int -> [Int] -> UCList -> Maybe Int
       go counter indexes (hd:tai) =
        if subset_matching_ indexes hd
         then Just counter
         else go (counter + 1) indexes tai
       go _ _ [] = Nothing


subset_matching_ :: [Int] -> UCListRow -> Bool
subset_matching_ [] _ = True
subset_matching_ _ row | isEmpty row = False
subset_matching_ indexes row = (fromList indexes) `isSubsetOf` row

isEmpty :: UCListRow -> Bool
isEmpty = IntSet.null


----------superset matching------------------------------
--if index is a superset of any row
superset_matching :: Set Int -> UCList -> Maybe [Int]
superset_matching idxs listCache =
  go 0 (Set.toList idxs) listCache
 where go :: Int -> [Int] -> UCList -> Maybe [Int]
       go counter indexes (hd:tai) =
           if superset_matching_ indexes hd
            then Just (toList hd)
            else go (counter + 1) indexes tai
       go _ _ [] = Nothing

superset_matching_ :: [Int] -> UCListRow -> Bool
superset_matching_ [] _ = False
superset_matching_ _ row | isEmpty row= True
superset_matching_ indexes row = row `isSubsetOf` ( fromList indexes )

update:: Set Int -> UCList -> UCList
update sindexes li =
  let indexes = Set.toList sindexes
  in   case subset_matching indexes li of
          Just i -> update_row_list i indexes li
          Nothing -> case superset_matching sindexes li of
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

