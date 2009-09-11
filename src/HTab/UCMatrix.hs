module HTab.UCMatrix 
(UCMatrix,
 superset_matching,
 empty,
 update)
where

import Data.Array.Diff

type UCMatrix = DiffArray  (Int,Int) Bool

----------------bit-matrix-------------------

empty :: Int -> Int -> UCMatrix 
empty u v = array ((0,0),(u-1,v-1)) [((i,j),False) | j <- range (0,v-1), i <- range (0,u-1)]


--if the list of indexes are a subset of some row in the matrix,
--it returns the matrix row, otherwise it returns nothing
--------subsetmatching
subset_matching :: Int -> Int -> Int -> Int -> [Int] -> UCMatrix -> Maybe Int
subset_matching cu_row row max_row max_col indexes matrix =
                if (row > max_row) || (cu_row == -1)
                  then Nothing
                  else if subset_matching_ row 0 max_col indexes matrix
                        then Just row
                        else subset_matching cu_row (row+1) max_row max_col indexes matrix 

subset_matching_ :: Int -> Int -> Int -> [Int] -> UCMatrix -> Bool
subset_matching_ _   _   _       []       _                  = True
subset_matching_ _   col max_col _        _ |  col > max_col = False
subset_matching_ row col max_col (i:rest) matrix
 = case i `compare` col of
     EQ -> ( matrix !(row,col) ) && subset_matching_ row (col+1) max_col rest     matrix
     GT ->                          subset_matching_ row (col+1) max_col (i:rest) matrix
     LT -> False

--if the list of indexes are a superset of some row in the matrix,
--it returns the matrix row, otherwise it returns nothing
superset_matching :: Int -> Int -> Int -> [Int] -> UCMatrix -> Maybe [Int]
superset_matching row max_row _ _ _ | row > max_row = Nothing
superset_matching row max_row max_col indexes matrix =
   if superset_matching_ False row 0 max_col indexes matrix
     then Just (get_indexes indexes matrix row 0 max_col)
     else superset_matching (row+1) max_row max_col indexes matrix 


get_indexes :: [Int]-> UCMatrix -> Int -> Int -> Int -> [Int]
get_indexes (i:rest) m row col max_col
 | col < max_col
 = if i==col 
     then if m !(row,col)
             then (i : get_indexes rest     m row (col+1) max_col )
             else      get_indexes rest     m row (col+1) max_col 
     else              get_indexes (i:rest) m row (col+1) max_col 

get_indexes (i:_) m row col _
 = if ( i==col ) && ( m !(row,col) )
     then [i]
     else []

get_indexes [] _ _ _ _ = []

superset_matching_ :: Bool -> Int -> Int -> Int -> [Int] ->UCMatrix -> Bool
superset_matching_ flag _   col max_col _        _      | col > max_col = flag
superset_matching_ flag row col max_col (i:rest) matrix =
 case i `compare` col of
   EQ -> if matrix !(row,col)
           then superset_matching_ True row (col+1) max_col rest matrix
           else superset_matching_ flag row (col+1) max_col rest matrix
   GT -> ( not $ matrix !(row,col) ) && superset_matching_ flag row (col+1) max_col (i:rest) matrix
   LT -> False 

superset_matching_ flag row col max_col [] matrix =
    ( not $ matrix !(row,col) ) && superset_matching_ flag row (col+1) max_col [] matrix

add_row :: Int -> Int -> Int
add_row old_current_row mrow | old_current_row < mrow =  old_current_row + 1
add_row _ _ = 0

update :: Int -> Int -> Int -> [Int] -> UCMatrix -> (Int,UCMatrix)
update cu_col cu_row ma_row indexes mat =
   case subset_matching cu_row 0 ma_row cu_col indexes mat of
        Nothing -> case superset_matching 0 ma_row cu_col indexes mat of
                     Nothing -> -- update
                                let new_current_row = add_row cu_row ma_row
                                    ma2 = update_row new_current_row 0 cu_col indexes  mat
                                in (new_current_row ,  ma2)
                     Just _ -> (cu_row ,  mat)
                                 --if it is a superset of an aready existing row, don't add it 
        Just i -> let ma1 = update_row i 0 cu_col indexes  mat
                  in (cu_row ,  ma1)



--update the row (entered in the first parameter) of the matrix 
--with the information in the indexes (the fourth paramter):
--for each column of the matrix: 
--if column in list of indexes then matrix(row,column)= True
--else matrix(row,column) = False
update_row ::  Int -> Int -> Int -> [Int] -> UCMatrix -> UCMatrix
update_row _ col max_col _ m | col > max_col = m

update_row row col max_col (i:rest) m 
 = if col == i 
     then if not $ m !(row,col)
          then let new_matrix = m //[((row,col),True)]
               in update_row row (col+1) max_col rest new_matrix
          else update_row row (col+1) max_col rest m
     else if m !(row,col)
          then let new_matrix = m //[((row,col),False)]
               in update_row row (col+1) max_col (i:rest) new_matrix
          else update_row row (col+1) max_col (i:rest) m

update_row row col max_col [] m =
 if m !(row,col)
   then let new_matrix = m // [((row,col),False)]
        in update_row row (col+1) max_col [] new_matrix
   else update_row row (col+1) max_col [] m


