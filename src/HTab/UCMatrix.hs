module HTab.UCMatrix 
(UCMatrix,subset_matching,superset_matching,gen_matrix,update_matrix)
where

import Data.Maybe()
import Data.Array.Diff

--import Debug.Trace(trace)


--a bit matrix where we will store the patterns found in the algorithm
type UCMatrix = DiffArray  (Int,Int) Bool


----------------bit-matrix-------------------

gen_matrix :: Int -> Int -> UCMatrix 
gen_matrix u v = array ((0,0),(u-1,v-1)) [((i,j),False) | j <- range (0,v-1), i <- range (0,u-1)] :: UCMatrix


--if the list of indexes are a subset of some row in the matrix,
--it returns the matrix row, otherwise it returns nothing
--------subsetmatching
subset_matching :: Int -> Int -> Int -> Int -> [Int] ->UCMatrix -> Maybe Int
subset_matching cu_row row max_row max_col indexes matrix =
                if (row > max_row) || (cu_row == (-1))
                  then Nothing
                  else if subset_matching_ row 0 max_col indexes matrix
                        then Just row
                        else subset_matching cu_row (row+1) max_row max_col indexes matrix 

subset_matching_ :: Int -> Int -> Int -> [Int] ->UCMatrix -> Bool
subset_matching_ row col max_col (i:rest) matrix =
                if col > max_col
                  then False
                  else if i==col 
                         then if matrix !(row,col) == True
                                then subset_matching_ row (col+1) max_col rest matrix
                                else False
                         else if i>col 
                                then subset_matching_ row (col+1) max_col (i:rest) matrix
                                else False

subset_matching_ _ _ _ [] _ = True

--if the list of indexes are a superset of some row in the matrix,
--it returns the matrix row, otherwise it returns nothing
--------superset matching        
superset_matching :: Int -> Int -> Int -> [Int] ->UCMatrix -> Maybe [Int]
superset_matching row max_row max_col indexes matrix =
                if row > max_row
                  then Nothing
                  else if superset_matching_ False row 0 max_col indexes matrix
                        then Just (get_indexes indexes matrix row 0 max_col)
                        else superset_matching (row+1) max_row max_col indexes matrix 

get_indexes :: [Int]-> UCMatrix -> Int -> Int -> Int -> [Int]
get_indexes (i:rest) m row col max_col= 
   if col < max_col 
        then if i==col 
                then if  m !(row,col) == True 
                        then let rest_new = get_indexes rest m row (col+1) max_col 
                             in (i:rest_new)
                        else get_indexes rest m row (col+1) max_col 
                else get_indexes (i:rest) m row (col+1) max_col 
        else if i==col 
                then if  m !(row,col) == True 
                        then [i]
                        else []
                else []

get_indexes [] _ _ _ _= []

superset_matching_ :: Bool -> Int -> Int -> Int -> [Int] ->UCMatrix -> Bool
superset_matching_ flag row col max_col (i:rest) matrix =
                if col > max_col 
                  then if flag then True
                               else False
                  else if i==col
                         then if matrix !(row,col) == True
                                then superset_matching_ True row (col+1) max_col rest matrix
                                else superset_matching_ flag row (col+1) max_col rest matrix
                         else if i>col
                                then if matrix !(row,col) == True
                                        then False
                                        else superset_matching_ flag row (col+1) max_col (i:rest) matrix
                                else False

superset_matching_ flag row col max_col [] matrix =
                if (col > max_col) && flag
                  then True
                  else if flag
                        then if matrix !(row,col) == True
                                then False
                                else superset_matching_ flag row (col+1) max_col [] matrix
                        else False


add_row :: Int -> Int -> Int
add_row old_current_row mrow = 
        if old_current_row <  mrow
                then old_current_row + 1
                else 0

update_matrix :: Int -> Int -> Int -> [Int] -> UCMatrix -> (Int,UCMatrix)
update_matrix cu_col cu_row ma_row indexes mat =
        case (subset_matching cu_row 0 ma_row cu_col indexes mat) of
             Nothing -> case (superset_matching 0 ma_row cu_col indexes mat) of
                          Nothing -> let new_current_row = (add_row cu_row ma_row)
                                         ma2 = update_row new_current_row 0 cu_col indexes  mat
                                     in (new_current_row, ma2)
                          Just _ -> (cu_row,mat)  --if it is a superset of an aready existing row, don't add it 
             Just i -> let ma1 = (update_row i 0 cu_col indexes  mat)
                       in (cu_row,ma1)

--update the row (entered in the first parameter) of the matrix 
--with the information in the indexes (the fourth paramter):
--for each column of the matrix: 
--if column in list of indexes then matrix(row,column)= True
--else matrix(row,column) = False
update_row ::  Int -> Int -> Int -> [Int] -> UCMatrix-> UCMatrix
update_row row col max_col (i:rest) m =
        if col <= max_col
        then if col == i 
                then if m !(row,col) == False
                     then let new_matrix = m //[((row,col),True)]
                          in update_row row (col+1) max_col rest new_matrix
                     else update_row row (col+1) max_col rest m
                else if m !(row,col) == True 
                     then let new_matrix = m //[((row,col),False)]
                          in update_row row (col+1) max_col (i:rest) new_matrix
                     else update_row row (col+1) max_col (i:rest) m
        else m
update_row row col max_col [] m =
        if col <= max_col
        then if m !(row,col) == True 
                then let new_matrix = m //[((row,col),False)]
                     in update_row row (col+1) max_col [] new_matrix
                else update_row row (col+1) max_col [] m
        else m













--debug :: Show a => a -> a
--debug x = trace (show x) x
