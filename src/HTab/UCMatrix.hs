module HTab.UCMatrix 
(UCMatrix,subset_matching,superset_matching,gen_matrix )
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
superset_matching :: Int -> Int -> Int -> [Int] ->UCMatrix -> Maybe Int
superset_matching row max_row max_col indexes matrix =
                if row > max_row
                  then Nothing
                  else if superset_matching_ False row 0 max_col indexes matrix
                        then Just row
                        else superset_matching (row+1) max_row max_col indexes matrix 

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


--debug :: Show a => a -> a
--debug x = trace (show x) x
