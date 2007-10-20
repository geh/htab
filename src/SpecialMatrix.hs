module SpecialMatrix
(
MMatrix, Bounds,
mkEmpty, addElement, newUArray, indexOfEarliest, Column,Row

) where

import Control.Monad.ST
import Control.Monad(filterM)
import Data.Array.ST(STUArray, readArray, writeArray, getBounds,newArray)
import Data.Array.Unboxed(UArray,listArray)
import Ix(range)

import Data.List(elemIndex)

type MMatrix s = STUArray s (Int,Int) Bool
type Bounds = ((Int,Int),(Int,Int))



newUArray :: Bounds -> UArray (Int,Int) Bool
newUArray ((a,b),(c,d)) = listArray ((a,b),(c,d)) (repeat False)

mkEmpty :: Bounds -> ST s (MMatrix s)
mkEmpty bnds   = newArray bnds False


-- returns the list of indexes of modified columns
-- and the new urfather of the new equivalence class

addElement :: MMatrix s -> (Int,Int) -> ST s ([Int],Int)
addElement t (pr,nom) = do writeArray t (pr,nom) True

                           rowIdxs <- seekRows nom t
                           rows <- mapM (getRow t) rowIdxs
                           let oredRow = orRows rows
                           replaceRowsBy rowIdxs oredRow t

                           colIdxs <- seekColumns pr t
                           cols <- mapM (getColumn t) colIdxs

                           let newUrfather = minimum $ urfatherSet cols

                           let oredCol = orColumns cols
                           replaceColsBy colIdxs oredCol t

                           return (colIdxs,newUrfather)

type Row = [Bool]
type Column = [Bool]


urfatherSet :: [Column] -> [Int]
urfatherSet cols = map indexOfEarliestNoMaybe cols


indexOfEarliestNoMaybe :: Column -> Int
indexOfEarliestNoMaybe c = case (elemIndex True c) of
                            Just e  -> e
                            Nothing -> error $ "indexOfEarliest error " ++ (show c)

indexOfEarliest :: Column -> Maybe Int
indexOfEarliest c = elemIndex True c

getRow :: MMatrix s -> Int -> ST s Row
getRow t rowNum =
 do bounds <- getBounds t
    let width = (snd $ snd bounds)
    getRow' t rowNum 0 width

getRow' :: MMatrix s -> Int -> Int -> Int -> ST s [Bool]
getRow' _ _ _ (-1) = return []
getRow' t rowNum colNum remainder = do  hd <- readArray t (rowNum,colNum)
                                        tl <- getRow' t rowNum (colNum+1) (remainder-1)
                                        return (hd:tl)

getColumn :: MMatrix s -> Int -> ST s Column
getColumn t column =
 do bounds <- getBounds t
    let height = (fst $ snd bounds)
    getColumn' t column 0 height

getColumn' :: MMatrix s -> Int -> Int -> Int -> ST s [Bool]
getColumn' _ _ _ (-1) = return []
getColumn' t colNum rowNum remainder = do hd <- readArray t (rowNum,colNum)
                                          tl <- getColumn' t colNum (rowNum+1) (remainder-1)
                                          return (hd:tl)

setRow :: MMatrix s -> Int -> [Bool] -> ST s ()
setRow t rowNum newrow = setRow' t 0 rowNum newrow


setRow' :: MMatrix s -> Int-> Int -> [Bool] -> ST s ()
setRow' t colNum rowNum (hd:tl) = do writeArray t (rowNum,colNum) hd
                                     setRow' t (colNum+1) rowNum tl

setRow' _ _ _ [] =  return ()

setColumn :: MMatrix s -> Int -> [Bool] -> ST s ()
setColumn t colNum newcolumn = setColumn' t colNum 0 newcolumn


setColumn' :: MMatrix s -> Int -> Int -> [Bool] -> ST s ()
setColumn' t colNum rowNum (hd:tl) = do writeArray t (rowNum,colNum) hd
                                        setColumn' t colNum (rowNum+1) tl

setColumn' _ _ _ [] =  return ()


seekColumns :: Int -> MMatrix s -> ST s [Int]
seekColumns rowNum t = do bounds <- getBounds t
                          let maxColIdx = snd $ snd bounds
                          let colIdxs = range (0,maxColIdx)
                          filterM (\c -> do readArray t (rowNum,c)) colIdxs

orColumns :: [Column] -> Column
orColumns = foldr1 or_lists

orRows :: [Row] -> Row
orRows = orColumns


replaceColsBy :: [Int] -> Column -> MMatrix s -> ST s ()
replaceColsBy colIdxs col t = mapM_ (\c -> setColumn t c col) colIdxs



seekRows :: Int -> MMatrix s -> ST s [Int]
seekRows colNum t = do bounds <- getBounds t
                       let maxRowIdx = fst $ snd bounds
                       let rowIdxs = range (0,maxRowIdx)
                       filterM (\r -> do readArray t (r,colNum)) rowIdxs

replaceRowsBy :: [Int] -> Row -> MMatrix s -> ST s ()
replaceRowsBy rowIdxs row t = mapM_ (\r -> setRow t r row) rowIdxs



or_lists :: [Bool] -> [Bool] -> [Bool]
or_lists = zipWith (||)
