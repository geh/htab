module SpecialMatrix
(
MMatrix, Bounds,
mkEmpty, addElement, newUArray, indexOfEarliest, Column,Line

) where

import Control.Monad.ST
import Control.Monad(filterM)
import Data.Array.ST(STUArray, readArray, writeArray, getBounds,newArray)
import Data.Array.Unboxed(UArray,listArray)
--import Data.Array.IArray
import Ix(range)
--import Debug.Trace(trace)

import Data.Set(elems,Set,empty,insert)
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

                           lineIdxs <- seekLines nom t
                           lines <- mapM (getLineT t) lineIdxs  -- Warning: This binding for `lines' shadows an existing binding
                           let oredLine = orLines lines
                           replaceLinesBy lineIdxs oredLine t

                           colIdxs <- seekColumns pr t
                           cols <- mapM (getColumn t) colIdxs

                           let newUrfather = foldr1 min $ elems $ urfatherSet (empty::Set Int) cols

                           let oredCol = orColumns cols
                           replaceColsBy colIdxs oredCol t

                           return (colIdxs,newUrfather)



urfatherSet :: Set Int -> [Column] -> Set Int
urfatherSet s (hd:_) = insert (indexOfEarliestNoMaybe hd) s
urfatherSet s [] = s


indexOfEarliestNoMaybe :: Column -> Int
indexOfEarliestNoMaybe c = case (elemIndex True c) of
                            Just e  -> e
                            Nothing -> error $ "indexOfEarliest error " ++ (show c)

indexOfEarliest :: Column -> Maybe Int
indexOfEarliest c = elemIndex True c


type Line = [Bool]
type Column = [Bool]

getLineT :: MMatrix s -> Int -> ST s Line
getLineT t lineNum =
 do bounds <- getBounds t
    let width = (snd $ snd bounds)
    getLine' t lineNum 0 width

getLine' :: MMatrix s -> Int -> Int -> Int -> ST s [Bool]
getLine' _ _ _ (-1) = return []
getLine' t lineNum colNum remainder = do  hd <- readArray t (lineNum,colNum)
                                          tl <- getLine' t lineNum (colNum+1) (remainder-1)
                                          return (hd:tl)

getColumn :: MMatrix s -> Int -> ST s Column
getColumn t column =
 do bounds <- getBounds t
    let height = (fst $ snd bounds)
    getColumn' t column 0 height

getColumn' :: MMatrix s -> Int -> Int -> Int -> ST s [Bool]
getColumn' _ _ _ (-1) = return []
getColumn' t colNum lineNum remainder = do hd <- readArray t (lineNum,colNum)
                                           tl <- getColumn' t colNum (lineNum+1) (remainder-1)
                                           return (hd:tl)

setLine :: MMatrix s -> Int -> [Bool] -> ST s ()
setLine t lineNum newline = setLine' t 0 lineNum newline


setLine' :: MMatrix s -> Int-> Int -> [Bool] -> ST s ()
setLine' t colNum lineNum (hd:tl) = do writeArray t (lineNum,colNum) hd
                                       setLine' t (colNum+1) lineNum tl

setLine' _ _ _ [] =  return ()

setColumn :: MMatrix s -> Int -> [Bool] -> ST s ()
setColumn t colNum newcolumn = setColumn' t colNum 0 newcolumn


setColumn' :: MMatrix s -> Int -> Int -> [Bool] -> ST s ()
setColumn' t colNum lineNum (hd:tl) = do writeArray t (lineNum,colNum) hd
                                         setColumn' t colNum (lineNum+1) tl

setColumn' _ _ _ [] =  return ()


seekColumns :: Int -> MMatrix s -> ST s [Int]
seekColumns lineNum t = do bounds <- getBounds t
                           let maxColIdx = snd $ snd bounds
                           let colIdxs = range (0,maxColIdx)
                           filterM (\c -> do readArray t (lineNum,c)) colIdxs

orColumns :: [Column] -> Column
orColumns = foldr1 or_lists

orLines :: [Line] -> Line
orLines = orColumns


replaceColsBy :: [Int] -> Column -> MMatrix s -> ST s ()
replaceColsBy colIdxs col t = mapM_ (\c -> setColumn t c col) colIdxs



seekLines :: Int -> MMatrix s -> ST s [Int]
seekLines colNum t = do bounds <- getBounds t
                        let maxLineIdx = fst $ snd bounds
                        let lineIdxs = range (0,maxLineIdx)
                        filterM (\l -> do readArray t (l,colNum)) lineIdxs

replaceLinesBy :: [Int] -> Line -> MMatrix s -> ST s ()
replaceLinesBy lineIdxs line t = mapM_ (\l -> setLine t l line) lineIdxs



or_lists :: [Bool] -> [Bool] -> [Bool]
or_lists = zipWith (||)
