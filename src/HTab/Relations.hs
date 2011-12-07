module HTab.Relations

( Relations(..), emptyRels, insertRelation, mergePrefixes,
  successors, predecessors, allRels, null, linksFromTo )

where

import qualified Data.IntMap as IntMap
import Data.IntMap ( IntMap )

import qualified Data.List as List

import qualified HTab.DMap as D
import HTab.DMap ( DMap )

import HTab.Formula (Prefix, Rel, DependencySet, dsShow )
import Prelude hiding (id, pred, succ, null)

type InRel  = DMap {- Prefix Rel -} [(Prefix,DependencySet)]
type OutRel = DMap {- Prefix Rel -} [(Prefix,DependencySet)]

data Relations =  Relations {  inRel :: InRel ,
                              outRel :: OutRel }

emptyRels :: Relations
emptyRels = Relations { inRel = D.empty, outRel = D.empty }

null :: Relations -> Bool
null = IntMap.null . outRel

allRels :: Relations -> [(Prefix,Rel,Prefix)]
allRels rels = [ (p1,r,p2) | ((p1,r),ds_out_s) <-  D.flatten $ outRel rels,
                             (p2,_) <- ds_out_s ]


successors :: Relations -> Prefix -> IntMap {- Rel -} [(Prefix,DependencySet)]
successors rels p = IntMap.findWithDefault IntMap.empty p (outRel rels)

predecessors :: Relations -> Prefix -> IntMap {- Rel -} [(Prefix,DependencySet)]
predecessors rels p = IntMap.findWithDefault IntMap.empty p (inRel rels)

linksFromTo :: Relations -> Prefix -> Prefix -> [Rel]
linksFromTo rels p1 p2
  = map fst $ filter (\(_,p_d_s) -> p2 `elem` map fst p_d_s ) outs  where outs = IntMap.toList $ successors rels p1

-- assumes you never add twice the same relation
insertRelation :: Relations -> Prefix -> Rel -> Prefix -> DependencySet -> Relations
insertRelation rels p1 r p2 ds =
 let
  outRelMap = outRel rels
  inRelMap = inRel rels
  outRel_
   = case IntMap.lookup p1 outRelMap of
      Nothing       -> IntMap.insert p1 (IntMap.singleton r [(p2,ds)]) outRelMap
      Just innerMap
        -> case IntMap.lookup r innerMap of
             Nothing             -> IntMap.insert p1 (IntMap.insert r [(p2,ds)] innerMap)                outRelMap
             Just innerInnerList -> IntMap.insert p1 (IntMap.insert r ((p2,ds):innerInnerList) innerMap) outRelMap
  inRel_
   = case IntMap.lookup p2 inRelMap of
      Nothing       -> IntMap.insert p2 (IntMap.singleton r [(p1,ds)]) inRelMap
      Just innerMap
        -> case IntMap.lookup r innerMap of
            Nothing             -> IntMap.insert p2 (IntMap.insert r [(p1,ds)] innerMap)                inRelMap
            Just innerInnerList -> IntMap.insert p2 (IntMap.insert r ((p1,ds):innerInnerList) innerMap) inRelMap
 in
   Relations {outRel = outRel_ , inRel = inRel_ }


mergePrefixes :: Relations -> Prefix -> Prefix -> DependencySet -> Relations
mergePrefixes r pr ur _ | pr == ur = r
mergePrefixes r pr ur ds
 = let outRel_ = D.moveInnerDataDMapPlusDeps ds (outRel r) pr ur
       inRel_  = D.moveInnerDataDMapPlusDeps ds (inRel  r) pr ur
   in Relations { outRel = outRel_ , inRel = inRel_ }

instance Show Relations where
 show r  = "\nAccesibility: " ++ prettyShowMap_ (outRel r) (\v -> "(" ++ prettyShowMap_rel_bps_x v ++ ")") "\n "

prettyShowMap_ :: (Show y) => IntMap y -> (y -> String) -> String -> String
prettyShowMap_ dasMap valueShow separator
 = List.intercalate separator $ map (\(k,v) -> show k ++ " -> " ++ valueShow v)
          $ IntMap.toList dasMap

prettyShowMap_rel_bps_x :: (Show a) => IntMap {- Rel -} [(a,DependencySet)] -> String
prettyShowMap_rel_bps_x dasMap
 = List.intercalate ", " $ map (\(r,x_bp_s) -> (++) ("-" ++ show r ++ "-> ") $ List.intercalate ", "
                                 $ map (\(x,bp) -> show x ++ " " ++ dsShow bp) x_bp_s )
          $ IntMap.toList dasMap
