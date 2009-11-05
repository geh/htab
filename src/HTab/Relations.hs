module HTab.Relations

( Relations(..), emptyRels, insertRelation, mergePrefixes,
  successors, predecessors, allRels, null, linksFromTo )

where

import qualified Data.Map as Map
import Data.Map ( Map )
import qualified Data.List as List

import qualified HTab.DMap as DMap
import HTab.DMap ( DMap(..) )

import HTab.Formula (Prefix, Rel, DependencySet, dsShow )
import Prelude hiding (id, pred, succ, null)

type InRel  = DMap Prefix Rel [(Prefix,DependencySet)]
type OutRel = DMap Prefix Rel [(Prefix,DependencySet)]

data Relations =  Relations {  inRel :: InRel ,
                              outRel :: OutRel }

emptyRels :: Relations
emptyRels = Relations { inRel = DMap.empty, outRel = DMap.empty }

null :: Relations -> Bool
null = Map.null . DMap.toMap . outRel

allRels :: Relations -> [(Prefix,Rel,Prefix)]
allRels rels = [ (p1,r,p2) | ((p1,r),ds_out_s) <-  DMap.flatten $ outRel rels,
                             (p2,_) <- ds_out_s ]


successors :: Relations -> Prefix -> Map Rel [(Prefix,DependencySet)]
successors rels p = Map.findWithDefault (Map.empty) p (DMap.toMap $ outRel rels)

predecessors :: Relations -> Prefix -> Map Rel [(Prefix,DependencySet)]
predecessors rels p = Map.findWithDefault (Map.empty) p (DMap.toMap $ inRel rels)

linksFromTo :: Relations -> Prefix -> Prefix -> [Rel]
linksFromTo rels p1 p2
  = map fst $ filter (\(_,p_d_s) -> p2 `elem` (map fst p_d_s) ) outs  where outs = Map.toList $ successors rels p1

-- assumes you never add twice the same relation
insertRelation :: Relations -> Prefix -> Rel -> Prefix -> DependencySet -> Relations
insertRelation rels p1 r p2 ds =
 let
  outRelMap = DMap.toMap $ outRel rels
  inRelMap = DMap.toMap $ inRel rels
  outRel_
   = case Map.lookup p1 outRelMap of
      Nothing       -> DMap $ Map.insert p1 (Map.singleton r [(p2,ds)]) outRelMap
      Just innerMap
        -> case Map.lookup r innerMap of
             Nothing             -> DMap $ Map.insert p1 (Map.insert r [(p2,ds)] innerMap)                outRelMap
             Just innerInnerList -> DMap $ Map.insert p1 (Map.insert r ((p2,ds):innerInnerList) innerMap) outRelMap
  inRel_
   = case Map.lookup p2 inRelMap of
      Nothing       -> DMap $ Map.insert p2 (Map.singleton r [(p1,ds)]) inRelMap
      Just innerMap
        -> case Map.lookup r innerMap of
            Nothing             -> DMap $ Map.insert p2 (Map.insert r [(p1,ds)] innerMap)                inRelMap
            Just innerInnerList -> DMap $ Map.insert p2 (Map.insert r ((p1,ds):innerInnerList) innerMap) inRelMap
 in
   Relations {outRel = outRel_ , inRel = inRel_ }


mergePrefixes :: Relations -> Prefix -> Prefix -> DependencySet -> Relations
mergePrefixes r pr ur _ | pr == ur = r
mergePrefixes r pr ur ds
 = let outRel_ = DMap.moveInnerDataDMapPlusDeps ds (outRel r) pr ur
       inRel_  = DMap.moveInnerDataDMapPlusDeps ds (inRel  r) pr ur
   in Relations { outRel = outRel_ , inRel = inRel_ }

instance Show Relations where
 show r  = "\nAccesibility: " ++ prettyShowMap_ (DMap.toMap $ outRel r) (\v -> "(" ++ prettyShowMap_rel_bps_x v ++ ")") "\n "

prettyShowMap_ :: (Show x, Show y) => Map.Map x y -> (y -> String) -> String -> String
prettyShowMap_ dasMap valueShow separator
 = concat $ List.intersperse separator $ map (\(k,v) -> show k ++ " -> " ++ valueShow v)
          $ Map.toList dasMap

prettyShowMap_rel_bps_x :: (Show a) => Map.Map Rel [(a,DependencySet)] -> String
prettyShowMap_rel_bps_x dasMap
 = concat $ List.intersperse ", " $ map (\(r,x_bp_s) -> (++) ("-" ++ show r ++ "-> ") $ concat $ List.intersperse ", "
                                           $ map (\(x,bp) -> show x ++ " " ++ dsShow bp) x_bp_s
                                        )
          $ Map.toList dasMap
