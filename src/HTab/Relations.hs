module HTab.Relations

( Relations(..), emptyRels, insertRelation, mergePrefixes,
  successors, predecessors, allRels, null, linksFromTo )

where

import qualified Data.IntMap as I
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
null = I.null . outRel

allRels :: Relations -> [(Prefix,Rel,Prefix)]
allRels rels = [ (p1,r,p2) | ((p1,r),ds_out_s) <-  D.flatten $ outRel rels,
                             (p2,_) <- ds_out_s ]


successors :: Relations -> Prefix -> IntMap {- Rel -} [(Prefix,DependencySet)]
successors rels p = I.findWithDefault I.empty p (outRel rels)

predecessors :: Relations -> Prefix -> IntMap {- Rel -} [(Prefix,DependencySet)]
predecessors rels p = I.findWithDefault I.empty p (inRel rels)

linksFromTo :: Relations -> Prefix -> Prefix -> [Rel]
linksFromTo rels p1 p2
  = map fst $ filter (\(_,p_d_s) -> p2 `elem` map fst p_d_s ) outs
     where outs = I.toList $ successors rels p1

-- assumes you never add twice the same relation
insertRelation :: Relations -> Prefix -> Rel -> Prefix -> DependencySet -> Relations
insertRelation rels p1 r p2 ds =
 let
  outr = outRel rels
  inr  = inRel rels
  outRel_
   = case I.lookup p1 outr of
      Nothing       -> I.insert p1 (I.singleton r [(p2,ds)]) outr
      Just inner
        -> case I.lookup r inner of
             Nothing        -> I.insert p1 (I.insert r [(p2,ds)] inner)           outr
             Just innerList -> I.insert p1 (I.insert r ((p2,ds):innerList) inner) outr
  inRel_
   = case I.lookup p2 inr of
      Nothing       -> I.insert p2 (I.singleton r [(p1,ds)]) inr
      Just inner
        -> case I.lookup r inner of
            Nothing        -> I.insert p2 (I.insert r [(p1,ds)] inner)           inr
            Just innerList -> I.insert p2 (I.insert r ((p1,ds):innerList) inner) inr
 in
   Relations {outRel = outRel_ , inRel = inRel_ }


mergePrefixes :: Relations -> Prefix -> Prefix -> DependencySet -> Relations
mergePrefixes r pr ur _ | pr == ur = r
mergePrefixes r pr ur ds
 = let outRel_ = D.moveInnerDataDMapPlusDeps ds (outRel r) pr ur
       inRel_  = D.moveInnerDataDMapPlusDeps ds (inRel  r) pr ur
   in Relations { outRel = outRel_ , inRel = inRel_ }

instance Show Relations where
 show r = "\nRelations: " ++
            prettyShowMap_ (outRel r)
                           (\v -> "(" ++ prettyShowMap_rel_bps_x v ++ ")") "\n "

prettyShowMap_ :: (Show y) => IntMap y -> (y -> String) -> String -> String
prettyShowMap_ dasMap valueShow separator
 = List.intercalate separator $ map (\(k,v) -> show k ++ " -> " ++ valueShow v)
          $ I.toList dasMap

prettyShowMap_rel_bps_x :: (Show a) => IntMap {- Rel -} [(a,DependencySet)] -> String
prettyShowMap_rel_bps_x m
 = List.intercalate ", "
      $ map (\(r,x_bp_s) -> (++) ("-" ++ show r ++ "-> ") $ List.intercalate ", "
                  $ map (\(x,bp) -> show x ++ " " ++ dsShow bp) x_bp_s )
      $ I.toList m
