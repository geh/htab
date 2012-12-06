module HTab.Relations

( OutRels, emptyRels, insertRelation, mergePrefixes,
  successors, allRels, null, linksFromTo,
  showRels )

where

import qualified Data.IntMap as I
import Data.IntMap ( IntMap )
import qualified Data.Map as M
import Data.Map ( Map )

import qualified Data.List as List

import qualified HTab.DMap as D
import HTab.DMap ( DMap )

import HTab.Formula (Prefix, Rel, DependencySet, dsShow )
import Prelude hiding (id, pred, succ, null)

type OutRels = DMap {- Prefix Rel -} [(Prefix,DependencySet)]

emptyRels :: OutRels
emptyRels = D.empty

null :: OutRels -> Bool
null = I.null

allRels :: OutRels -> [(Prefix,Rel,Prefix)]
allRels rels = [ (p1,r,p2) | (p1,r,ds_out_s) <-  D.flatten rels,
                             (p2,_) <- ds_out_s ]

linksFromTo :: OutRels -> Prefix -> Prefix -> [Rel]
linksFromTo rels p1 p2
  = List.nub [ r | (pa,r,pb) <- allRels rels, pa == p1, pb == p2]

successors :: OutRels -> Prefix -> Map Rel [(Prefix,DependencySet)]
successors rels p = I.findWithDefault M.empty p rels

-- assumes you never add twice the same relation
insertRelation :: OutRels -> Prefix -> Rel -> Prefix -> DependencySet -> OutRels
insertRelation rels p1 r p2 ds =
  case I.lookup p1 rels of
      Nothing       -> I.insert p1 (M.singleton r [(p2,ds)]) rels
      Just inner
        -> case M.lookup r inner of
             Nothing        -> I.insert p1 (M.insert r [(p2,ds)] inner)           rels
             Just innerList -> I.insert p1 (M.insert r ((p2,ds):innerList) inner) rels


mergePrefixes :: OutRels -> Prefix -> Prefix -> DependencySet -> OutRels
mergePrefixes r pr ur _ | pr == ur = r
mergePrefixes r pr ur ds = D.moveInnerPlusDeps ds r pr ur

showRels :: OutRels -> String
showRels r = prettyShowMap_ r (\v -> "(" ++ prettyShowMap_rel_bps_x v ++ ")") "\n "

prettyShowMap_ :: (Show y) => IntMap y -> (y -> String) -> String -> String
prettyShowMap_ m valueShow separator
 = List.intercalate separator $ map (\(k,v) -> show k ++ " -> " ++ valueShow v)
          $ I.toList m

prettyShowMap_rel_bps_x :: (Show a) => Map Rel [(a,DependencySet)] -> String
prettyShowMap_rel_bps_x m
 = List.intercalate ", "
      $ map (\(r,x_bp_s) -> (++) ("-" ++ r ++ "-> ") $ List.intercalate ", "
                  $ map (\(x,bp) -> show x ++ " " ++ dsShow bp) x_bp_s )
      $ M.toList m
