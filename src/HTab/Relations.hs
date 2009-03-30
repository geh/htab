module HTab.Relations

( Relations(..), emptyRels, insertRelation, mergePrefixWith,
  getSuccessors, getPredecessors, getIncomingLinks, getOutgoingLinks,
  getAllRels, showPretty ) 

where

--
-- enable quick access to outgoing and incoming links, given a prefix
--

import Data.Map ( Map )
import qualified Data.Map as Map

import HTab.DMap ( DMap(..) )
import qualified HTab.DMap as DMap

import Data.IntSet  (IntSet )
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import HTab.Formula (Prefix, Rel, DependencySet, dsUnion, dsUnions )

import Prelude hiding (id, pred, succ)

type Id = Int
type Ids = IntSet
type RelToId = Map (Prefix,Rel,Prefix) Id
type IdToRel = Map Id (Prefix,Rel,Prefix,DependencySet)
type InOutRel = DMap Prefix Rel (Ids,Ids)

data Relations = Relations { relToId :: RelToId,
                             idToRel :: IdToRel,
                            inOutRel :: InOutRel }
 deriving (Show)


showPretty :: Relations -> String
showPretty rels = concat  [ show p1 ++ "-R" ++ show rel ++ "->" ++ show (p2,bprs) ++ " "
                                              | ((p1,rel),(_,outs))  <- DMap.flattenDMap $ inOutRel rels,
                                                 let outs_l = IntSet.toList outs,
                                                 not $ null outs_l,
                                                 id <- outs_l,
                                                 let (_,_,p2,bprs_) = (Map.!) (idToRel rels) id,
                                                 let bprs = IntSet.toList bprs_] 

emptyRels :: Relations
emptyRels = Relations { relToId = Map.empty,
                        idToRel = Map.empty,
                        inOutRel = DMap.empty }

getAllRels :: Relations -> [(Prefix,Rel,Prefix)]
getAllRels rels = Map.keys (relToId rels)

getNewId :: Relations -> Id
getNewId rels = case Set.maxView $ Map.keysSet $ idToRel rels of
                   Nothing     -> 0
                   Just (i,_)  -> i+1

tMap2 :: (a -> b -> c) -> (a,a) -> (b,b) -> (c,c)
tMap2 f (a1,a2) (b1,b2) = (f a1 b1, f a2 b2)

insertRelation :: Relations -> Prefix -> Rel -> Prefix -> DependencySet -> Relations
-- check if already here
insertRelation rels p1 r p2 ds =
 case Map.lookup (p1,r,p2) (relToId rels) of
  Nothing -> rels{relToId = Map.insert (p1,r,p2) id         (relToId rels),
                  idToRel = Map.insert id (p1,r,p2,ds)      (idToRel rels),
                  inOutRel = inOutRel''  }
               where id = getNewId rels
                     inOutRel'  = DMap.insertWith (tMap2 IntSet.union) p1 r (IntSet.empty, IntSet.singleton id) (inOutRel rels)
                     inOutRel'' = DMap.insertWith (tMap2 IntSet.union) p2 r (IntSet.singleton id, IntSet.empty) inOutRel'
  Just id -> rels{idToRel = Map.adjust (\(p1_,r_,p2_,ds_) -> (p1_,r_,p2_,dsUnion ds ds_)) id (idToRel rels)}


mergePrefixWith :: Relations -> Prefix -> Prefix -> DependencySet ->Relations
mergePrefixWith rels pr ur newDs =
-- ur = getUrfather p (stop if ur=p)
-- outrel + inrels -> get all ids  through all relations
-- for a given id, remov the rel  (  1) 2) 3) 4) ) , add the new rel ( 1) 2) 3) 4) )
 if ur == pr then rels
   else 
    case DMap.lookup1 pr (inOutRel rels) of
     Nothing                       -> rels
     Just inner_pr                 -> updateRtiItr rels inner_pr pr ur newDs

updateRtiItr :: Relations -> Map Rel (Ids,Ids) -> Prefix -> Prefix -> DependencySet -> Relations -- idToRel , relToId
-- when there is no risk of ecrasement of relation
updateRtiItr rels m1 {- inOutId for the originating prefix-} pr ur newDs =
 let out_ids  = IntSet.toList $ IntSet.unions $ map snd $ Map.elems m1

     adjust_out :: Id -> (IdToRel,RelToId,InOutRel) -> (IdToRel,RelToId,InOutRel)
     adjust_out id input@(idToRels_,relToIds_,inOutRels_)
        = case Map.lookup id idToRels_ of
           Nothing             -> input   -- in the case of a reflexive link, if it has already been removed by the "adjust_in" function
           Just (p1,r,p2,ds) ->
            let itr'  = Map.delete id idToRels_
                rti'  = Map.delete (p1,r,p2) relToIds_
            in
             case Map.lookup (ur,r,p2) relToIds_ of
               Nothing -> let  itr'' = Map.insert id (ur,r,p2,dsUnion ds newDs) itr'
                               rti'' = Map.insert (ur,r,p2) id rti'
                          in   (itr'', rti'',addNewOut inOutRels_ ur r id)

               Just id_ur -> let (_,_,_,ds2) = (Map.!) idToRels_ id_ur
                                 itr'' = Map.insert id_ur (ur,r,p2,dsUnions [ds,ds2,newDs]) itr'
                             in  (itr'',rti',removeIn inOutRels_ p2 r id)


     in_ids  = IntSet.toList $ IntSet.unions $ map fst $ Map.elems m1

     adjust_in :: Id -> (IdToRel,RelToId,InOutRel) -> (IdToRel,RelToId,InOutRel)
     adjust_in id input@(idToRels_,relToIds_,inOutRels_)
        = case Map.lookup id idToRels_ of
           Nothing             -> input
           Just (p1,r,p2,ds) ->
            let itr'  = Map.delete id idToRels_
                rti'  = Map.delete (p1,r,p2) relToIds_
            in
             case Map.lookup (p1,r,ur)  relToIds_ of
               Nothing -> let  itr'' = Map.insert id (p1,r,ur,dsUnion ds newDs) itr'
                               rti'' = Map.insert (p1,r,ur) id rti'
                          in   (itr'', rti'',addNewIn inOutRels_ ur r id)

               Just id_ur -> let (_,_,_,ds2) = (Map.!) idToRels_ id_ur
                                 itr'' = Map.insert id_ur (p1,r,ur,dsUnions [ds,ds2,newDs]) itr'
                             in  (itr'',rti',removeOut inOutRels_ p1 r id)


     (idToRels' ,relToIds' , inOutRels')  = foldr adjust_out (idToRel rels,relToId rels,inOutRel rels)  out_ids
     (idToRels'',relToIds'', inOutRels'') = foldr adjust_in  (idToRels',   relToIds',   inOutRels')  in_ids

     inOutRels''' = DMap.delete pr inOutRels''

     in 

     rels{idToRel = idToRels'',
          relToId = relToIds'',
          inOutRel = inOutRels''' }


addNewOut :: InOutRel -> Prefix -> Rel -> Id -> InOutRel
addNewOut ior pr rel id
 = DMap.insertWith (tMap2 IntSet.union) pr rel (IntSet.empty,IntSet.singleton id) ior


addNewIn :: InOutRel -> Prefix -> Rel -> Id -> InOutRel
addNewIn ior pr rel id
 = DMap.insertWith (tMap2 IntSet.union) pr rel (IntSet.singleton id,IntSet.empty) ior

removeOut :: InOutRel -> Prefix -> Rel -> Id -> InOutRel
removeOut ior p r id
 = let (ins,outs) = (DMap.!) ior p r
       outs_ = IntSet.delete id outs    in
   DMap.insert p r (ins,outs_) ior

removeIn :: InOutRel -> Prefix -> Rel -> Id -> InOutRel
removeIn ior p r id
 = let (ins,outs) = (DMap.!) ior p r
       ins_ = IntSet.delete id ins      in
   DMap.insert p r (ins_,outs) ior


getSuccessors :: Relations -> Prefix -> Rel -> [(Prefix, DependencySet)]
getSuccessors rels p r
 = case DMap.lookup p r (inOutRel rels) of
    Nothing      -> []
    Just (_,ids) -> (`map` IntSet.toList ids) $ \id -> let (_,_,succ,ds) = (Map.!) (idToRel rels) id in (succ, ds)

getOutgoingLinks :: Relations -> Prefix -> [(Rel, [(Prefix, DependencySet)])]
getOutgoingLinks rels p
 = case Map.lookup p (DMap.toMap $ inOutRel rels) of
    Nothing    -> []
    Just rToId -> [ (r,p_ds_s)        | (r,(_,ids)) <- Map.assocs rToId,
                                        let p_ds_s = [(succ,ds) | id <- IntSet.toList ids, let (_,_,succ,ds) = (Map.!) (idToRel rels) id]
                  ]

getPredecessors :: Relations -> Prefix -> Rel -> [(Prefix, DependencySet)]
getPredecessors rels p r
 = case DMap.lookup p r (inOutRel rels) of
    Nothing      -> []
    Just (ids,_) -> (`map` IntSet.toList ids) $ \id -> let (pred,_,_,ds) = (Map.!) (idToRel rels) id in (pred, ds)


getIncomingLinks :: Relations -> Prefix -> [(Rel,[( Prefix, DependencySet)])]
getIncomingLinks rels p
 = case Map.lookup p (DMap.toMap $ inOutRel rels) of
    Nothing     -> []
    Just rToId -> [ (r,p_ds_s)        | (r,(ids,_)) <- Map.assocs rToId,
                                        let p_ds_s = [(pred,ds) | id <- IntSet.toList ids, let (pred,_,_,ds) = (Map.!) (idToRel rels) id]
                  ]

