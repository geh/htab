module HTab.Relations

( Relations(..), emptyRels, insertRelation, mergePrefixWith,
  successors, predecessors, incomingLinks, outgoingLinks,
  allRels, null, linksFromTo )

where

--
-- enable quick access to outgoing and incoming links of a prefix
--

import qualified Data.Map as Map
import Data.Map ( Map )
import qualified Data.Set as Set
import Data.Set ( Set )
import qualified Data.IntSet as IntSet

import qualified HTab.DMap as DMap
import HTab.DMap ( DMap(..) )

import HTab.Formula (Prefix, Rel, DependencySet, dsUnion )
import Prelude hiding (id, pred, succ, null)

type Id = (Prefix,Rel,Prefix)
type IdToData = Map Id DependencySet
type InOutRel = DMap Prefix Rel (Set Prefix, Set Prefix)

data Relations = Relations { idToData :: IdToData,
                             inOutRel :: InOutRel }

instance Show Relations where
  show rels = concat  [ show p1 ++ "-R" ++ show rel ++ "->" ++ show (p2,bprs) ++ " "
                                        | ((p1,rel),(_,outs))  <- DMap.flatten $ inOutRel rels,
                                           not $ Set.null outs,
                                           let outs_l = Set.toList outs,
                                           p2 <- outs_l,
                                           let bprs = IntSet.toList $ (Map.!) (idToData rels) (p1,rel,p2) ]

emptyRels :: Relations
emptyRels = Relations { idToData = Map.empty,
                        inOutRel = DMap.empty }

null :: Relations -> Bool
null r = Map.null (idToData r)

allRels :: Relations -> [(Prefix,Rel,Prefix)]
allRels rels = Map.keys (idToData rels)

tMap2 :: (a -> b -> c) -> (a,a) -> (b,b) -> (c,c)
tMap2 f (a1,a2) (b1,b2) = (f a1 b1, f a2 b2)

insertRelation :: Relations -> Prefix -> Rel -> Prefix -> DependencySet -> Relations
insertRelation rels p1 r p2 ds =
 let id = (p1,r,p2) in
  case Map.lookup id (idToData rels) of
   Nothing -> let inOutRel'  = DMap.insertWith (tMap2 Set.union) p1 r (Set.empty, Set.singleton p2) (inOutRel rels)
                  inOutRel'' = DMap.insertWith (tMap2 Set.union) p2 r (Set.singleton p1, Set.empty) inOutRel'
              in
              rels{idToData = Map.insert id ds (idToData rels),
                   inOutRel = inOutRel''  }
   Just _  -> rels{idToData = Map.adjust (\ds_ -> dsUnion ds ds_) id (idToData rels)}

mergePrefixWith :: Relations -> Prefix -> Prefix -> DependencySet ->Relations
mergePrefixWith rels pr ur newDs =
 if ur == pr then rels
   else 
    case DMap.lookup1 pr (inOutRel rels) of
     Nothing                       -> rels
     Just inner_pr                 -> updateRtiItr rels pr inner_pr pr ur newDs

updateRtiItr :: Relations -> Prefix -> Map Rel (Set Prefix, Set Prefix) -> Prefix -> Prefix -> DependencySet -> Relations
updateRtiItr rels p1 p1_inOutMap pr ur newDs =
 let out_ids = concatMap ( \(r,(_,outs)) -> map (\o -> (r,o)) $ Set.toList outs) $ Map.assocs p1_inOutMap

     adjust_out :: (Rel,Prefix) -> (IdToData,InOutRel) -> (IdToData,InOutRel)
     adjust_out (r,p2) input@(idToData_,inOutRels_)
        = case Map.lookup id idToData_ of
           Nothing -> input
           Just ds ->
            let itd'  = Map.delete id idToData_
                itd'' = Map.insertWith dsUnion (ur,r,p2) (dsUnion ds newDs) itd'
                ior'  = replaceIn inOutRels_ p2 r p1 ur
                ior'' = addNewOut ior'     ur r p2
            in
                (itd'', ior'')
          where id = (p1,r,p2)

     in_ids  = concatMap ( \(r,(ins,_)) -> map (\i -> (i,r)) $ Set.toList ins) $ Map.assocs p1_inOutMap

     adjust_in :: (Prefix,Rel) -> (IdToData,InOutRel) -> (IdToData,InOutRel)
     adjust_in (p0,r) input@(idToData_,inOutRels_)
        = case Map.lookup id idToData_ of
           Nothing -> input
           Just ds ->
            let itd'  = Map.delete id idToData_
                itd'' = Map.insertWith dsUnion (p0,r,ur) (dsUnion ds newDs) itd'
                ior'  = replaceOut inOutRels_ p0 r p1 ur
                ior'' = addNewIn ior'      ur r p0
            in
              (itd'',ior'')
           where id = (p0,r,p1)

     (idToData' , inOutRels')  = foldr adjust_out (idToData rels, inOutRel rels)  out_ids
     (idToData'', inOutRels'') = foldr adjust_in  (idToData',        inOutRels')  in_ids

     inOutRels''' = DMap.delete pr inOutRels''

     in 

     rels{idToData = idToData'',
          inOutRel = inOutRels''' }


addNewOut :: InOutRel -> Prefix -> Rel -> Prefix -> InOutRel
addNewOut ior pr rel pOut
 = DMap.insertWith (tMap2 Set.union) pr rel (Set.empty,Set.singleton pOut) ior

addNewIn :: InOutRel -> Prefix -> Rel -> Prefix -> InOutRel
addNewIn ior pr rel pIn
 = DMap.insertWith (tMap2 Set.union) pr rel (Set.singleton pIn,Set.empty) ior

replaceIn :: InOutRel -> Prefix -> Rel -> Prefix -> Prefix -> InOutRel
replaceIn ior p r pRemove pAdd
  = let (ins,outs) = (DMap.!) ior p r
        ins_ = Set.insert pAdd $ Set.delete pRemove ins in
   DMap.insert p r (ins_,outs) ior

replaceOut :: InOutRel -> Prefix -> Rel -> Prefix -> Prefix -> InOutRel
replaceOut ior p r pRemove pAdd
  = let (ins,outs) = (DMap.!) ior p r
        outs_ = Set.insert pAdd $ Set.delete pRemove outs in
   DMap.insert p r (ins,outs_) ior


successors :: Relations -> Prefix -> Rel -> [(Prefix, DependencySet)]
successors rels p r
 = case DMap.lookup p r (inOutRel rels) of
    Nothing        -> []
    Just (_,succs) -> (`map` Set.toList succs) $ \succ -> let ds = (Map.!) (idToData rels) (p,r,succ) in (succ, ds)

outgoingLinks :: Relations -> Prefix -> [(Rel, [(Prefix, DependencySet)])]
outgoingLinks rels p
 = case Map.lookup p (DMap.toMap $ inOutRel rels) of
    Nothing    -> []
    Just rToId -> [ (r,p_ds_s) | (r,(_,succs)) <- Map.assocs rToId,
                                 let p_ds_s = [(succ,ds) | succ <- Set.toList succs, let ds = (Map.!) (idToData rels) (p,r,succ)]
                  ]

predecessors :: Relations -> Prefix -> Rel -> [(Prefix, DependencySet)]
predecessors rels p r
 = case DMap.lookup p r (inOutRel rels) of
    Nothing        -> []
    Just (preds,_) -> (`map` Set.toList preds) $ \pred -> let ds = (Map.!) (idToData rels) (pred,r,p) in (pred, ds)


incomingLinks :: Relations -> Prefix -> [(Rel,[( Prefix, DependencySet)])]
incomingLinks rels p
 = case Map.lookup p (DMap.toMap $ inOutRel rels) of
    Nothing     -> []
    Just rToId -> [ (r,p_ds_s) | (r,(preds,_)) <- Map.assocs rToId,
                                 let p_ds_s = [(pred,ds) | pred <- Set.toList preds, let ds = (Map.!) (idToData rels) (pred,r,p)]
                  ]


linksFromTo :: Relations -> Prefix -> Prefix -> [Rel]
linksFromTo rels p1 p2
 = map fst $ filter (\(_,p_d_s) -> p2 `elem` (map fst p_d_s) ) outs
    where outs = outgoingLinks rels p1
