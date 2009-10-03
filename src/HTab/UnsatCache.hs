module HTab.UnsatCache 
( update, query )
where

import Control.Monad ( when )
import Control.Monad.State(put, get)
import Control.Applicative ( (<$>) )
import qualified HTab.DMap as DMap
import qualified Data.Map as Map
import qualified Data.Bimap as Bimap
import qualified Data.Set as Set

import Data.Maybe( fromJust )
import Data.List
import HTab.Formula
import HTab.Branch(BranchInfo(..),Branch(..),BranchMonad, BranchData(..),
                   UCache(..),UCMap,CacheStructure(..),
                   Univ_constraints,AugmentedPrefixes,
                   getUrfather,
                   search_disjunctPrefixes)
import qualified HTab.DisjSet as DS

update :: Prefix -> Branch -> BranchMonad ()
update pr br =
 do bd <- get
    let ur = getUrfather br $ DS.Prefix pr
    let invalid_prefixes = nub $ prevPref br
    let add_cache = search_disjunctPrefixes pr (disjunctPrefixes bd)
                    && (pr `notElem` invalid_prefixes )
    when add_cache $ put bd{unsat_cache = updateOne ur br (unsat_cache bd)}
                                                                        
updateOne :: Prefix -> Branch -> UCache -> UCache
updateOne pr br UCache{bimap = bm, cache = c} =
 let localForms   = DMap.lookupInter pr $ trueForms br

     univForms1   = fst $ get_univ_forms (univCons br)
     univForms    = map A univForms1

     noms         = getNoms (localForms ++ univForms1)
     nominalForms = fst $ get_nominal_forms noms br

     cacheForms = localForms ++ univForms ++ nominalForms

     (indexes,newBimap) = updateBimap bm cacheForms
 in
      UCache{ bimap  = newBimap,
              cache  = insertCache (Set.fromList indexes) c }

-- get the set of formulas true at the nominals appearing in the formulas to be cached
getNoms :: [Formula]-> [NomSymbol]
getNoms fs = Set.toList $ Set.unions $ map (fst . extractNominals ) fs

get_nominal_forms:: [NomSymbol] -> Branch -> ([Formula],DependencySet)
get_nominal_forms noms br = 
 foldr merge ([],dsEmpty) $ map get_nominal_forms_one noms 
 where merge (fs1,ds1) (fs2,ds2) = (fs1 ++ fs2, dsUnion ds1 ds2)

       get_nominal_forms_one n = 
        let ur  = getUrfather br $ DS.Nominal (showNom n)
            btf = Map.lookup ur $ DMap.toMap $ trueForms br
            (btf_list,dps) = case btf of
                               Nothing     -> ([], dsEmpty)
                               Just btfSet -> (Map.keys btfSet, dsUnions $ Map.elems btfSet)
        in (map (At n) btf_list, dps)


-- get the universally constrained formulas
get_univ_forms :: Univ_constraints -> ([Formula],DependencySet)
get_univ_forms ucs = ( map snd ucs, dsUnions $ map fst ucs )

query :: Branch -> UCache -> BranchInfo
query br uc  = query_ (nub (incrPrs br)) br uc

query_ :: AugmentedPrefixes -> Branch -> UCache -> BranchInfo
query_ (p:ps) br uc =
 case query_pr p br uc  of
     b@(BranchClash _ _ _ _) -> b
     BranchOK _              -> query_ ps br uc

query_ [] br _ = BranchOK br

query_pr :: Prefix -> Branch -> UCache -> BranchInfo
query_pr pr br UCache{bimap = bm, cache = c} =
 let  localForms   = DMap.lookupInter pr $ trueForms br

      univForms1   = fst $ get_univ_forms (univCons br)
      univForms    = map A univForms1

      noms         = getNoms (localForms ++ univForms1)
      nominalForms = fst $ get_nominal_forms noms br

      cacheForms = localForms ++ univForms ++ nominalForms
 in
      case ( do indexes <- Set.fromList <$> lookupBimap bm cacheForms
                queryCache indexes c   ) of
       Nothing     -> BranchOK br
       Just newIdx ->
                let new_form_list = get_new_formula_list bm newIdx
                    dps           = get_dps br pr new_form_list
                in
                  BranchClash br pr dps (neg taut)


-- receives the list of indexes of formulas in the cache, and the bidirectional map,
-- and returns the list of formulas corresponding to this list of indexes
get_new_formula_list :: UCMap -> [Int] -> [Formula]
get_new_formula_list inv_desc = map (\i -> fromJust $ Bimap.lookupR i inv_desc)


--to get the dependency set corresponding to a list of UCFormulas
get_dps :: Branch -> Prefix -> [Formula] -> DependencySet
get_dps br pr
 = dsUnions . map get_dps_one

   where get_dps_one (A f)
          =  dsUnion (get_dps_local (A f))
                     ( case lookup_ f (univCons br) of
                          Nothing -> dsEmpty
                          Just dps -> dps              )

         get_dps_one (At n f)
           = let ur = getUrfather br $ DS.Nominal $ showNom n
                 dn = case DMap.lookup ur f (trueForms br) of
                         Nothing -> dsEmpty
                         Just d -> d
             in dsUnion dn (get_dps_local (At n f))

         get_dps_one f = get_dps_local f

         get_dps_local f
            = case DMap.lookup pr f (trueForms br) of
                  Nothing -> dsEmpty
                  Just d -> d

         lookup_ f = (lookup f) . (map switch)
         switch (x,y) = (y,x)


-- Formula <-> Idx mapping

updateBimap :: UCMap -> [Formula] -> ([Int],UCMap)
updateBimap bmap fs =
 foldr  (\f (currentIdxs,currentMap)
            -> let (idx,newMap) = get_index currentMap f
               in  ((idx:currentIdxs), newMap)
        )
        ([],bmap) fs

get_index :: UCMap -> Formula -> (Int,UCMap)
get_index bmap f =
 case Bimap.lookup f bmap of
    Just i  -> (i, bmap)
    Nothing -> (newIdx,newBimap)
                where newIdx   = 1 + ( fst $ Bimap.findMaxR bmap )
                      newBimap = Bimap.insert f newIdx bmap

lookupBimap :: UCMap -> [Formula] -> Maybe [Int]
lookupBimap bmap fs =
 foldr  (\f mList
            -> case mList of
                Nothing -> Nothing
                Just is -> case Bimap.lookup f bmap of { Just i -> Just (i:is) ; Nothing -> Nothing }
        )
        (Just []) fs

