module HTab.UnsatCache 
(update_cache,search_cache,CachingInstance(..))
where

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
                   del_pref_disjunctPrefixes, search_disjunctPrefixes)
import qualified HTab.DisjSet as DS

data CachingInstance = Cclash | Cdisjunct deriving Show

------------update--------------------------------
--given the input prefix, get the parents and call to update cache 
update_cache :: Prefix -> Branch -> CachingInstance -> BranchMonad BranchData
--when calling from a clash, don't add into the cache the info from the clashing prefix
update_cache pr1 br Cclash =
 do bd <- get
    let invalid_prefixes = nub $ prevPref br
    let new_disPr = del_pref_disjunctPrefixes br pr1 (disjunctPrefixes bd)
    case Map.lookup pr1 (prefParent br) of
          Nothing -> do put    bd{disjunctPrefixes = new_disPr}
                        return bd{disjunctPrefixes = new_disPr}
          Just p -> if not $ elem p invalid_prefixes
                      then do let new_uc = update_cache_prefixes p br (unsat_cache bd) invalid_prefixes
                              put    bd{unsat_cache = new_uc, disjunctPrefixes = new_disPr}
                              return bd{unsat_cache = new_uc, disjunctPrefixes = new_disPr}
                      else do put    bd{disjunctPrefixes = new_disPr}
                              return bd{disjunctPrefixes = new_disPr}

--when calling after backtracking from the application of a disjunct rule, add the info from the first prefix
update_cache pr1  br Cdisjunct =
 do bd <- get
    let pr = getUrfather br $ DS.Prefix pr1
    let add_cache = search_disjunctPrefixes pr1 (disjunctPrefixes bd)
    let invalid_prefixes = nub (prevPref br)
    if add_cache && (not $ elem pr1 invalid_prefixes )
     then
       do let n_uc = update_cache_ pr br (unsat_cache bd)
          case Map.lookup pr1 (prefParent br) of
                Nothing -> return bd{unsat_cache = n_uc}
                Just p -> if not $ elem p invalid_prefixes
                            then do let new_new_uc = update_cache_prefixes p br n_uc invalid_prefixes
                                    put    bd{unsat_cache = new_new_uc}
                                    return bd{unsat_cache = new_new_uc}
                            else do put    bd{unsat_cache = n_uc}
                                    return bd{unsat_cache = n_uc}
      else return bd

                                                                        
update_cache_prefixes :: Prefix -> Branch -> UCache-> [Prefix] -> UCache
update_cache_prefixes pr br uc notvps=
 let u_pr   = getUrfather br $ DS.Prefix pr
     new_uc = update_cache_ u_pr br uc
 in case Map.lookup pr (prefParent br) of
       Nothing -> new_uc
       Just p -> if not $ elem p notvps
                  then update_cache_prefixes p br new_uc notvps
                  else new_uc

update_cache_ :: Prefix -> Branch -> UCache -> UCache
update_cache_ pr br UCache{bimap = bm, cache = c} =
 let -- See what formulas we cache
     localForms   = DMap.lookupInter pr $ trueForms br

     univForms1   = fst $ get_univ_forms (univCons br)
     univForms    = map A univForms1

     noms         = getNoms (localForms ++ univForms1)
     nominalForms = fst $ get_nominal_forms noms br

     cacheForms = localForms ++ univForms ++ nominalForms -- formulas to be cached

     -- Update the Formula <-> Int BiMap
     (indexes,newBimap) = updateBimap bm cacheForms

 in
      UCache{ bimap  = newBimap,
              cache  = insertCache (Set.fromList indexes) c }

--get the set of formulas true at the nominals appearing in the formulas to be cached
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


--to get the universally constrained formulas
get_univ_forms :: Univ_constraints -> ([Formula],DependencySet)
get_univ_forms ucs = ( map snd ucs, dsUnions $ map fst ucs )

---------------------------------------------------------------------------
--------------------------------search------------------------------------
---------------------------------------------------------------------------

--for each branch, we will only look for a cache hit in the new prefixes introduced by the branch,
--this value is stored in the field incrPrs :: AugmentedPrefixes, in the branch.

--idea: to create, for each prefix, a list of indexes consisting in the non universal formulas
--         true at that prefix, plus the universal formulas true at that prefix.
--        Then, check if this indexes list is a superset of some row in the matrix
--        if it is -> we have a cache hit, and the branch is unsat
--        if not -> go on working with the branch

search_cache :: Branch -> BranchData -> BranchInfo
search_cache br bd  = search_cache_ (nub (incrPrs br)) br bd

search_cache_ :: AugmentedPrefixes -> Branch -> BranchData -> BranchInfo
search_cache_ (pr:tail_pr) br bd =
 case search_cache_pr pr br bd  of
     b@(BranchClash _ _ _ _) -> b
     BranchOK _              -> search_cache_ tail_pr br bd

search_cache_ [] _ bd = branch_info bd

search_cache_pr :: Prefix -> Branch -> BranchData -> BranchInfo
search_cache_pr pr br bd =
 let  localForms   = DMap.lookupInter pr $ trueForms br

      univForms1   = fst $ get_univ_forms (univCons br)
      univForms    = map A univForms1

      noms         = getNoms (localForms ++ univForms1)
      nominalForms = fst $ get_nominal_forms noms br

      cacheForms = localForms ++ univForms ++ nominalForms -- formulas to be cached
  in
      case unsat_cache bd of
       UCache{bimap = bm,
              cache = c}
        ->
         case ( do indexes <- Set.fromList <$> lookupBimap bm cacheForms
                   queryCache indexes c   ) of
          Nothing     -> branch_info bd
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

