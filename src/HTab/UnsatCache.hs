module HTab.UnsatCache 
(update_cache,search_cache,CachingInstance(..))
where

import Control.Monad.State(put, get)
import qualified HTab.DMap as DMap
import qualified Data.Map as Map
import qualified Data.Bimap as Bimap
import Data.Set ( Set )
import qualified Data.Set as Set

import Data.Maybe()
import Data.List
import HTab.UCMatrix
import HTab.UCList
import HTab.Formula
import HTab.CommandLine ( Caching(..) )
import HTab.Branch(BranchInfo(..),Branch(..),BranchMonad, BranchData(..),
                   UCache(..),Univ_constraints,AugmentedPrefixes,UCMap,
                   getUrfather,
                   del_pref_disjunctPrefixes, search_disjunctPrefixes)
import qualified HTab.DisjSet as DS


--import Debug.Trace

data CachingInstance = Cclash | Cdisjunct deriving Show
---------------------------------------------------
--cache
--------------------------------------------------

------------update--------------------------------
--given the input prefix, get the parents and call to update cache 
update_cache :: Caching -> Prefix -> Branch -> CachingInstance -> BranchMonad BranchData
--when calling from a clash, don't add into the cache the info from the clashing prefix
update_cache approach pr1 br Cclash = 
                        do bd <- get
                           let uc = (unsat_cache bd)
                           let invalid_prefixes =  nub (prevPref br) --to allow just one repetition of each element
                           let old_disPr = (disjunctPrefixes bd)
                           let new_disPr = (del_pref_disjunctPrefixes  br pr1 old_disPr)
                           let ppr = Map.lookup pr1 (prefParent br) 
                           case ppr of
                                 Nothing -> do put bd{disjunctPrefixes = new_disPr}
                                               return bd{disjunctPrefixes = new_disPr}
                                 Just p -> if not (elem p invalid_prefixes )
                                             then do let new_uc = update_cache_prefixes approach p br uc invalid_prefixes
                                                     put bd{unsat_cache = new_uc,                                                       disjunctPrefixes = new_disPr}
                                                     return bd{unsat_cache = new_uc,                                                           disjunctPrefixes = new_disPr}
                                             else do put bd{disjunctPrefixes = new_disPr}
                                                     return bd{disjunctPrefixes = new_disPr}

--when calling after backtracking from the application of a disjunct rule, add the info from the first prefix
update_cache approach pr1  br Cdisjunct = 
               do bd <- get
                  let ds_pr =  (DS.Prefix pr1)
                  let pr = (getUrfather br ds_pr )
                  let d_p = (disjunctPrefixes bd)
                  let add_cache = (search_disjunctPrefixes pr1 d_p)
                  if add_cache 
                   then do let n_uc = update_cache_ approach pr br (unsat_cache bd)
                           let invalid_prefixes = nub (prevPref br) --to allow just one repetition of each element
                           let ppr =  Map.lookup pr1 (prefParent br) 
                           case ppr of
                                 Nothing -> return bd{unsat_cache = n_uc}
                                 Just p -> if not (elem p invalid_prefixes )
                                             then do let new_new_uc=
                                                             update_cache_prefixes approach p br n_uc invalid_prefixes
                                                     put bd{unsat_cache = new_new_uc}
                                                     return bd{unsat_cache = new_new_uc}
                                             else do put bd{unsat_cache = n_uc}
                                                     return bd{unsat_cache = n_uc}
                    else return bd
                           


                                                                        

update_cache_prefixes :: Caching -> Prefix -> Branch -> UCache-> [Prefix] -> UCache
update_cache_prefixes approach pr br uc notvps= 
                                    let ds_pr = DS.Prefix pr
                                        u_pr = (getUrfather br ds_pr )
                                        new_uc = update_cache_ approach u_pr br uc
                                        ppr = Map.lookup pr (prefParent br) 
                                    in case ppr of
                                          Nothing -> new_uc
                                          Just p -> if not (elem p notvps)
                                                        then update_cache_prefixes approach p br new_uc notvps
                                                        else new_uc

update_cache_ :: Caching -> Prefix -> Branch -> UCache-> UCache
update_cache_ MatrixCaching pr br uc =
                         let btf1 = Map.lookup pr (DMap.toMap (branchTrueForms br))
                             branchTrueForms1 = case btf1 of
                                                     Nothing -> []
                                                     Just btfSet -> Map.keys btfSet
                             (univForms1,_) = get_univ_forms (univCons br)
                             univForms = map UniversalC univForms1
                             nonUnivForms = map NonUniversalC (remove_univ branchTrueForms1 univForms1)
                             --nominal formulas
                             nomsF = getNoms branchTrueForms1
                             nomsU = getNoms univForms1
                             nomsFU = Set.union nomsF nomsU
                             noms = sort(Set.toList nomsFU)
                             (nominalForms,_) = get_nominal_forms noms br
                             --concatenat NonUniversalC, UniversalC and Nominal formulas
                             cacheForms = nonUnivForms ++ univForms ++ nominalForms
                             descMat = (descrip_matrix uc)
                             curr_i = (current_index uc)
                             (c_i, indexes,newMapDesc) =  get_indexes_list descMat cacheForms curr_i True
                             c_r = (current_row uc)
                             m_r = (max_row uc)
                             mat = (matrix uc)
                             sort_indexes = (sort (nub indexes))
                             (n_cr,new_matrix)= (update_matrix  c_i c_r m_r sort_indexes mat)
                         in uc{ descrip_matrix = newMapDesc,
                                current_index = c_i,
                                current_row = n_cr,
                                matrix = new_matrix}


update_cache_ ListCaching pr br uc =
                         let btf1 = Map.lookup pr (DMap.toMap (branchTrueForms br))
                             branchTrueForms1 = case btf1 of
                                                     Nothing -> []
                                                     Just btfSet -> Map.keys btfSet
                             nonUnivForms = map NonUniversalC (remove_univ branchTrueForms1 univForms1)
                             --UniversalC formulas
                             (univForms1,_) = get_univ_forms (univCons br)
                             univForms = map UniversalC univForms1
                             --nominal formulas
                             nomsF = getNoms branchTrueForms1
                             nomsU = getNoms univForms1
                             nomsFU = Set.union nomsF nomsU
                             noms = sort(Set.toList nomsFU)
                             (nominalForms,_) = get_nominal_forms noms br
                             --concatenat NonUniversalC, UniversalC and Nominal formulas
                             cacheForms = nonUnivForms ++ univForms ++ nominalForms
                             descMat = (descrip_matrix uc)
                             curr_i = (current_index uc)
                             (c_i, indexes,newMapDesc) =  get_indexes_list descMat cacheForms curr_i True
                             li = (listsList uc)
                             sort_indexes =  (sort (nub indexes))
                             new_list=  (update_list sort_indexes li)
                         in  uc{ descrip_matrix = newMapDesc,
                                 current_index = c_i,
                                 listsList = new_list}

--to get the set of formulas true at the nominals appearing in the formulas to be cached
getNoms ::[Formula]-> Set.Set NomSymbol
getNoms (f:rest)= 
        let (allNomsU,_) = extractNominals f
            restNoms = getNoms rest
        in Set.union allNomsU restNoms
getNoms [] = Set.empty

get_nominal_forms:: [NomSymbol] -> Branch -> ([UCFormula],DependencySet)
get_nominal_forms (n:rest) br = 
                let ds_n =  (DS.Nominal (showNom n))
                    uf_n = getUrfather br ds_n 
                    btf = Map.lookup uf_n (DMap.toMap (branchTrueForms br))
                    btf_list = case btf of
                                 Nothing -> []
                                 Just btfSet -> Map.keys btfSet
                    dps = case btf of
                                Nothing -> dsEmpty
                                Just btfSet -> dsUnions $ Map.elems btfSet
                    
                    btf_listNom = map (NominalC n) btf_list
                in (concat[btf_listNom,restBtf],dsUnion dps rest_dps)
                where (restBtf,rest_dps) = get_nominal_forms rest br
get_nominal_forms [] _ = ([],dsEmpty)


--to get the universally constrained formulas
get_univ_forms :: Univ_constraints -> ([Formula],DependencySet)
get_univ_forms ((dps,f):rest)= let (tail_u,tail_dps) = get_univ_forms rest
                               in ((f:tail_u),dsUnion dps tail_dps)
get_univ_forms []=([],dsEmpty)

remove_univ :: [Formula] -> [Formula] -> [Formula] 
remove_univ (nuf:tail_nuf) univ_forms =
        let is_univ = is_universal nuf univ_forms
            tail_new_nuf = remove_univ tail_nuf univ_forms
        in if is_univ 
             then tail_new_nuf
             else (nuf:tail_new_nuf)
remove_univ [] _ = []

is_universal :: Formula -> [Formula] -> Bool 
is_universal (A _) _ = True
is_universal form (uf:utail) = 
        if form == uf
        then True
        else is_universal form utail
is_universal _ [] = False

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

search_cache :: Caching -> Branch -> BranchData -> BranchInfo
search_cache caching br bd  =
                      let not_repeted_incrPrs = nub (incrPrs br)
                      in search_cache_ caching not_repeted_incrPrs br bd

--to iterate over the list of prefixes
search_cache_ :: Caching -> AugmentedPrefixes -> Branch -> BranchData -> BranchInfo
search_cache_ caching (pr:tail_pr) br bd =
                                   let res = search_cache_pr caching pr br bd 
                                   in case res  of
                                        b@(BranchClash _ _ _ _) -> b
                                        BranchOK _ ->search_cache_ caching tail_pr br bd
                                                        
search_cache_ _ [] _ bd = (branch_info bd)

--to detect a cache hit for a prefix and a branch
search_cache_pr :: Caching -> Prefix -> Branch -> BranchData -> BranchInfo
search_cache_pr MatrixCaching pr br bd
                          = let btf1 = Map.lookup pr (DMap.toMap (branchTrueForms br))
                                branchTrueForms1 = case btf1 of
                                                        Nothing -> []
                                                        Just btfSet -> Map.keys btfSet
                                (univForms1,_) = get_univ_forms (univCons br)
                                univForms = map UniversalC univForms1
                                nonUnivForms = map NonUniversalC (remove_univ branchTrueForms1 univForms1)
                                --nominal formulas
                                nomsF = getNoms branchTrueForms1
                                nomsU = getNoms univForms1
                                nomsFU = Set.union nomsF nomsU
                                noms = sort(Set.toList nomsFU)
                                (nominalForms,_) = get_nominal_forms noms br
                                --concatenat NonUniversalC, UniversalC and Nominal formulas
                                cacheForms = nonUnivForms ++ univForms ++ nominalForms
                                us = (unsat_cache bd)
                                c_i = (current_index us)
                                m_r = (max_row us)
                                mat = (matrix us)
                                de = (descrip_matrix us)
                                (_, indexes,_) = get_indexes_list de cacheForms c_i False
                                sort_indexes = (sort(nub indexes))
                            in if do_search sort_indexes
                                  then let r = (superset_matching 0 m_r c_i sort_indexes mat)
                                       in case r of
                                               Nothing      -> (branch_info bd)
                                               Just new_ind -> let new_form_list = get_new_formula_list  new_ind de
                                                                   dps = get_dps new_form_list br pr
                                                               in (BranchClash br pr dps (neg taut))
                                  else (branch_info bd)

search_cache_pr ListCaching pr br bd
                          = let btf1 = Map.lookup pr (DMap.toMap (branchTrueForms br))
                                branchTrueForms1 = case btf1 of
                                                        Nothing -> []
                                                        Just btfSet -> Map.keys btfSet
                                --UniversalC formulas
                                (univForms1,_) = get_univ_forms (univCons br)
                                univForms = map UniversalC univForms1
                                nonUnivForms = map NonUniversalC (remove_univ branchTrueForms1 univForms1)
                                --nominal formulas
                                nomsF = getNoms branchTrueForms1
                                nomsU = getNoms univForms1
                                nomsFU = Set.union nomsF nomsU
                                noms = sort(Set.toList nomsFU)
                                (nominalForms,_) = get_nominal_forms noms br
                                cacheForms = nonUnivForms ++ univForms ++ nominalForms
                                us = (unsat_cache bd)
                                c_i = (current_index us)
                                li =  (listsList us)
                                de = (descrip_matrix us)
                                (_, indexes,_) =  (get_indexes_list de cacheForms c_i False)
                                sort_indexes =  (sort(nub indexes))
                            in if do_search sort_indexes
                                  then let r = (superset_matching_list 0 sort_indexes li)
                                       in case r of
                                               Nothing      -> (branch_info bd)
                                               Just new_ind -> let new_form_list = get_new_formula_list  new_ind de
                                                                   dps = get_dps new_form_list br pr
                                                               in (BranchClash br pr dps (neg taut))
                                  else (branch_info bd)



--receives the list of indexes of formulas in the cache, and the bidireccional map,
-- and returns the list of formulas corresponding to this list of indexes
get_new_formula_list :: [Int] -> UCMap -> [UCFormula]
get_new_formula_list (i:rest) inv_desc = 
        (f:restF) 
        where f' = Bimap.lookupR i inv_desc 
              f = case f' of
                    Nothing -> NonUniversalC (neg taut)
                    Just x -> x
              restF = get_new_formula_list rest inv_desc 
get_new_formula_list [] _  = []

--to get the dependency set corresponding to a list of UCFormulas
get_dps::[UCFormula] -> Branch -> Prefix -> DependencySet
get_dps (UniversalC form: restForms) br pr= 
                                let dps= get_dps_fU (univCons br) form
                                in dsUnion dps (get_dps restForms br pr)

get_dps (NominalC n form: restForms) br pr= let ds_n =  (DS.Nominal (showNom n))
                                                uf_n = getUrfather br ds_n 
                                                dps1 = DMap.lookup uf_n form (branchTrueForms br)
                                                dps = case dps1  of
                                                         Nothing -> dsEmpty
                                                         Just d -> d
                                            in dsUnion dps (get_dps restForms br pr)

get_dps (NonUniversalC form: restForms) br pr = let dps1 = DMap.lookup pr form (branchTrueForms br)
                                                    dps = case dps1  of
                                                             Nothing -> dsEmpty
                                                             Just d -> d
                                                in dsUnion dps (get_dps restForms br pr)

get_dps [] _ _ = dsEmpty

get_dps_fU :: Univ_constraints -> Formula -> DependencySet
get_dps_fU ((dps,f):rest) fo= if f==fo 
                                then dps
                                else get_dps_fU rest fo
get_dps_fU [] _ = dsEmpty


-----------------------------------------------------------------------------------
---------------Mapping Structure functions------------------------------------------
------------------------------------------------------------------------------------

updateDesc :: UCMap -> UCFormula -> Int -> (Int,UCMap)
updateDesc mapDes f cu_index = 
        let new_index = cu_index + 1
            new_mapDes = (Bimap.insert f new_index mapDes)
        in (new_index,new_mapDes)

--if the method was called from update cache, then it updates the description map,
--otherwise (invoqued from a search) it just returns -1
get_index :: UCMap -> Bool -> UCFormula -> Int -> (Int,Int,UCMap)
get_index mapDes upd f c_i= 
             let find_index = Bimap.lookup f  mapDes
             in case find_index  of
                  Nothing -> if upd
                                then let (n_i,new_mapDes) = updateDesc mapDes f c_i
                                     in (n_i, n_i, new_mapDes)
                                else (-1, c_i, mapDes)
                  Just i -> (i, c_i, mapDes)

get_indexes_list :: UCMap -> [UCFormula] -> Int -> Bool -> (Int,[Int],UCMap)
get_indexes_list descMat (f:fs) c_i udp =
    (new_ci, (i:is),new_mapDes) 
        where 
         (i,aux_ci,aux_mapDes)= (get_index descMat udp f c_i)
         (new_ci,is,new_mapDes) = get_indexes_list aux_mapDes fs aux_ci udp
get_indexes_list descMat [] c_i _ = (c_i,[],descMat)



do_search :: [Int] -> Bool
do_search (i:is) = if i== (-1) 
                           then False
                           else do_search is

do_search [] = True


-----------------------------------------------------------------------
---------------------------debugging----------------------------------
-----------------------------------------------------------------------

-- debug :: Show a => a -> a
-- debug x = trace (show x) x
