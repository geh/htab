module HTab.UnsatCache 
(update_cache,search_cache)
where

import Control.Monad.State(put, get)

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Maybe()
import Data.List
import HTab.UCMatrix
import HTab.UCList
import Data.Array.Diff
import HTab.Formula
import HTab.Branch(BranchInfo(..),Branch(..),BranchMonad, BranchData(..),
                   UCache(..),Univ_constraints,AugmentedPrefixes,UCMap,
                   getUrfather)
import qualified HTab.DisjSet as DS


--import Debug.Trace

---------------------------------------------------
--cache
--------------------------------------------------

------------update--------------------------------
--given the input prefix, get the parents and call to update cache 
update_cache :: Int -> Prefix -> Branch -> Bool -> BranchMonad BranchData
--when calling from a clash, don't add into the cache the info from the clashing prefix
update_cache approach pr br False = 
                        do bd <- get
                           let uc = (unsat_cache bd)
                           let valid_prefixes = nub (notPrevPref br) --to allow just one repetition of each element
                           let ppr = Map.lookup pr (prefParent br) 
                           case ppr of
                                 Nothing -> return bd
                                 Just p -> if elem p valid_prefixes 
                                             then do let ds_pr = DS.Prefix p
                                                     let u_p = (getUrfather br ds_pr )
                                                     let new_uc = update_cache_prefixes approach u_p br uc valid_prefixes
                                                     put bd{unsat_cache = new_uc}
                                                     return bd{unsat_cache = new_uc}
                                             else return bd

--when calling after backtracking from the application of a disjunct rule, add the info from the first prefix
update_cache approach pr  br True = 
                        do bd <- get
                           let n_uc = update_cache_ approach pr br (unsat_cache bd)
                           let valid_prefixes = nub (notPrevPref br) --to allow just one repetition of each element
                           let ppr =  Map.lookup pr (prefParent br) 
                           case ppr of
                                 Nothing -> return bd{unsat_cache = n_uc}
                                 Just p -> if (elem p valid_prefixes )
                                             then do let ds_pr = DS.Prefix p
                                                     let u_p = (getUrfather br ds_pr )
                                                     let new_new_uc=
                                                             update_cache_prefixes approach u_p br n_uc valid_prefixes
                                                     put bd{unsat_cache = new_new_uc}
                                                     return bd{unsat_cache = new_new_uc}
                                             else do put bd{unsat_cache = n_uc}
                                                     return bd{unsat_cache = n_uc}


update_cache_prefixes :: Int -> Prefix -> Branch -> UCache-> [Prefix] -> UCache
update_cache_prefixes approach pr br uc vps= 
                                    let ds_pr = DS.Prefix pr
                                        u_pr = (getUrfather br ds_pr )
                                        new_uc = update_cache_ approach u_pr br uc
                                        ppr = Map.lookup u_pr (prefParent br) 
                                    in case ppr of
                                          Nothing -> new_uc
                                          Just p -> if elem p vps
                                                        then update_cache_prefixes approach p br new_uc vps
                                                        else new_uc

--using matrix
update_cache_ :: Int -> Prefix -> Branch -> UCache-> UCache
update_cache_ 1 pr br uc = 
                         let btf1 = Map.lookup pr (branchTrueForms br)
                             branchTrueForms1 = case btf1 of
                                                     Nothing -> []
                                                     Just btfSet -> Set.toList btfSet
                             univForms1 = get_univ_forms (univCons br)
                             univForms = map UniversalC univForms1
                             nonUnivForms = map NonUniversalC (remove_univ branchTrueForms1 univForms1)
                             --nominal formulas
                             nomsF = getNoms branchTrueForms1
                             nomsU = getNoms univForms1
                             nomsFU = Set.union nomsF nomsU
                             noms = sort(Set.toList nomsFU)
                             nominalForms = get_nominal_forms noms br
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


--using lists approach
update_cache_ 2 pr br uc = 
                         let btf1 = Map.lookup pr (branchTrueForms br)
                             branchTrueForms1 = case btf1 of
                                                     Nothing -> []
                                                     Just btfSet -> Set.toList btfSet
                             nonUnivForms = map NonUniversalC (remove_univ branchTrueForms1 univForms1)
                             --UniversalC formulas
                             univForms1 = get_univ_forms (univCons br)
                             univForms = map UniversalC univForms1
                             --nominal formulas
                             nomsF = getNoms branchTrueForms1
                             nomsU = getNoms univForms1
                             nomsFU = Set.union nomsF nomsU
                             noms = sort(Set.toList nomsFU)
                             nominalForms = get_nominal_forms noms br
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

get_nominal_forms:: [NomSymbol] -> Branch -> [UCFormula]
get_nominal_forms (n:rest) br = 
                let ds_n =  (DS.Nominal (showNom n))
                    uf_n = getUrfather br ds_n 
                    btf = Map.lookup uf_n (branchTrueForms br)
                    btf_list = case btf of
                                 Nothing -> []
                                 Just btfSet -> Set.toList btfSet
                    btf_listNom = map (NominalC n) btf_list
                in concat[btf_listNom,restBtf]
                where restBtf = get_nominal_forms rest br
get_nominal_forms [] _ = []


--to get the universally constrained formulas
get_univ_forms :: Univ_constraints -> [Formula]
get_univ_forms ((_,f):rest)= let tail_u = get_univ_forms rest
                             in (f:tail_u)
get_univ_forms []=[]

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

search_cache :: Int -> Branch -> BranchData -> BranchInfo
search_cache approach br bd  = 
                      let not_repeted_incrPrs = nub (incrPrs br)
                      in search_cache_ approach not_repeted_incrPrs br bd

--to iterate over the list of prefixes
search_cache_ :: Int -> AugmentedPrefixes -> Branch -> BranchData -> BranchInfo
search_cache_ approach (pr:tail_pr) br bd = 
                                   let res = search_cache_pr approach pr br bd 
                                   in case res  of
                                        b@(BranchClash _ _ _ _) -> b
                                        BranchOK _ ->search_cache_ approach tail_pr br bd
                                                        
search_cache_ _ [] _ bd = (branch_info bd)

--to detect a cache hit for a prefix and a branch
--using a bit matrix
search_cache_pr :: Int -> Prefix -> Branch -> BranchData -> BranchInfo
search_cache_pr 1 pr br bd =let btf1 = Map.lookup pr (branchTrueForms br)
                                branchTrueForms1 = case btf1 of
                                                        Nothing -> []
                                                        Just btfSet -> Set.toList btfSet
                                univForms1 = get_univ_forms (univCons br)
                                univForms = map UniversalC univForms1
                                nonUnivForms = map NonUniversalC (remove_univ branchTrueForms1 univForms1)
                                --nominal formulas
                                nomsF = getNoms branchTrueForms1
                                nomsU = getNoms univForms1
                                nomsFU = Set.union nomsF nomsU
                                noms = sort(Set.toList nomsFU)
                                nominalForms = get_nominal_forms noms br
                                --concatenat NonUniversalC, UniversalC and Nominal formulas
                                cacheForms = nonUnivForms ++ univForms ++ nominalForms
                                us = (unsat_cache bd)
                                c_i = (current_index us)
                                m_r = (max_row us)
                                mat = (matrix us)
                                (_, indexes,_) = get_indexes_list (descrip_matrix us) cacheForms c_i False
                                sort_indexes = (sort(nub indexes))
                            in if do_search sort_indexes
                                  then let r = (superset_matching 0 m_r c_i sort_indexes mat)
                                       in case r of
                                               Nothing -> (branch_info bd)
                                               Just _  -> (BranchClash br pr dsEmpty (neg taut)) 
                                  else (branch_info bd)
--using lists approach
search_cache_pr 2 pr br bd =let btf1 = Map.lookup pr (branchTrueForms br)
                                branchTrueForms1 = case btf1 of
                                                        Nothing -> []
                                                        Just btfSet -> Set.toList btfSet
                                --UniversalC formulas
                                univForms1 = get_univ_forms (univCons br)
                                univForms = map UniversalC univForms1
                                nonUnivForms = map NonUniversalC (remove_univ branchTrueForms1 univForms1)
                                --nominal formulas
                                nomsF = getNoms branchTrueForms1
                                nomsU = getNoms univForms1
                                nomsFU = Set.union nomsF nomsU
                                noms = sort(Set.toList nomsFU)
                                nominalForms = get_nominal_forms noms br
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
                                               Nothing -> (branch_info bd)
                                               Just _  -> (BranchClash br pr dsEmpty (neg taut)) 
                                  else (branch_info bd)

-----------------------------------------------------------------------------------
---------------Mapping Structure functions------------------------------------------
------------------------------------------------------------------------------------

updateDesc :: UCMap -> UCFormula -> Int -> (Int,UCMap)
updateDesc mapDes f cu_index = 
        let new_index = cu_index + 1
            new_mapDes = (Map.insert f new_index mapDes)
        in (new_index,new_mapDes)

--if the method was called from update cache, then it updates the description map,
--otherwise (invoqued from a search) it just returns -1
get_index :: UCMap -> Bool -> UCFormula -> Int -> (Int,Int,UCMap)
get_index mapDes upd f c_i= 
             let find_index = Map.lookup f  mapDes
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

------------------------------------------------------------------------------------
------------------------------MatrixFunctions---------------------------------------
------------------------------------------------------------------------------------
add_row :: Int -> Int -> Int
add_row old_current_row mrow = 
        if old_current_row <  mrow
                then old_current_row + 1
                else 0

update_matrix :: Int -> Int -> Int -> [Int] -> UCMatrix -> (Int,UCMatrix)
update_matrix cu_col cu_row ma_row indexes mat =
        case (subset_matching cu_row 0 ma_row cu_col indexes mat) of
             Nothing -> case (superset_matching 0 ma_row cu_col indexes mat) of
                          Nothing -> let new_current_row = (add_row cu_row ma_row)
                                         ma2 = update_row new_current_row 0 cu_col indexes  mat
                                     in (new_current_row, ma2)
                          Just _ -> (cu_row,mat)  --if it is a superset of an aready existing row, don't add it 
             Just i -> let ma1 = (update_row i 0 cu_col indexes  mat)
                       in (cu_row,ma1)

--update the row (entered in the first parameter) of the matrix 
--with the information in the indexes (the fourth paramter):
--for each column of the matrix: 
--if column in list of indexes then matrix(row,column)= True
--else matrix(row,column) = False
update_row ::  Int -> Int -> Int -> [Int] -> UCMatrix-> UCMatrix
update_row row col max_col (i:rest) m =
        if col <= max_col
        then if col == i 
                then if m !(row,col) == False
                     then let new_matrix = m //[((row,col),True)]
                          in update_row row (col+1) max_col rest new_matrix
                     else update_row row (col+1) max_col rest m
                else if m !(row,col) == True 
                     then let new_matrix = m //[((row,col),False)]
                          in update_row row (col+1) max_col (i:rest) new_matrix
                     else update_row row (col+1) max_col (i:rest) m
        else m
update_row row col max_col [] m =
        if col <= max_col
        then if m !(row,col) == True 
                then let new_matrix = m //[((row,col),False)]
                     in update_row row (col+1) max_col [] new_matrix
                else update_row row (col+1) max_col [] m
        else m

-----------------------------------------------------------------------
--                        Lists Function                                    ---
-----------------------------------------------------------------------

update_list:: [Int] -> UCList -> UCList
update_list indexes li = 
        case (subset_matching_list 0 indexes li) of
          Just i -> (update_row_list i indexes li)
          Nothing -> case superset_matching_list 0 indexes li of
                        Just _ -> li --if indexes is a superset of a row, don't update
                        Nothing -> (add_row_list indexes li)

update_row_list::Int -> [Int] -> UCList -> UCList
update_row_list ind indexes li = 
        let pre = take ind li
            suf = drop (ind + 1) li
            new_li = pre ++ suf
        in (indexes:new_li)

add_row_list :: [Int] -> UCList -> UCList
add_row_list indexes li = (indexes:li)


-----------------------------------------------------------------------
---------------------------debugging----------------------------------
-----------------------------------------------------------------------

--debug :: Show a => a -> a
--debug x = trace (show x) x
