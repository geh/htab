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
import qualified HTab.UCMatrix as UCMatrix
import qualified HTab.UCList   as UCList
import HTab.Formula
import HTab.CommandLine ( Caching(..) )
import HTab.Branch(BranchInfo(..),Branch(..),BranchMonad, BranchData(..),
                   UCache(..),Univ_constraints,AugmentedPrefixes,UCMap,
                   getUrfather,
                   del_pref_disjunctPrefixes, search_disjunctPrefixes)
import qualified HTab.DisjSet as DS


data CachingInstance = Cclash | Cdisjunct deriving Show


------------update--------------------------------
--given the input prefix, get the parents and call to update cache 
update_cache :: Caching -> Prefix -> Branch -> CachingInstance -> BranchMonad BranchData
--when calling from a clash, don't add into the cache the info from the clashing prefix
update_cache approach pr1 br Cclash = 
 do bd <- get
    let invalid_prefixes = nub $ prevPref br
    let new_disPr = del_pref_disjunctPrefixes br pr1 (disjunctPrefixes bd)
    case Map.lookup pr1 (prefParent br) of
          Nothing -> do put    bd{disjunctPrefixes = new_disPr}
                        return bd{disjunctPrefixes = new_disPr}
          Just p -> if not $ elem p invalid_prefixes
                      then do let new_uc = update_cache_prefixes approach p br (unsat_cache bd) invalid_prefixes
                              put    bd{unsat_cache = new_uc, disjunctPrefixes = new_disPr}
                              return bd{unsat_cache = new_uc, disjunctPrefixes = new_disPr}
                      else do put    bd{disjunctPrefixes = new_disPr}
                              return bd{disjunctPrefixes = new_disPr}

--when calling after backtracking from the application of a disjunct rule, add the info from the first prefix
update_cache approach pr1  br Cdisjunct = 
 do bd <- get
    let pr = getUrfather br $ DS.Prefix pr1
    let add_cache = search_disjunctPrefixes pr1 (disjunctPrefixes bd)
    let invalid_prefixes = nub (prevPref br)
    if add_cache && (not $ elem pr1 invalid_prefixes )
     then
       do let n_uc = update_cache_ approach pr br (unsat_cache bd)
          case Map.lookup pr1 (prefParent br) of
                Nothing -> return bd{unsat_cache = n_uc}
                Just p -> if not $ elem p invalid_prefixes
                            then do let new_new_uc = update_cache_prefixes approach p br n_uc invalid_prefixes
                                    put    bd{unsat_cache = new_new_uc}
                                    return bd{unsat_cache = new_new_uc}
                            else do put    bd{unsat_cache = n_uc}
                                    return bd{unsat_cache = n_uc}
      else return bd

                                                                        
update_cache_prefixes :: Caching -> Prefix -> Branch -> UCache-> [Prefix] -> UCache
update_cache_prefixes approach pr br uc notvps= 
 let u_pr   = getUrfather br $ DS.Prefix pr
     new_uc = update_cache_ approach u_pr br uc
 in case Map.lookup pr (prefParent br) of
       Nothing -> new_uc
       Just p -> if not $ elem p notvps
                  then update_cache_prefixes approach p br new_uc notvps
                  else new_uc

update_cache_ :: Caching -> Prefix -> Branch -> UCache-> UCache
update_cache_ approach pr br uc =
 let -- See what formulas we cache
     trueForms    = DMap.lookupInter pr $ branchTrueForms br

     univForms1   = fst $ get_univ_forms (univCons br)
     univForms    = map UniversalC    univForms1
     nonUnivForms = map NonUniversalC (remove_univ trueForms univForms1)

     noms         = getNoms (trueForms ++ univForms1)
     nominalForms = fst $ get_nominal_forms noms br

     cacheForms = nonUnivForms ++ univForms ++ nominalForms -- formulas to be cached

     -- Update the Formula <-> Int BiMap
     (maxIdx, indexes,newMapDesc) = update_ucmap ( descrip_matrix uc ) cacheForms (current_index uc)

     -- common part for the following
     sorted_indexes = sort $ nub indexes
 in
     case approach of
       MatrixCaching ->
        let (n_cr,new_matrix) = UCMatrix.update maxIdx (current_row uc) (max_row uc) sorted_indexes $ matrix uc
        in uc{ descrip_matrix = newMapDesc,
               current_index  = maxIdx,
               current_row    = n_cr,
               matrix         = new_matrix}

       ListCaching ->
            uc{ descrip_matrix = newMapDesc,
                current_index  = maxIdx,
                listsList      = UCList.update sorted_indexes $ listsList uc }

--get the set of formulas true at the nominals appearing in the formulas to be cached
getNoms :: [Formula]-> [NomSymbol]
getNoms fs = Set.toList $ Set.unions $ map (fst . extractNominals ) fs

get_nominal_forms:: [NomSymbol] -> Branch -> ([UCFormula],DependencySet)
get_nominal_forms noms br = 
 foldr merge ([],dsEmpty) $ map get_nominal_forms_one noms 
 where merge (fs1,ds1) (fs2,ds2) = (fs1 ++ fs2, dsUnion ds1 ds2)

       get_nominal_forms_one n = 
        let ur  = getUrfather br $ DS.Nominal (showNom n)
            btf = Map.lookup ur $ DMap.toMap $ branchTrueForms br
            (btf_list,dps) = case btf of
                               Nothing     -> ([], dsEmpty)
                               Just btfSet -> (Map.keys btfSet, dsUnions $ Map.elems btfSet)
        in (map (NominalC n) btf_list, dps)


--to get the universally constrained formulas
get_univ_forms :: Univ_constraints -> ([Formula],DependencySet)
get_univ_forms ucs = ( map snd ucs, dsUnions $ map fst ucs )


type TrueForms = [Formula]
type UnivForms = [Formula]

remove_univ :: TrueForms -> UnivForms -> [Formula] 
remove_univ trueForms univ_forms
 = filter (\f -> not $ is_universal f univ_forms) trueForms

is_universal :: Formula -> UnivForms -> Bool 
is_universal (A _) _  = True
is_universal form ufs = any (== form) ufs

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

search_cache_ :: Caching -> AugmentedPrefixes -> Branch -> BranchData -> BranchInfo
search_cache_ caching (pr:tail_pr) br bd =
 case search_cache_pr caching pr br bd  of
     b@(BranchClash _ _ _ _) -> b
     BranchOK _              -> search_cache_ caching tail_pr br bd

search_cache_ _ [] _ bd = branch_info bd

search_cache_pr :: Caching -> Prefix -> Branch -> BranchData -> BranchInfo
search_cache_pr approach pr br bd =
 let  trueForms    = DMap.lookupInter pr $ branchTrueForms br

      univForms1 = fst $ get_univ_forms (univCons br)
      univForms  = map UniversalC univForms1
      nonUnivForms = map NonUniversalC (remove_univ trueForms univForms1)

      noms         = getNoms (trueForms ++ univForms1)
      nominalForms = fst $ get_nominal_forms noms br

      cacheForms = nonUnivForms ++ univForms ++ nominalForms -- formulas to be cached

      uc  = unsat_cache bd
      c_i = current_index uc
      m_r = max_row uc
      mat = matrix uc
      li = listsList uc
      de  = descrip_matrix uc

  in
     case ( do indexes <- sort . nub <$> lookup_ucmap de cacheForms
               case approach of
                 MatrixCaching -> UCMatrix.superset_matching 0 m_r c_i indexes mat
                 ListCaching   -> UCList.superset_matching   0         indexes li   ) of
      Nothing     -> branch_info bd
      Just newIdx ->
               let new_form_list = get_new_formula_list de newIdx
                   dps           = get_dps new_form_list br pr
               in
                 BranchClash br pr dps (neg taut)


-- receives the list of indexes of formulas in the cache, and the bidirectional map,
-- and returns the list of formulas corresponding to this list of indexes
get_new_formula_list :: UCMap -> [Int] -> [UCFormula]
get_new_formula_list inv_desc = map (\i -> fromJust $ Bimap.lookupR i inv_desc)


--to get the dependency set corresponding to a list of UCFormulas
get_dps::[UCFormula] -> Branch -> Prefix -> DependencySet
get_dps (UniversalC form: restForms) br pr= 
  let dps = get_dps_fU (univCons br) form
  in dsUnion dps (get_dps restForms br pr)

get_dps (NominalC n form: restForms) br pr
 = let ds_n =  (DS.Nominal (showNom n))
       uf_n = getUrfather br ds_n 
       dps1 = DMap.lookup uf_n form (branchTrueForms br)
       dps = case dps1  of
                Nothing -> dsEmpty
                Just d -> d
   in dsUnion dps (get_dps restForms br pr)

get_dps (NonUniversalC form: restForms) br pr
 = let dps1 = DMap.lookup pr form (branchTrueForms br)
       dps = case dps1  of
                Nothing -> dsEmpty
                Just d -> d
   in dsUnion dps (get_dps restForms br pr)

get_dps [] _ _ = dsEmpty

get_dps_fU :: Univ_constraints -> Formula -> DependencySet
get_dps_fU ucs fo
 = case lookup fo $ map switch ucs of
      Nothing -> dsEmpty
      Just dps -> dps
    where switch (x,y) = (y,x)


-----------------------------------------------------------------------------------
---------------Mapping Structure functions------------------------------------------
------------------------------------------------------------------------------------

update_ucmap :: UCMap -> [UCFormula] -> Int -> (Int,[Int],UCMap)
update_ucmap descMat fs maxIdx =
 foldr  (\f (currentMaxIdx,currentIdxs,currentMap)
            -> let (newMaxIdx,idx,newMap) = get_index currentMap f currentMaxIdx
               in  (newMaxIdx, (idx:currentIdxs), newMap) 
        )
        (maxIdx, [], descMat) fs

get_index :: UCMap -> UCFormula -> Int -> (Int,Int,UCMap)
get_index mapDes f maxIdx = 
 case Bimap.lookup f mapDes of
    Just i  -> (maxIdx, i, mapDes)
    Nothing -> let (n_i,new_mapDes) = updateBiMap mapDes f maxIdx
               in  (n_i, n_i, new_mapDes)

updateBiMap :: UCMap -> UCFormula -> Int -> (Int,UCMap)
updateBiMap mapDes f maxIdx = 
  let newMaxIdx  = maxIdx + 1
      new_mapDes = Bimap.insert f newMaxIdx mapDes
  in ( newMaxIdx, new_mapDes )


lookup_ucmap :: UCMap -> [UCFormula] -> Maybe [Int]
lookup_ucmap descMat fs =
 foldr  (\f mList
            -> case mList of
                Nothing -> Nothing
                Just is -> case Bimap.lookup f descMat of { Just i -> Just (i:is) ; Nothing -> Nothing }
        )
        (Just []) fs

