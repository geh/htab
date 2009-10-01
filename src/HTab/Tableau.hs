module HTab.Tableau where

import Control.Monad.State(StateT,lift,modify, put, get)
import qualified Data.Map as Map
import qualified HTab.DMap as DMap
import HTab.Base(vPutStrLn)
import HTab.Statistics(updateStep,printOutInspectionMetrics,
                       recordClosedBranch, recordCacheHit, recordFiredRule)
import HTab.Branch(BranchInfo(..),Branch(..),BranchMonad, BranchData(..),
                   calculateStepInfo, collectUevBprs, getBranch, setPrevPref,
                   del_pref_disjunctPrefixes, del_level_disjunctPrefixes,DisjunctPrefixes)
import HTab.CommandLine(logState,backJumping,caching,CmdLineParams)
import HTab.Rules(Rule,applyRule,
                  applicableRules,ruleToId,
                  get_pr_disjunt_rule)
import HTab.Statistics(Statistics)
import HTab.Formula(Prefix,DependencySet,Formula,dsEmpty,dsMember,dsUnion,languageTrans)
import HTab.ModelGen ( Model, buildModel )
import HTab.Timeout( isTimeout )
import HTab.UnsatCache (updateWhenClash, updateWhenDisjunct, query)

type Path = [Int]
data OpenFlag = OPEN Model | CLOSED DependencySet | TIMEOUT

tableau :: Path -> BranchMonad OpenFlag
tableau path =
      do logMe
         bd <- get
         let clp = branch_clp bd

         timeout <- isTimeout $ timeout_signal bd
         if timeout
          then return TIMEOUT
          else do debugMsg_NewSection path
                  case branch_info bd of
                     BranchClash br pr bprs f ->
                      do debugMsg_BranchClash br pr bprs f path
                         liftStats $ recordClosedBranch
                         case caching clp of
                             Nothing -> return (CLOSED bprs)
                             Just _  -> do updateWhenClash pr br
                                           debugMsg_BranchClash1 br pr dsEmpty 1 path
                                           return (CLOSED bprs)
                     BranchOK br_ ->
                      do let currentBranchingDepth = length path + 1
                         let br = calculateStepInfo br_
                         case caching clp of
                          Nothing
                            -> do debugMsg_BranchOK br_
                                  case applicableRules br clp currentBranchingDepth of
                                    []   ->
                                        do debugMsg_BranchOK_saturated
                                           return $ if existUnsatisfiedEventualities br
                                                     then CLOSED $ collectUevBprs br
                                                     else OPEN   $ buildModel br
                                    (rule:_) ->
                                        do debugMsg_BranchOK_applicableRule rule
                                           liftStats $ recordFiredRule $ ruleToId rule
                                           let possibleBranches = applyRule clp rule br
                                           chooseBranch possibleBranches path

                          Just _
                            -> do case query br_ (unsat_cache bd) of-- not br, because br has removed its augmented prefixes
                                     new_bi@(BranchClash br1 pr1 bprs1 _) ->
                                         do debugMsg_BranchClash1 br1 pr1 bprs1 0 path--TODO see should I add this line?
                                            let new_disjunctPrefixes = del_pref_disjunctPrefixes br1 pr1 (disjunctPrefixes bd)
                                            modify (update_cache_hit new_disjunctPrefixes new_bi)
                                            liftStats $ recordClosedBranch
                                            liftStats $ recordCacheHit
                                            return (CLOSED bprs1)
                                     BranchOK br1_ ->
                                        do -- no cache hit: go on working with the branch
                                           debugMsg_BranchOK br1_
                                           case applicableRules br clp currentBranchingDepth of
                                                [] ->   do debugMsg_BranchOK_saturated
                                                           return $ if existUnsatisfiedEventualities br
                                                                      then CLOSED $ collectUevBprs br
                                                                      else OPEN   $ buildModel br
                                                (rule:_) ->
                                                        do debugMsg_BranchOK_applicableRule rule
                                                           liftStats $ recordFiredRule $ ruleToId rule
                                                           let possibleBranches' = applyRule clp rule br
                                                           --to avoid entering in the rules.hs code, clean the
                                                           --notPrevPref here...
                                                           let pref_dis_rule = get_pr_disjunt_rule rule
                                                           let possibleBranches = 
                                                                case pref_dis_rule of
                                                                  Nothing -> possibleBranches'
                                                                  Just _ -> setPrevPrefInBranch possibleBranches'
                                                           set_disjointPrefixes currentBranchingDepth pref_dis_rule 
                                                           result_branching <- chooseBranch possibleBranches path
                                                           --if rule is a disjunction rule and if the result 
                                                           --of chooseBranch is closed, then update the cache 
                                                           case pref_dis_rule of 
                                                            Nothing -> return result_branching
                                                            Just p -> 
                                                             do modify (delete_levels currentBranchingDepth)
                                                                case result_branching of 
                                                                  c@(CLOSED bprs) ->
                                                                     do updateWhenDisjunct p br
                                                                        debugMsg_BranchClash1 br p bprs 2 path
                                                                        return c
                                                                  TIMEOUT -> return TIMEOUT
                                                                  o@(OPEN _)  -> return o

-- depth-first branch-choosing strategy

chooseBranch :: [BranchInfo] ->  Path -> BranchMonad OpenFlag
chooseBranch bis path = chooseBranch_ dsEmpty $ zipWith (\bi n -> (bi,n:path)) bis [0..]

chooseBranch_ :: DependencySet -> [(BranchInfo,Path)] -> BranchMonad OpenFlag
chooseBranch_ currentDepSet ((hd,path):tl) =
 do bd' <- get
    put bd'{branch_info=hd}
    res <- tableau path
    --when caching is activated, get the cache information added during tableau to the current branch level
    bd <- case ( caching $ branch_clp bd' ) of 
             Nothing -> return bd' 
             _ ->  do auxbd <-get
                      let unsatC = (unsat_cache auxbd)
                      let old_disPr = (disjunctPrefixes auxbd)
                      return bd'{unsat_cache= unsatC,
                                 disjunctPrefixes = old_disPr} 

    let currentBranchingDepth = length path
    let backjump = (not $ languageTrans $ inputLanguage $ getBranch $ branch_info bd)
                   && (backJumping $ branch_clp bd) -- disable backjumping in presence of transitive closure
    case res of
     TIMEOUT       -> return TIMEOUT
     o@(OPEN _)    -> return o
     CLOSED depSet ->
      if backjump && (not $ dsMember currentBranchingDepth depSet)
       then return $ CLOSED depSet
       else chooseBranch_ (dsUnion currentDepSet depSet) tl

chooseBranch_ currentDepSet [] = return $ CLOSED currentDepSet


logMe :: BranchMonad ()
logMe = do liftStats $ printOutInspectionMetrics
           liftStats $ modify updateStep

--
liftStats :: StateT Statistics IO a -> BranchMonad a
liftStats  = lift

liftIO :: IO a -> BranchMonad a
liftIO = lift . lift

--

debugMsg_NewSection :: Path -> BranchMonad ()
debugMsg_NewSection path =
 do bd <- get
    let showState = logState $ branch_clp bd
    let depth = length path
    let width = head path 
    let traceMsg = "Depth " ++ show depth ++ " Width " ++ show width ++ " path " ++ show path
    liftIO $ vPutStrLn ("\n>> " ++ traceMsg) showState

debugMsg_BranchClash :: Branch -> Prefix -> DependencySet -> Formula -> Path -> BranchMonad ()
debugMsg_BranchClash br pr bprs f path =
 do bd <- get
    let showState = logState $ branch_clp bd
    let currentBranchingDepth = length path
    liftIO $ vPutStrLn (show br ++ "\nClasher : " ++ show (pr,bprs,currentBranchingDepth,f)) showState

debugMsg_BranchClash1 :: Branch -> Prefix -> DependencySet -> Int-> Path -> BranchMonad ()
debugMsg_BranchClash1 br pr dps n path =
 do bd <- get
    let showState = logState $ branch_clp bd
    let ucache = (unsat_cache bd)
    let d_p = (disjunctPrefixes bd)
    let currentBranchingDepth = length path
    liftIO $ vPutStrLn (show br ++ "\nUC Clasher : " ++ show (pr,dps,currentBranchingDepth,n,path,ucache,d_p)) showState


debugMsg_BranchOK :: Branch -> BranchMonad ()
debugMsg_BranchOK br =
 do bd <- get
    let showState = logState $ branch_clp bd
    liftIO $ vPutStrLn (show br) showState

debugMsg_BranchOK_applicableRule :: Rule -> BranchMonad ()
debugMsg_BranchOK_applicableRule rule =
 do bd <- get
    let showState = logState $ branch_clp bd
    liftIO $ vPutStrLn ("\n>> Rule : " ++ show rule) showState

debugMsg_BranchOK_saturated :: BranchMonad ()
debugMsg_BranchOK_saturated =
 do bd <- get
    let showState = logState $ branch_clp bd
    let traceMsg = "Saturated open branch"
    liftIO $ vPutStrLn ("\n>> " ++ traceMsg) showState

existUnsatisfiedEventualities :: Branch -> Bool
existUnsatisfiedEventualities br = not ((Map.null $ DMap.toMap $ prefToUevFwd br) && (Map.null $ DMap.toMap $ prefToUevBwd br))

setPrevPrefInBranch :: [BranchInfo] -> [BranchInfo]
setPrevPrefInBranch (hd:tl) = (new_hd:new_tl)
                                 where new_hd = case hd of
                                                            BranchOK br -> BranchOK (setPrevPref br )
                                                            BranchClash br pr dp f -> 
                                                                      BranchClash (setPrevPref br) pr dp f  
                                       new_tl = setPrevPrefInBranch tl
setPrevPrefInBranch [] = []

set_disjointPrefixes :: Int -> Maybe Prefix -> BranchMonad BranchData
set_disjointPrefixes lev pref_dis_rule =
              do bd <- get
                 case pref_dis_rule of
                    Nothing -> return bd
                    Just p -> do put bd{disjunctPrefixes=((lev,p):(disjunctPrefixes bd))}
                                 return bd{disjunctPrefixes=((lev,p):(disjunctPrefixes bd))}

delete_levels :: Int -> BranchData ->  BranchData
delete_levels cur_level bd =
        let new_d = del_level_disjunctPrefixes cur_level (disjunctPrefixes bd)
        in bd{disjunctPrefixes = new_d}

-- only called when new_bi is BranchClash ...
update_cache_hit :: DisjunctPrefixes -> BranchInfo -> BranchData ->  BranchData
update_cache_hit new_disjunctPrefixes new_bi bd = bd{branch_info = new_bi,
                                                     disjunctPrefixes = new_disjunctPrefixes}

