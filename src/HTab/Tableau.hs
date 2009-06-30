module HTab.Tableau where

import Control.Monad.State(StateT,lift,modify, put, get)
import qualified Data.Map as Map
import qualified HTab.DMap as DMap
import HTab.Base(vPutStrLn)
import HTab.Statistics(updateStep,printOutInspectionMetrics,
                       recordClosedBranch,recordFiredRule)
import HTab.Branch(BranchInfo(..),Branch(..),BranchMonad, BranchData(..),branch_depth,
                   addZeroInPath, incPathHead, calculateStepInfo, collectUevBprs,
                   getBranch,getUrfather,wipeNotPrevPref )
import HTab.CommandLine(logState,backJumping,caching,CmdLineParams)
import HTab.Rules(Rule,applyRule,
                  applicableRules,ruleToId,
                  get_pr_disjunt_rule)
import HTab.Statistics(Statistics)
import HTab.Formula(Prefix,DependencySet,Formula,dsEmpty,dsMember,dsUnion,languageTrans)
import HTab.ModelGen ( Model, buildModel )
import HTab.Timeout( isTimeout )
import HTab.UnsatCache

--import Debug.Trace

import qualified HTab.DisjSet as DS

data OpenFlag = OPEN Model | CLOSED DependencySet | TIMEOUT

tableau :: BranchMonad OpenFlag
tableau =
      do logMe
         bd <- get
         let clp = branch_clp bd
         let caching_approach =  caching $ clp
         let activate_caching = (caching_approach /= 0) 

         let signal = timeout_signal bd
         timeout <- isTimeout signal
         if timeout
          then return TIMEOUT
          else do debugMsg_NewSection
                  case (branch_info bd) of
                     BranchClash br pr bprs f ->
                      do debugMsg_BranchClash br pr bprs f
                         liftStats $ recordClosedBranch
                         -- update the cache
                         if activate_caching 
                             then do let ds_pr =  (DS.Prefix pr)
                                     let u_pr = (getUrfather br ds_pr )
                                     _ <- update_cache caching_approach u_pr br False
                                     debugMsg_BranchClash1 br u_pr 1
                                     return (CLOSED bprs)
                             else return (CLOSED bprs)
                     BranchOK br_ ->
                      do 
                         if (not activate_caching)
                          then do debugMsg_BranchOK br_
                                  let currentBranchingDepth = (branch_depth bd) + 1
                                  let br = calculateStepInfo br_
                                  case applicableRules br clp currentBranchingDepth of
                                    (rule:_) ->
                                        do debugMsg_BranchOK_applicableRule rule
                                           liftStats $ recordFiredRule $ ruleToId rule
                                           let possibleBranches = applyRule clp rule br
                                           modify addZeroInPath
                                           chooseBranch possibleBranches
                                    []   ->
                                        do debugMsg_BranchOK_saturated
                                           return $ if (Map.null $ DMap.toMap $ prefToUevFwd br) && (Map.null $ DMap.toMap $ prefToUevBwd br)
                                                     then OPEN (buildModel br)        -- no unsatisfied eventuality
                                                     else CLOSED $ collectUevBprs br  -- which bprs ? union those of the unsatisfied eventualities
                          else do let new_bi = search_cache caching_approach br_ bd 
                                  case (new_bi) of
                                     BranchClash br1 pr1 bprs1 _ ->
                                         do --we found a hit: update branch data to reflect the closed branch... 
                                            debugMsg_BranchClash1 br1 pr1 0--TODO see should I add this line?
                                            put bd{branch_info = new_bi}
                                            liftStats $ recordClosedBranch
                                            return (CLOSED bprs1)
                                     BranchOK br1_ ->
                                        do --we didn't find a hit: go on working with the branch
                                           debugMsg_BranchOK br1_
                                           let currentBranchingDepth = (branch_depth bd) + 1
                                           let br = calculateStepInfo br1_
                                           case applicableRules br clp currentBranchingDepth of
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
                                                                  Just p_d -> wipeNotPrevPrefInPossBranches p_d possibleBranches'
                                                           modify addZeroInPath
                                                           result_branching <- chooseBranch possibleBranches
                                                           --if rule is a disjunction rule and if the result 
                                                           --of chooseBranch is closed, then update the cache 
                                                           case pref_dis_rule of 
                                                             Nothing -> return result_branching
                                                             Just p -> 
                                                                case result_branching of 
                                                                  c@(CLOSED _) ->
                                                                     do let ds_pr =  (DS.Prefix p)
                                                                        let u_p = (getUrfather br ds_pr )
                                                                        _ <- update_cache caching_approach u_p br True
                                                                        debugMsg_BranchClash1 br u_p 2
                                                                        return c
                                                                  TIMEOUT -> return TIMEOUT
                                                                  o@(OPEN _)  -> return o
                                                [] ->   do debugMsg_BranchOK_saturated
                                                           return $ if (Map.null $ DMap.toMap $ prefToUevFwd br) && (Map.null $ DMap.toMap $ prefToUevBwd br)
                                                                      then OPEN (buildModel br)        -- no unsatisfied eventuality
                                                                      else CLOSED $ collectUevBprs br  -- which bprs ? union those of the unsatisfied eventualities

-- depth-first branch-choosing strategy
chooseBranch :: [BranchInfo] ->  BranchMonad OpenFlag
chooseBranch = chooseBranch_ dsEmpty

chooseBranch_ :: DependencySet -> [BranchInfo] -> BranchMonad OpenFlag
chooseBranch_ currentDepSet (hd:tl) =
 do bd' <- get
    put bd'{branch_info=hd}
    res <- tableau
    let activate_caching = (caching $ branch_clp bd') /= 0
    bd <- if activate_caching then get 
                              else return bd'
    let currentBranchingDepth = branch_depth bd
    let backjump = (not $ languageTrans $ inputLanguage $ getBranch $ branch_info bd) && (backJumping $ branch_clp bd) -- disable backjumping in presence of transitive closure
    case res of
     TIMEOUT       -> return TIMEOUT
     o@(OPEN _)    -> return o
     CLOSED depSet ->
      if backjump
       then
          if dsMember currentBranchingDepth depSet  -- was the clash because of this branching ?
             then do put $ incPathHead bd
                     chooseBranch_ (dsUnion currentDepSet depSet) tl
             else return $ CLOSED depSet
       else
        do put $ incPathHead bd
           chooseBranch_ (dsUnion currentDepSet depSet) tl

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

debugMsg_NewSection :: BranchMonad ()
debugMsg_NewSection =  
 do bd <- get
    let showState = logState $ branch_clp bd
    let path = branch_path bd
    let depth = branch_depth bd
    let width = head path 
    let traceMsg = "Depth " ++ show depth ++ " Width " ++ show width ++ " path " ++ show path
    liftIO $ vPutStrLn ("\n>> " ++ traceMsg) showState

debugMsg_BranchClash :: Branch -> Prefix -> DependencySet -> Formula -> BranchMonad ()
debugMsg_BranchClash br pr bprs f =
 do bd <- get
    let showState = logState $ branch_clp bd
    liftIO $ vPutStrLn (show br ++ "\nClasher : " ++ show (pr,bprs,f)) showState

debugMsg_BranchClash1 :: Branch -> Prefix -> Int-> BranchMonad ()
debugMsg_BranchClash1 br pr n =
 do bd <- get
    let showState = logState $ branch_clp bd
    let ucache = (unsat_cache bd)
    let path = (branch_path bd)
    liftIO $ vPutStrLn (show br ++ "\nUC Clasher : " ++ show (pr,n,path,ucache)) showState


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



wipeNotPrevPrefInPossBranches :: Prefix -> [BranchInfo] -> [BranchInfo]
wipeNotPrevPrefInPossBranches p (hd:tl) = (new_hd:new_tl)
                                          where new_hd = case hd of
                                                            BranchOK br -> BranchOK (wipeNotPrevPref p br )
                                                            BranchClash br pr dp f -> 
                                                                      BranchClash (wipeNotPrevPref p br) pr dp f  
                                                new_tl = wipeNotPrevPrefInPossBranches p tl
wipeNotPrevPrefInPossBranches _ [] = []

--debug :: Show a => a -> a
--debug x = trace (show x) x
