module HTab.Tableau where

import Control.Monad.State(StateT,lift,modify, put, get)
import HTab.Base(vPutStrLn)
import HTab.Statistics(updateStep,printOutInspectionMetrics,
                       recordClosedBranch, recordCacheHit, recordFiredRule)
import HTab.Branch(BranchInfo(..),Branch(..),BranchMonad, BranchData(..),
                   calculateStepInfo, unfulfilledEventualities, setPrevPref,
                   delNonAncestors, del_level_disjunctPrefixes)
import HTab.CommandLine(logState,backJumping,caching,CmdLineParams)
import HTab.Rules(Rule,applyRule,
                  applicableRule,ruleToId,
                  get_pr_disjunt_rule)
import HTab.Statistics(Statistics)
import HTab.Formula(Prefix,DependencySet,Formula,dsEmpty,dsMember,dsUnion)
import HTab.ModelGen ( Model, buildModel )
import HTab.Timeout( isTimeout )
import HTab.UnsatCache (update, query)

type Path = [Int]
data OpenFlag = OPEN Model | CLOSED DependencySet | TIMEOUT

tableau :: Path -> BranchMonad OpenFlag
tableau path =
      do logMe
         bd <- get
         let clp = branch_clp bd

         timeout <- isTimeout $ timeout_signal bd
         if timeout then return TIMEOUT else
          do
           debugMsg_NewSection path
           case branch_info bd of
              BranchClash br pr bprs f ->
               do debugMsg_BranchClash br pr bprs f path
                  liftStats $ recordClosedBranch
                  case caching clp of
                      Nothing -> return (CLOSED bprs)
                      _       -> do let new_disPr = delNonAncestors br pr (disjunctPrefixes bd)
                                    put bd{disjunctPrefixes = new_disPr}
                                    debugMsg_BranchClash1 br pr dsEmpty 1 path
                                    return (CLOSED bprs)
              BranchOK br_ ->
               do let currentBranchingDepth = length path + 1
                  let br = calculateStepInfo br_
                  case caching clp of
                   Nothing
                     -> do debugMsg_BranchOK br_
                           case applicableRule br clp currentBranchingDepth of
                             Nothing  ->
                                 do debugMsg_BranchOK_saturated
                                    return $ case unfulfilledEventualities br of
                                              Just ds -> CLOSED ds
                                              Nothing -> OPEN   $ buildModel br
                             Just (rule,newTodo) ->
                                 do debugMsg_BranchOK_applicableRule rule
                                    liftStats $ recordFiredRule $ ruleToId rule
                                    let possibleBranches = applyRule clp rule br newTodo
                                    chooseBranch possibleBranches path

                   _
                     -> case query br_ (unsat_cache bd) of-- not br, because br has removed its augmented prefixes
                           BranchClash br1 pr1 bprs1 _ ->
                               do debugMsg_BranchClash1 br1 pr1 bprs1 0 path--TODO see should I add this line?
                                  let new_disjunctPrefixes = delNonAncestors br1 pr1 (disjunctPrefixes bd)
                                  modify (\b -> b{disjunctPrefixes = new_disjunctPrefixes})
                                  liftStats $ recordClosedBranch
                                  liftStats $ recordCacheHit
                                  return (CLOSED bprs1)
                           BranchOK br1_ ->
                              do -- no cache hit: go on working with the branch
                                 debugMsg_BranchOK br1_
                                 case applicableRule br clp currentBranchingDepth of
                                      Nothing  -> do debugMsg_BranchOK_saturated
                                                     return $ case unfulfilledEventualities br of
                                                                Just ds -> CLOSED ds
                                                                Nothing -> OPEN   $ buildModel br
                                      Just (rule,newTodo) ->
                                              do debugMsg_BranchOK_applicableRule rule
                                                 liftStats $ recordFiredRule $ ruleToId rule
                                                 let possibleBranches' = applyRule clp rule br newTodo
                                                 --to avoid entering in the rules.hs code, clean the
                                                 --notPrevPref here...
                                                 let pref_dis_rule = get_pr_disjunt_rule rule
                                                 let possibleBranches =
                                                      case pref_dis_rule of
                                                        Nothing -> possibleBranches'
                                                        _       -> setPrevPrefInBranch possibleBranches'
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
                                                           do update p br
                                                              debugMsg_BranchClash1 br p bprs 2 path
                                                              return c
                                                        TIMEOUT -> return TIMEOUT
                                                        o@(OPEN _)  -> return o

-- depth-first branch-choosing strategy

chooseBranch :: [BranchInfo] ->  Path -> BranchMonad OpenFlag
chooseBranch bis path = chooseBranch_ dsEmpty $ zipWith (\bi n -> (bi,n:path)) bis [0..]

chooseBranch_ :: DependencySet -> [(BranchInfo,Path)] -> BranchMonad OpenFlag
chooseBranch_ currentDepSet ((hd,path):tl) =
 do bd <- get
    put bd{branch_info=hd}
    res <- tableau path
    let currentBranchingDepth = length path
    case res of
     TIMEOUT       -> return TIMEOUT
     o@(OPEN _)    -> return o
     CLOSED depSet ->
      if (backJumping $ branch_clp bd) && (not $ dsMember currentBranchingDepth depSet)
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
    let ucache = unsat_cache bd
    let d_p = disjunctPrefixes bd
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

setPrevPrefInBranch :: [BranchInfo] -> [BranchInfo]
setPrevPrefInBranch
 = map (\bi -> case bi of {BranchOK br -> BranchOK (setPrevPref br); BranchClash br pr dp f ->  BranchClash (setPrevPref br) pr dp f})

set_disjointPrefixes :: Int -> Maybe Prefix -> BranchMonad ()
set_disjointPrefixes lev pref_dis_rule =
              do bd <- get
                 case pref_dis_rule of
                    Nothing -> return () 
                    Just p -> put bd{disjunctPrefixes=((lev,p):(disjunctPrefixes bd))}

delete_levels :: Int -> BranchData ->  BranchData
delete_levels cur_level bd =
        let new_d = del_level_disjunctPrefixes cur_level (disjunctPrefixes bd)
        in bd{disjunctPrefixes = new_d}

