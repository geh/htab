module HTab.Tableau where

import Control.Monad.State(StateT,lift,modify, put, get)
import HTab.Base(vPutStrLn)
import HTab.Statistics(updateStep,printOutInspectionMetrics,
                       recordClosedBranch,recordFiredRule)
import HTab.Branch(BranchInfo(..),Branch,BranchMonad, BranchData(..),branch_depth,
                   addZeroInPath, incPathHead, calculateStepInfo )
import HTab.CommandLine(logState,CmdLineParams)
import HTab.Rules(Rule,applyRule,
                  applicableRules,ruleToId)
import HTab.Statistics(Statistics)
import HTab.Formula(Prefix,DependencySet,Formula,dsEmpty,dsMember,dsUnion)
import HTab.ModelGen ( HerbrandModel, buildHerbrandModel )
import HTab.Timeout( isTimeout )

data OpenFlag = OPEN HerbrandModel | CLOSED DependencySet | TIMEOUT

tableau :: BranchMonad OpenFlag
tableau =
      do logMe
         bd <- get
         let clp = branch_clp bd

         let signal = timeout_signal bd
         timeout <- isTimeout signal
         if timeout
          then return TIMEOUT
          else do debugMsg_NewSection
                  case (branch_info bd) of
                     BranchClash br pr bprs f ->
                      do debugMsg_BranchClash br pr bprs f
                         liftStats $ recordClosedBranch
                         return (CLOSED bprs)
                     BranchOK br_ ->
                      do debugMsg_BranchOK br_
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
                              return $ OPEN (buildHerbrandModel br)

-- depth-first branch-choosing strategy
chooseBranch :: [BranchInfo] ->  BranchMonad OpenFlag
chooseBranch = chooseBranch_ dsEmpty

chooseBranch_ :: DependencySet -> [BranchInfo] -> BranchMonad OpenFlag
chooseBranch_ currentDepSet (hd:tl) =
 do bd <- get
    put bd{branch_info=hd}
    res <- tableau
    let currentBranchingDepth = branch_depth bd
    case res of
     TIMEOUT       -> return TIMEOUT
     o@(OPEN _)    -> return o
     CLOSED depSet -> if dsMember currentBranchingDepth depSet  -- was the clash because of this branching ?
                         then do put $ incPathHead bd
                                 chooseBranch_ (dsUnion currentDepSet depSet) tl
                         else return $ CLOSED depSet

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


