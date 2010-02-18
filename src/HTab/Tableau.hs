module HTab.Tableau where

import Control.Monad.State(StateT,lift,modify, put, get)
import HTab.Base(vPutStrLn)
import HTab.Statistics(updateStep,printOutInspectionMetrics,
                       recordClosedBranch, recordFiredRule)
import HTab.Branch(BranchInfo(..),Branch(..),BranchMonad, BranchData(..),
                   calculateStepInfo, unfulfilledEventualities)
import HTab.CommandLine(logState,backJumping,CmdLineParams)
import HTab.Rules(Rule,applyRule,applicableRule,ruleToId)
import HTab.Statistics(Statistics)
import HTab.Formula(Prefix,DependencySet,Formula,dsEmpty,dsMember,dsUnion)
import HTab.ModelGen ( Model, buildModel )
import HTab.Timeout( isTimeout )

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
                  return (CLOSED bprs)
              BranchOK br_ ->
               do let currentBranchingDepth = length path + 1
                  let br = calculateStepInfo br_
                  debugMsg_BranchOK br_
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
                           case possibleBranches of
                            [newBi] -> do put bd{branch_info=newBi}
                                          tableau (0:path)
                            _       -> chooseBranch possibleBranches path

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

