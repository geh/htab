module HTab.Tableau
 (OpenFlag(..), tableauStart)
where

import Control.Monad.Reader(ask)
import Control.Monad.State(StateT,lift,modify)
import HTab.Base(vPutStrLn)
import HTab.Statistics(updateStep,printOutInspectionMetrics,
                       recordClosedBranch, recordFiredRule)
import HTab.Branch(BranchInfo(..),Branch(..),BranchMonad, BranchData(..),
                   unfulfilledEventualities)
import HTab.CommandLine(logState,backJumping,CmdLineParams,configureMetrics)
import HTab.Rules(Rule,applyRule,applicableRule,ruleToId)
import HTab.Statistics(Statistics)
import HTab.Formula(Prefix,DependencySet,Formula,dsEmpty,dsMember,dsUnion)
import HTab.ModelGen ( Model, buildModel )
import HTab.Timeout( isTimeout )

type Depth = Int
data OpenFlag = OPEN Model | CLOSED DependencySet | TIMEOUT

tableauStart :: CmdLineParams -> BranchInfo -> BranchMonad OpenFlag
tableauStart clp bi = (liftStats $ configureMetrics clp) >> tableau 0 bi


tableau :: Depth -> BranchInfo -> BranchMonad OpenFlag
tableau depth branchInfo =
      do logMe
         bd <- ask
         timeout <- isTimeout $ timeout_signal bd
         if timeout then return TIMEOUT else
          do
           debugMsg_NewSection depth
           case branchInfo of
              BranchClash br pr bprs f ->
               do debugMsg_BranchClash br pr bprs f depth
                  liftStats $ recordClosedBranch
                  return (CLOSED bprs)
              BranchOK br ->
               do debugMsg_BranchOK br
                  let clp = branch_clp bd
                  case applicableRule br clp (depth + 1) of
                    Nothing  ->
                        do debugMsg_BranchOK_saturated
                           return $ case unfulfilledEventualities br of
                                     Just ds -> CLOSED ds
                                     Nothing -> OPEN   $ buildModel br
                    Just (rule,newTodo) ->
                        do debugMsg_BranchOK_applicableRule rule
                           liftStats $ recordFiredRule $ ruleToId rule
                           case applyRule clp rule br newTodo of
                            [newBi] -> tableau (depth + 1) newBi
                            bis     -> chooseBranch dsEmpty bis (depth + 1)


chooseBranch :: DependencySet -> [BranchInfo] -> Depth -> BranchMonad OpenFlag
chooseBranch currentDepSet (hd:tl) depth =
 do res <- tableau depth hd
    case res of
     TIMEOUT       -> return TIMEOUT
     o@(OPEN _)    -> return o
     CLOSED depSet ->
      do bd <- ask
         if (backJumping $ branch_clp bd) && (not $ dsMember depth depSet)
          then return $ CLOSED depSet
          else chooseBranch (dsUnion currentDepSet depSet) tl depth

chooseBranch currentDepSet [] _ = return $ CLOSED currentDepSet

--

logMe :: BranchMonad ()
logMe = do liftStats $ printOutInspectionMetrics
           liftStats $ modify updateStep

debugMsg_NewSection :: Depth -> BranchMonad ()
debugMsg_NewSection depth =
 do bd <- ask
    let showState = logState $ branch_clp bd
    let traceMsg = "Depth " ++ show depth
    liftIO $ vPutStrLn ("\n>> " ++ traceMsg) showState

debugMsg_BranchClash :: Branch -> Prefix -> DependencySet -> Formula -> Depth -> BranchMonad ()
debugMsg_BranchClash br pr bprs f depth =
 do bd <- ask
    let showState = logState $ branch_clp bd
    liftIO $ vPutStrLn (show br ++ "\nClasher : " ++ show (pr,bprs,depth,f)) showState

debugMsg_BranchOK :: Branch -> BranchMonad ()
debugMsg_BranchOK br =
 do bd <- ask
    let showState = logState $ branch_clp bd
    liftIO $ vPutStrLn (show br) showState

debugMsg_BranchOK_applicableRule :: Rule -> BranchMonad ()
debugMsg_BranchOK_applicableRule rule =
 do bd <- ask
    let showState = logState $ branch_clp bd
    liftIO $ vPutStrLn ("\n>> Rule : " ++ show rule) showState

debugMsg_BranchOK_saturated :: BranchMonad ()
debugMsg_BranchOK_saturated =
 do bd <- ask
    let showState = logState $ branch_clp bd
    let traceMsg = "Saturated open branch"
    liftIO $ vPutStrLn ("\n>> " ++ traceMsg) showState

liftStats :: StateT Statistics IO a -> BranchMonad a
liftStats  = lift

liftIO :: IO a -> BranchMonad a
liftIO = lift . lift

