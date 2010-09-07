module HTab.Tableau
 (OpenFlag(..), tableauStart)
where

import System.Console.CmdArgs ( whenLoud )

import Control.Monad.Reader(ask)
import Control.Monad.State(StateT,lift,modify)
import HTab.Statistics(updateStep,printOutMetrics,
                       recordClosedBranch, recordFiredRule, Statistics)
import HTab.Branch(BranchInfo(..),Branch(..),BranchMonad, BranchData(..),
                   unfulfilledEventualities)
import HTab.CommandLine(backjumping,CmdLineParams,configureStats)
import HTab.Rules(Rule,applyRule,applicableRule,ruleToId)
import HTab.Formula(Prefix,DependencySet,Formula,dsEmpty,dsMember,dsUnion)
import HTab.ModelGen ( Model, buildModel )
import HTab.Timeout( isTimeout )

type Depth = Int
data OpenFlag = OPEN Model | CLOSED DependencySet | TIMEOUT

tableauStart :: CmdLineParams -> BranchInfo -> BranchMonad OpenFlag
tableauStart clp bi = liftStats (configureStats clp) >> tableau 0 bi


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
                  liftStats recordClosedBranch
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
                    Just (rule,newTodo,newBranch)  -> -- of course then merge newBranch and newTodo
                        do debugMsg_BranchOK_applicableRule rule
                           liftStats $ recordFiredRule $ ruleToId rule
                           case applyRule clp rule newBranch newTodo of
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
         if (backjumping $ branch_clp bd) && (not $ dsMember depth depSet)
          then return $ CLOSED depSet
          else chooseBranch (dsUnion currentDepSet depSet) tl depth

chooseBranch currentDepSet [] _ = return $ CLOSED currentDepSet

--

logMe :: BranchMonad ()
logMe = do liftStats printOutMetrics
           liftStats $ modify updateStep

debugMsg_NewSection :: Depth -> BranchMonad ()
debugMsg_NewSection depth
 = liftIO $ whenLoud $ putStrLn ("\n>> Depth " ++ show depth)

debugMsg_BranchClash :: Branch -> Prefix -> DependencySet -> Formula -> Depth -> BranchMonad ()
debugMsg_BranchClash br pr bprs f depth
 = liftIO $ whenLoud $ putStrLn (show br ++ "\nClasher : " ++ show (pr,bprs,depth,f))

debugMsg_BranchOK :: Branch -> BranchMonad ()
debugMsg_BranchOK br
 = liftIO $ whenLoud $ putStrLn (show br)

debugMsg_BranchOK_applicableRule :: Rule -> BranchMonad ()
debugMsg_BranchOK_applicableRule rule
 = liftIO $ whenLoud $ putStrLn ("\n>> Rule : " ++ show rule)

debugMsg_BranchOK_saturated :: BranchMonad ()
debugMsg_BranchOK_saturated
 = liftIO $ whenLoud $ putStrLn ("\n>> Saturated open branch")

liftStats :: StateT Statistics IO a -> BranchMonad a
liftStats  = lift

liftIO :: IO a -> BranchMonad a
liftIO = lift . lift

