module HTab.Tableau
 (OpenFlag(..), tableauStart)
where

import System.Console.CmdArgs ( whenLoud )

import Control.Monad.State(StateT,lift,modify)
import HTab.Statistics(Statistics,updateStep,printOutMetrics,recordClosedBranch, recordFiredRule)
import HTab.Branch(BranchInfo(..), unfulfilledEventualities)
import HTab.CommandLine(backjumping,CmdLineParams,configureStats)
import HTab.Rules(applyRule,applicableRule,ruleToId)
import HTab.Formula(DependencySet,dsEmpty,dsMember,dsUnion)
import HTab.ModelGen ( Model, buildModel )

type Depth = Int
data OpenFlag = OPEN Model | CLOSED DependencySet
type TableauMonad a = StateT Statistics IO a

tableauStart :: CmdLineParams -> BranchInfo -> TableauMonad OpenFlag
tableauStart clp bi = (configureStats clp) >> tableau clp 0 bi

tableau :: CmdLineParams -> Depth -> BranchInfo -> TableauMonad OpenFlag
tableau clp depth branchInfo =
      do let verbose = lift . whenLoud . putStrLn
         printOutMetrics
         modify updateStep
         verbose (">> Depth " ++ show depth)
         case branchInfo of
            BranchClash br pr bprs f ->
             do verbose (show br ++ "Clasher : " ++ show (pr,bprs,depth,f))
                recordClosedBranch
                return $ CLOSED bprs
            BranchOK br ->
             do verbose (show br)
                case applicableRule br clp (depth + 1) of
                  Nothing  ->
                      do verbose (">> Saturated open branch")
                         return $ case unfulfilledEventualities br of
                                   Just ds -> CLOSED ds
                                   Nothing -> OPEN   $ buildModel br
                  Just (rule,newTodo,newBranch)  -> -- of course then merge newBranch and newTodo
                      do verbose (">> Rule : " ++ show rule)
                         recordFiredRule $ ruleToId rule
                         case applyRule clp rule newBranch newTodo of
                          [newBi] -> tableau clp (depth + 1) newBi
                          bis     -> chooseBranch clp dsEmpty bis (depth + 1)


chooseBranch :: CmdLineParams -> DependencySet -> [BranchInfo] -> Depth -> TableauMonad OpenFlag
chooseBranch clp currentDepSet (hd:tl) depth =
 do res <- tableau clp depth hd
    case res of
     o@(OPEN _)    -> return o
     CLOSED depSet ->
         if backjumping clp && not (dsMember depth depSet)
          then return $ CLOSED depSet
          else chooseBranch clp (dsUnion currentDepSet depSet) tl depth

chooseBranch _ currentDepSet [] _ = return $ CLOSED currentDepSet
