module HTab.Tableau
 (OpenFlag(..), tableauStart)
where

import System.Console.CmdArgs ( whenLoud )

import Control.Monad.State(StateT,lift,modify)
import HTab.Statistics(Statistics,updateStep,printOutMetrics,recordClosedBranch, recordFiredRule)
import HTab.Branch(BranchInfo(..))
import HTab.CommandLine(backjumping,Params,configureStats)
import HTab.Rules(applyRule,applicableRule,ruleToId)
import HTab.Formula(DependencySet,dsEmpty,dsMember,dsUnion)
import HTab.ModelGen ( Model, buildModel )

type Depth = Int
data OpenFlag = OPEN Model | CLOSED DependencySet
type TableauMonad a = StateT Statistics IO a

tableauStart :: Params -> BranchInfo -> TableauMonad OpenFlag
tableauStart p bi = configureStats p >> tableauDown p 0 bi

tableauDown :: Params -> Depth -> BranchInfo -> TableauMonad OpenFlag
tableauDown p depth branchInfo =
      do let verbose = lift . whenLoud . putStrLn
         printOutMetrics
         modify updateStep
         verbose $ ">> Depth " ++ show depth
         case branchInfo of
            BranchClash br pr bprs f ->
             do verbose $ show br ++ "Clasher : " ++ show (pr,bprs,depth,f)
                recordClosedBranch
                return $ CLOSED bprs
            BranchOK br ->
             do verbose (show br)
                case applicableRule br p (depth + 1) of
                  Nothing  ->
                      do verbose ">> Saturated open branch"
                         return $ OPEN $ buildModel br
                  Just (rule,newTodo,newBranch)  -> -- of course then merge newBranch and newTodo
                      do verbose $ ">> Rule : " ++ show rule
                         recordFiredRule $ ruleToId rule
                         case applyRule p rule newBranch newTodo of
                          [newBi] -> tableauDown  p (depth + 1) newBi
                          bis     -> tableauRight p (depth + 1) bis dsEmpty

tableauRight :: Params -> Depth -> [BranchInfo] -> DependencySet -> TableauMonad OpenFlag
tableauRight p depth (hd:tl) currentDepSet =
 do res <- tableauDown p depth hd
    case res of
     o@(OPEN _)    -> return o
     CLOSED depSet ->
         if backjumping p && not (dsMember depth depSet)
          then return $ CLOSED depSet
          else tableauRight p depth tl (dsUnion currentDepSet depSet)

tableauRight _ _ [] currentDepSet = return $ CLOSED currentDepSet
