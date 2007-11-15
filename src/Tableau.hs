module Tableau where

import Base(vPutStrLn)
import Control.Monad.State(StateT,lift,modify, put, get)
import Statistics(updateStep,printOutInspectionMetrics,
                  recordClosedBranch,recordFiredRule)
import Branch(BranchInfo(..),Branch,BranchMonad, BranchData(..),branch_depth,
              addZeroInPath, incPathHead )
import CommandLine(logState,CmdLineParams)
import Rules(Rule,applyRule,
             applicableRules,ruleToId)
import Statistics(Statistics)
import Formula(Prefix,BranchingPrefixes,Formula,bps_empty,bps_member,bps_union)
import LatexOutput
import LatexOutputHelper
import ModelGen ( HerbrandModel, buildHerbrandModel )

--

type DependencySet = BranchingPrefixes -- to handle backjumping

data OpenFlag = OPEN HerbrandModel | CLOSED DependencySet

--

tableau :: BranchMonad OpenFlag
tableau =
      do logMe
         bd <- get
         let clp = branch_clp bd
         debugMsg_NewSection

         case (branch_info bd) of
          BranchClash br pr bprs f ->
           do debugMsg_BranchClash br pr bprs f
              liftStats $ recordClosedBranch
              return (CLOSED bprs)

          BranchOK br ->
           do debugMsg_BranchOK br
              let currentBranchingDepth = (branch_depth bd) + 1 -- `+ 1` because it's only when we know if there is an applicable rule
                                                                -- that we increase the depth of the branch
              case (chooseRule $ applicableRules br clp currentBranchingDepth) of
               Just rule ->
                do debugMsg_BranchOK_applicableRule rule
                   liftStats $ recordFiredRule $ ruleToId rule
                   let possibleBranches = applyRule clp rule br
                   modify addZeroInPath
                   chooseBranch possibleBranches
               Nothing   ->
                do debugMsg_BranchOK_saturated
                   return $ OPEN (buildHerbrandModel br)


-- simple rule-choosing strategy
chooseRule :: [Rule] -> Maybe Rule
chooseRule (hd:_)  = Just hd
chooseRule [] = Nothing

-- depth-first branch-choosing strategy
chooseBranch :: [BranchInfo] ->  BranchMonad OpenFlag
chooseBranch = chooseBranch_ bps_empty

chooseBranch_ :: BranchingPrefixes -> [BranchInfo] -> BranchMonad OpenFlag
chooseBranch_ currentDepSet (hd:tl) =
 do bd <- get
    put bd{branch_info=hd}
    res <- tableau
    let currentBranchingDepth = branch_depth bd
    case (res) of
     o@(OPEN _)    -> return o
     CLOSED depSet -> if bps_member currentBranchingDepth depSet  -- was the clash because of this branching ?
                         then do put $ incPathHead bd
                                 -- put bd (BranchData) as it was before branching
                                 -- in order to retrieve the path at that stage
                                 chooseBranch_ (bps_union currentDepSet depSet) tl
                         else return $ CLOSED (bps_union currentDepSet depSet)

chooseBranch_ currentDepSet [] = return $ CLOSED currentDepSet


logMe :: BranchMonad ()
logMe = do liftStats $ printOutInspectionMetrics
           liftStats $ modify updateStep

--
liftStats :: StateT Statistics IO a -> BranchMonad a
liftStats  = lift

liftIO :: IO a -> BranchMonad a
liftIO = lift . lift

-- STDout and LateX debug messages

debugMsg_NewSection :: BranchMonad ()
debugMsg_NewSection =  
 do bd <- get
    let showState = logState $ branch_clp bd
    let path = branch_path bd
    let depth = branch_depth bd
    let width = head path 
    let traceMsg = ("Depth " ++ (show depth) ++ " Width " ++ (show width) ++ " path " ++ (show path) )
    liftIO $ vPutStrLn ("\n>> " ++ traceMsg) showState
    latexPut $ section traceMsg

debugMsg_BranchClash :: Branch -> Prefix -> BranchingPrefixes -> Formula -> BranchMonad ()
debugMsg_BranchClash br pr bprs f =
 do bd <- get
    let showState = logState $ branch_clp bd
    liftIO $ vPutStrLn ((show br) ++ "\nClasher : " ++ (show (pr,bprs,f))) showState
    latexPut $ (showLatex br) ++ "\n\nClasher : " ++ (math $ showLatex (pr,bprs,f)) ++ "\n\n"

debugMsg_BranchOK :: Branch -> BranchMonad ()
debugMsg_BranchOK br =
 do bd <- get
    let showState = logState $ branch_clp bd
    liftIO $ vPutStrLn (show br) showState
    latexPut $ (showLatex br) ++ "\n"

debugMsg_BranchOK_applicableRule :: Rule -> BranchMonad ()
debugMsg_BranchOK_applicableRule rule =
 do bd <- get
    let showState = logState $ branch_clp bd
    liftIO $ vPutStrLn ("\n>> Rule : " ++ (show rule)) showState
    latexPut $ ("Rule : " ++ (showLatex rule))

debugMsg_BranchOK_saturated :: BranchMonad ()
debugMsg_BranchOK_saturated =
 do bd <- get
    let showState = logState $ branch_clp bd
    let traceMsg = "Saturated open branch"
    liftIO $ vPutStrLn ("\n>> " ++ traceMsg) showState
    latexPut $ traceMsg

latexPut :: String -> BranchMonad ()
latexPut input = do bd <- get
                    let clp = branch_clp bd
                    latexPutCLP clp input

