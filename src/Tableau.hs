module Tableau where

import Base(vPutStrLn)
import Control.Monad.State(StateT,lift,modify, put, get)
import Statistics(updateStep,printOutInspectionMetrics,
                  recordClosedBranch,recordFiredRule)
import Branch(BranchInfo(..),Branch,BranchMonad, BranchData(..),branch_depth,
              addZeroInPath, incPathHead)
import CommandLine(logState,CmdLineParams)
import Rules(Rule,applyRule,
             applicableRules,ruleToId)
import Statistics(Statistics)
import Formula(PrFormula)
import LatexOutput
import LatexOutputHelper

--

data OpenFlag = OPEN | CLOSED

--

tableau :: BranchMonad OpenFlag
tableau =
      do logMe
         bd <- get
         let clp = branch_clp bd
         debugMsg_NewSection

         case (branch_info bd) of
          BranchClash br pf ->
           do debugMsg_BranchClash br pf
              liftStats $ recordClosedBranch
              return CLOSED

          BranchOK br ->
           do debugMsg_BranchOK br
              case (chooseRule $ applicableRules br clp) of
               Just rule ->
                do debugMsg_BranchOK_applicableRule rule
                   liftStats $ recordFiredRule $ ruleToId rule
                   let possibleBranches = applyRule clp rule br
                   modify addZeroInPath
                   chooseBranch possibleBranches
                   -- when we want to keep information, modify the
                   -- BranchData state before returning
               Nothing   ->
                do debugMsg_BranchOK_saturated
                   return OPEN


-- simple rule-choosing strategy
chooseRule :: [Rule] -> Maybe Rule
chooseRule (hd:_)  = Just hd
chooseRule [] = Nothing

-- depth-first branch-choosing strategy
chooseBranch :: [BranchInfo]  -> BranchMonad OpenFlag
chooseBranch (hd:tl) =
 do bd <- get
    put bd{branch_info=hd}
    res <- tableau

    case (res) of
     OPEN     -> return OPEN
     CLOSED   -> do put $ incPathHead bd
                    -- put bd (BranchData) as it was before branching
                    -- in order to retrieve the path at that stage
                    chooseBranch tl

chooseBranch [] = return CLOSED

-- like hylores' logstate
logMe :: BranchMonad ()
logMe = do liftStats $ printOutInspectionMetrics
           liftStats $ modify updateStep  -- not very elegant to call it explicitely and here

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

debugMsg_BranchClash :: Branch -> PrFormula -> BranchMonad ()
debugMsg_BranchClash br pf =
 do bd <- get
    let showState = logState $ branch_clp bd
    liftIO $ vPutStrLn ((show br) ++ "\nClasher : " ++ (show pf)) showState
    latexPut $ (showLatex br) ++ "\n\nClasher : " ++ (math $ showLatex pf) ++ "\n\n"

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

