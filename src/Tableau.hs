module Tableau where

import Base(vPutStrLn)
import Control.Monad.State(lift,modify, put, get)
import Statistics(updateStep,printOutInspectionMetrics,
                  recordClosedBranch,recordFiredRule)
import Branch(BranchInfo(..),BranchMonad, BranchData(..),branch_depth)
import CommandLine(logRules,logState,CmdLineParams)
import Rules(Rule,applyRule,
             applicableRules,ruleToId)
import LatexOutput
import LatexOutputHelper

--

data SatFlag = SAT | UNSAT | TIMEOUT
 deriving Show

--

tableau :: BranchMonad SatFlag
tableau =
      do logMe
         bd <- get
         let clp = branch_clp bd
         let showState = logState clp
         let showRules = logRules clp
         let showSome = (showState || showRules)
         let depth = branch_depth bd
         let width = head $ branch_path bd

         let traceMsg = ("Depth " ++ (show depth) ++ " Width " ++ (show width)
                            ++ " path " ++ (show $ branch_path bd) )
         liftIO $ vPutStrLn ("\n>> " ++ traceMsg) showSome
         latexPut $ section traceMsg

         case (branch_info bd) of
          BranchClash br pf ->
           do liftIO $ vPutStrLn ((show br) ++ "\nClasher : " ++ (show pf)) showState
              latexPut $ (showLatex br) ++ "\n\nClasher : " ++ (math $ showLatex pf) ++ "\n\n"
              liftStats $ recordClosedBranch
              return UNSAT

          BranchOK br ->
           do liftIO $ vPutStrLn (show br) showState
              latexPut $ (showLatex br) ++ "\n"
              case (chooseRule $ applicableRules br clp) of
               Just rule ->
                do liftIO $ vPutStrLn ("\n>> Rule : " ++ (show rule)) showRules
                   latexPut $ ("Rule : " ++ (showLatex rule))
                   liftStats $ recordFiredRule $ ruleToId rule
                   let possibleBranches = applyRule clp rule br
                   modify (\bdata -> bdata{branch_path=(0:(branch_path bdata))})
                   chooseBranch possibleBranches
                   -- when we want to keep information, modify the
                   -- BranchData state before returning
               Nothing   ->
                do let traceMsg4 = "Saturated open branch"
                   liftIO $ vPutStrLn ("\n>> " ++ traceMsg4) showSome
                   latexPut $ traceMsg4
                   return SAT


-- dumb rule-choosing strategy
chooseRule :: [Rule] -> Maybe Rule
chooseRule (hd:_)  = Just hd
chooseRule [] = Nothing

-- depth-first strategy
chooseBranch :: [BranchInfo]  -> BranchMonad SatFlag
chooseBranch (hd:tl)
    = do bd <- get
         put bd{branch_info=hd}
         res <- tableau

         case (res) of
          SAT        -> do return SAT
          UNSAT      ->
           do put bd{branch_path=(((head (branch_path bd))+1):(tail $ branch_path bd))}
              -- we re-put bd (branchdata as it was before branching)
              -- in order to retrieve the path at that stage
              -- the problem is that we forget all information about the branches
              -- explored
              chooseBranch tl

          TIMEOUT    -> error $ "shouldn't happen"

chooseBranch [] = return UNSAT

-- like hylores' logstate. will be more developped.
logMe :: BranchMonad ()
logMe = do liftStats $ printOutInspectionMetrics
           liftStats $ modify updateStep  -- not very elegant to call it explicitely and here

--

liftStats  = lift
liftIO = lift . lift

--


latexPut :: String -> BranchMonad ()
latexPut input = do bd <- get
                    let clp = branch_clp bd
                    latexPutCLP clp input
