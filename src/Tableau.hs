module Tableau where

import Base(vPutStrLn)
import Control.Monad.State(lift,modify, put, get)
import Statistics(updateStep,printOutInspectionMetrics,recordClosedBranch)
import Branch
import CommandLine(logRules,logState,CmdLineParams)
import Rules(Rule,applyRule,applyToMonad, applicableRules, howManyBranches)

data SatFlag = SAT | UNSAT | TIMEOUT
 deriving Show



tableau :: Int -> CmdLineParams -> BranchMonad SatFlag
tableau depth clp =
      do logMe
         let showState = (logState clp)
         let showRules = (logRules clp)
         bi <- get
         case bi of
            BranchClash br pf -> do liftIO $ vPutStrLn (show br) showState
                                    liftIO $ vPutStrLn ("\nClasher : " ++ (show pf)) showState
                                    liftStats $ recordClosedBranch -- increment counter by modifying the Statistics monad
                                    return UNSAT

            BranchOK br -> do liftIO $ vPutStrLn (show br) showState
                              let listOfRules = applicableRules br
                              let r = chooseRule listOfRules
                              case r of
                                  Just rule -> do liftIO $ vPutStrLn ("\n>> Rule : " ++ (show rule)) showRules
                                                  if (howManyBranches rule) > 1
                                                    then do let possibleBranches = applyRule rule br
                                                            chooseBranch possibleBranches depth 0 clp
                                                    else do applyToMonad rule
                                                            tableau (depth+1) clp
                                  Nothing   -> do liftIO $ vPutStrLn "\n>> Saturated open branch" (showState || showRules)
                                                  return SAT


-- dumb rule-choosing strategy
chooseRule :: [Rule] -> Maybe Rule
chooseRule (hd:_)  = Just hd
chooseRule [] = Nothing

-- dumb depth-first strategy
chooseBranch :: [BranchInfo] -> Int -> Int -> CmdLineParams ->  BranchMonad SatFlag
chooseBranch (hd:tl) depth width clp
    = do let showState = (logState clp)
         let showRules = (logRules clp)
         liftIO $ vPutStrLn ("\n>> Depth #" ++ (show depth) ++ " Width #" ++ (show width)) (showState || showRules)
         put hd          -- overwrite the monad with the first branchinfo given
         res <- tableau (depth+1) clp
         case (res) of
          SAT        -> do return SAT                       -- stop there and return SAT
          UNSAT      -> chooseBranch tl depth (width+1) clp -- examine next


          TIMEOUT    -> error $ "shouldn't happen"
chooseBranch [] depth width clp
  = do liftIO $ vPutStrLn ("\n>> Stop width at level " ++ show depth ++ " width " ++ show width) ((logState clp)||(logRules clp))
       return UNSAT

-- like hylores' logstate. will be more developped.
logMe :: BranchMonad ()
logMe = do liftStats $ printOutInspectionMetrics
           liftStats $ modify updateStep  -- not very elegant to call it explicitely and here



liftStats  = lift
liftIO = lift . lift