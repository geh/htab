module Tableau where

import Base(vPutStrLn)
import Control.Monad.State(lift,modify, put, get)
import Statistics(updateStep,printOutInspectionMetrics,recordClosedBranch)
import Branch(BranchInfo(..),BranchMonad)
import CommandLine(logRules,logState,CmdLineParams)
import Rules(Rule,applyRule,applyToMonad, applicableRules, howManyBranches)

--

data SatFlag = SAT | UNSAT | TIMEOUT
 deriving Show

--

tableau :: Int -> BranchMonad SatFlag
tableau depth =
      do logMe
         (bi,clp) <- get
         let showState = (logState clp)
         let showRules = (logRules clp)
         let showSome = (showState || showRules)
         case bi of
          BranchClash br pf ->
           do liftIO $ vPutStrLn (show br) showState
              liftIO $ vPutStrLn ("\nClasher : " ++ (show pf)) showState
              liftStats $ recordClosedBranch
              return UNSAT

          BranchOK br ->
           do liftIO $ vPutStrLn (show br) showState
              let listOfRules = applicableRules br
              let r = chooseRule listOfRules
              case r of
               Just rule ->
                do liftIO $ vPutStrLn ("\n>> Rule : " ++ (show rule)) showRules
                   if (howManyBranches rule) > 1
                      then do let possibleBranches = applyRule rule br
                              chooseBranch possibleBranches depth 0
                      else do applyToMonad rule
                              tableau (depth+1)
               Nothing   ->
                do liftIO $ vPutStrLn "\n>> Saturated open branch" showSome
                   return SAT


-- dumb rule-choosing strategy
chooseRule :: [Rule] -> Maybe Rule
chooseRule (hd:_)  = Just hd
chooseRule [] = Nothing

-- dumb depth-first strategy
chooseBranch :: [BranchInfo] -> Int -> Int  -> BranchMonad SatFlag
chooseBranch (hd:tl) depth width
    = do (_,clp) <- get
         let showState = (logState clp)
         let showRules = (logRules clp)
         let showSome = (showState || showRules)
         liftIO $ vPutStrLn ("\n>> Depth #" ++ (show depth) ++ " Width #" ++ (show width))
                            showSome
         put (hd,clp)          -- overwrite the monad with the first branchinfo given  -- TODO use a more specialised function than put ?
         res <- tableau (depth+1)
         case (res) of
          SAT        -> do return SAT                   -- stop there and return SAT
          UNSAT      -> chooseBranch tl depth (width+1) -- examine next


          TIMEOUT    -> error $ "shouldn't happen"
chooseBranch [] depth width
  = do (_,clp) <- get
       liftIO $ vPutStrLn ("\n>> Stop width at level " ++ show depth ++ " width " ++ show width)
                          ((logState clp)||(logRules clp))
       return UNSAT

-- like hylores' logstate. will be more developped.
logMe :: BranchMonad ()
logMe = do liftStats $ printOutInspectionMetrics
           liftStats $ modify updateStep  -- not very elegant to call it explicitely and here

--

liftStats  = lift
liftIO = lift . lift