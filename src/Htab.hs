module Main (main)

where

import System.Environment
import HyLoLexer(hyloLexer)
import HyLoParse
import CommandLine
import Branch
import Rules
import Timeout
import Statistics
import Control.Monad.State
import System.CPUTime(getCPUTime)

data SatFlag = SAT | UNSAT | TIMEOUT
 deriving Show

main :: IO ()
main =
    do {
        confhyloresrc <- getConf initialParams;
        args <- getArgs;
        let clp = parseParams confhyloresrc args in

        if ( paramsOk clp )
        then do {
                 start <- getCPUTime;
                 fstr <- readFile (filename clp);
                 case (parse . hyloLexer $ fstr)
                 of {
                     branchInfo ->
                        do result <- if (not ((maxtimeout clp) == 0))
                                        then timeout (maxtimeout clp)
                                                     (algoStart branchInfo clp)
                                                    (return (TIMEOUT, Nothing))
                                        else (algoStart branchInfo clp);

                           case result of
                               (SAT, Just stats)    -> (putStrLn "SAT" >>
                                                       printOutAllMetrics' stats)
                               (UNSAT, Just stats)  -> (putStrLn "UNSAT" >>
                                                       printOutAllMetrics' stats)
                               (TIMEOUT, Nothing)   -> (putStrLn "TIMEOUT")
                               _                    -> error ("Unexpected response: (" ++ show (fst result) ++ ", *)")

                           end <- getCPUTime
                           putStr "Elapsed time: "
                           print ((fromInteger (end - start)) / 1000000000000 :: Double)

                    }
                }
        else showHelp;
       }


algoStart :: BranchInfo -> CmdLineParams -> IO (SatFlag,Maybe Statistics)
algoStart bi clp = do vPutStrLn ">> Starting rules application"
                                       ((logState clp)||(logRules clp));
                      res <- initStatsState  (algoReallyStart bi 0 clp)
                      case res of
                       (satflag,stats) -> return (satflag, Just stats) -- for now, no useful stats
 where initStatsState = initialStatisticsStateFor runStateT


algoReallyStart :: BranchInfo -> Int -> CmdLineParams -> StateT Statistics IO SatFlag
algoReallyStart bi depth clp =
 do configureMetrics clp               -- knows from the command line which statistics will be displayed
    algoLoopCount bi depth clp


algoLoopCount :: BranchInfo -> Int -> CmdLineParams -> StateT Statistics IO SatFlag
algoLoopCount bi depth clp =
      do logMe
         let showState = (logState clp)
         let showRules = (logRules clp)
         case bi of
          BranchOK br -> do lift $ vPutStrLn (show br) showState
                            let listOfRules = applicableRules br
                            let r = chooseRule listOfRules
                            case r of
                             Just rule -> do lift $ vPutStrLn ("\n>> Rule : " ++ (show rule)) showRules
                                             let possibleBranches = applyRule rule br
                                             chooseBranch possibleBranches depth 0 clp
                             Nothing   -> do lift $ vPutStrLn "\n>> Saturated open branch" (showState || showRules)
                                             return SAT
          BranchClash br pf -> do lift $ vPutStrLn (show br) showState
                                  lift $ vPutStrLn ("\nClasher : " ++ (show pf)) showState
                                  recordClosedBranch -- increment counter by modifying the Statistics monad
                                  return UNSAT


-- dumb rule-choosing strategy
chooseRule :: [Rule] -> Maybe Rule
chooseRule (hd:_)  = Just hd
chooseRule [] = Nothing

-- dumb depth-first strategy
chooseBranch :: [BranchInfo] -> Int -> Int -> CmdLineParams ->  StateT Statistics IO SatFlag
chooseBranch (hd:tl) depth width clp
    = do let showState = (logState clp)
         let showRules = (logRules clp)
         lift $ vPutStrLn ("\n>> Depth #" ++ (show depth) ++ " Width #" ++ (show width)) (showState || showRules)
         alcRes <- algoLoopCount hd (depth+1) clp
         case (alcRes) of
          SAT        -> do return  SAT                      -- stop there and return SAT
          UNSAT      -> chooseBranch tl depth (width+1) clp -- examine next
          TIMEOUT    -> error $ "shouldn't happen"
chooseBranch [] depth width clp
  = do lift $ vPutStrLn ("\n>> Stop width at level " ++ show depth ++ " width " ++ show width) ((logState clp)||(logRules clp))
       return UNSAT


vPutStrLn :: String -> Bool -> IO ()
vPutStrLn s b = if b then putStrLn s
                     else return ()




-- like hylores' logstate. will be more developped.
logMe :: StateT Statistics IO ()
logMe = do printOutInspectionMetrics
           modify updateStep  -- not very elegant to call it explicitely and here