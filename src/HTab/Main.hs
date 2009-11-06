module HTab.Main

( runWithParams, TaskRunFlag(..))

where
import Control.Applicative ( (<$>) )
import Control.Monad       ( unless, when )
import Control.Monad.State( runStateT )

import System.IO           ( hSetBuffering, stdin, BufferMode(LineBuffering)) 
import System.CPUTime( getCPUTime )

import HyLo.InputFile.Parser ( QueryType(..) )

import HTab.CommandLine( filename, maxtimeout, CmdLineParams, logState, genModel,
                         configureMetrics, quietMode, simpleInput, showFormula )
import HTab.Branch( BranchInfo(..),initialBranchStateFor,BranchMonad, BranchData(..),
                    emptyBranch, addFirstFormulas,initUnsatCache )
import HTab.Statistics( Statistics, initialStatisticsStateFor, printOutAllMetrics' )
import HTab.Base( vPutStrLn )
import HTab.Tableau( liftStats, tableau, OpenFlag(..) )
import HTab.Formula( formulaLanguageInfo, Theory, RelInfo, Task,
                     Formula, encodeValidityTest, encodeSatTest, showRelInfo )
import qualified HTab.Formula as F
import HTab.ModelGen ( Model )

import HTab.Timeout ( withNoTimeout, notifyOnTimeout, TimeoutSignal )


data TaskRunFlag = SUCCESS | FAILURE | TIMEOUT_

runWithParams :: CmdLineParams -> IO (TaskRunFlag)
runWithParams clp =
 time clp "Total time: "
  $ do
     let myPutStrLn str = vPutStrLn str (not $ quietMode clp)
     --
     let fromStdIn = do myPutStrLn $ "Reading from stdin (run again with" ++
                                     "`--help' for usage options)"
                        hSetBuffering stdin LineBuffering
                        getContents

     let parse = if simpleInput clp then F.simpleParse clp else F.parse clp
     allTasks <- parse <$> maybe fromStdIn readFile (filename clp)
     --
     let handleTimeout
          | maxtimeout clp > 0 = notifyOnTimeout (maxtimeout clp)
          | otherwise          = withNoTimeout
     --
     result <- handleTimeout (runTasks allTasks clp)
     --
     case result of
        SUCCESS  -> myPutStrLn "\nAll tasks successful.\n"
        FAILURE  -> myPutStrLn "\nOne task failed.\n"
        TIMEOUT_ -> myPutStrLn "\nTimeout.\n"
     --
     return result

--

runTasks :: (Theory,RelInfo,[Task]) -> CmdLineParams -> TimeoutSignal ->  IO (TaskRunFlag)
runTasks allTasks@(theory,relInfo,tasks) clp ts =
 do
    let myPutStrLn str = vPutStrLn str (not $ quietMode clp)
    myPutStrLn "== Checking theory satisfiability =="
    res <- runOneTask (Satisfiable, genModel clp,[]) relInfo theory clp ts
    case res of
     SUCCESS | length tasks == 0 -> return SUCCESS
             | otherwise         -> do myPutStrLn "\n==         Starting tasks         =="
                                       res2 <- runTasks2 allTasks clp ts
                                       myPutStrLn "\n==         End of   tasks         =="
                                       return res2
     failOrTimeout               -> return failOrTimeout

--

runTasks2 :: (Theory,RelInfo,[Task]) -> CmdLineParams -> TimeoutSignal -> IO (TaskRunFlag)
runTasks2 (_,_,[]) _ _                    = error "runTasks2 empty list error"
runTasks2 (theory,relInfo,(hd:tl)) clp ts =
 do res <- runOneTask hd relInfo theory clp ts
    case res of
      SUCCESS | length tl == 0 -> return SUCCESS
              | otherwise      -> runTasks2  (theory,relInfo,tl) clp ts
      failOrTimeout            -> return failOrTimeout

--

runOneTask :: Task -> RelInfo -> Formula -> CmdLineParams -> TimeoutSignal -> IO (TaskRunFlag)
runOneTask (query,mOutFile,fs) relInfo theory clp ts=
 time clp "Task time:"
 $ do
     let myPutStrLn str = vPutStrLn str (not $ quietMode clp)
     --
     myPutStrLn $ "\n* " ++ case query of {Valid -> "Validity task"; Satisfiable -> "Satisfiability task"}
     --
     let f = case query of { Valid -> encodeValidityTest relInfo theory fs ; Satisfiable -> encodeSatTest relInfo theory fs}
     --
     f `seq` when (showFormula clp)
              $ myPutStrLn
               $ unlines ["Input for SAT test:",
                          "{ " ++ show f ++ " }",
                          "End of input",
                          "Relations properties :" ++ showRelInfo relInfo ]
     --
     let fLang         = formulaLanguageInfo f
     let initialBranch = emptyBranch clp fLang relInfo
     let branchInfo    = addFirstFormulas clp initialBranch f fLang
     --
     result <- tableauInit branchInfo clp ts
     --
     case result of
        (OPEN m, stats)   -> do myPutStrLn $
                                  case query of
                                      Valid       -> "The formula is not valid."
                                      Satisfiable -> "The formula is satisfiable."
                                saveGenModel clp mOutFile m
                                unless (quietMode clp) $
                                   printOutAllMetrics' stats
        (CLOSED _, stats) -> do myPutStrLn $
                                  case query of
                                      Valid       -> "The formula is valid."
                                      Satisfiable -> "The formula is unsatisfiable."
                                unless (quietMode clp) $
                                   printOutAllMetrics' stats
        (TIMEOUT, stats)  -> do myPutStrLn "TIMEOUT"
                                unless (quietMode clp) $
                                   printOutAllMetrics' stats
     --
     return $ case (query, fst result) of
               (     _     , TIMEOUT ) -> TIMEOUT_
               (Satisfiable, OPEN   _) -> SUCCESS
               (Satisfiable, CLOSED _) -> FAILURE
               (Valid      , OPEN   _) -> FAILURE
               (Valid      , CLOSED _) -> SUCCESS

--

saveGenModel :: CmdLineParams -> (Maybe FilePath) -> Model -> IO ()
saveGenModel clp mOutFile m = maybe (return ()) doWrite mOutFile
    where doWrite f = do writeFile f (show m)
                         unless (quietMode clp) $ vPutStrLn ("Model saved as " ++ f) (logState clp)

tableauInit :: BranchInfo -> CmdLineParams -> TimeoutSignal -> IO (OpenFlag,Statistics)
tableauInit bi clp ts =
        do vPutStrLn ">> Starting rules application" (logState clp)
           ((openflag,_),stats) <- initStatsState $ initBranchState bd $ tableauStart clp
           return (openflag,stats)
 where initStatsState  = initialStatisticsStateFor runStateT
       initBranchState = initialBranchStateFor runStateT
       bd              = BranchData
                          { branch_info = bi,
                            branch_clp  = clp,
                            timeout_signal = ts,
			    unsat_cache = initUnsatCache clp,
                            disjunctPrefixes = []
			    }

tableauStart :: CmdLineParams -> BranchMonad OpenFlag
tableauStart clp =
 do liftStats $ configureMetrics clp
    let initialPath = [0]
    tableau initialPath

--

time :: CmdLineParams -> String -> IO a -> IO a
time clp message action =
  do start  <- getCPUTime
     result <- action
     end <- getCPUTime
     let elapsedTime = fromInteger (end - start) / 1000000000000.0
     let myPutStrLn str = vPutStrLn str (not $ quietMode clp)
     myPutStrLn $ message ++ show (elapsedTime :: Double)
     return result

