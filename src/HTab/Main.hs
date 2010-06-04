module HTab.Main

( runWithParams, TaskRunFlag(..))

where
import Control.Applicative ( (<$>) )
import Control.Monad       ( unless, when )
import Control.Monad.State( runStateT )
import Control.Monad.Reader( runReaderT )

import System.IO           ( hSetBuffering, stdin, BufferMode(LineBuffering)) 
import System.CPUTime( getCPUTime )

import HyLo.InputFile.Parser ( QueryType(..) )

import HTab.CommandLine( filename, maxtimeout, CmdLineParams, logState, genModel, backJumping,
                         quietMode, simpleInput, showFormula )
import HTab.Branch( BranchInfo(..),initialBranchStateFor, BranchData(..),
                    emptyBranch, addFirstFormulas)
import HTab.Statistics( Statistics, initialStatisticsStateFor, printOutAllMetrics' )
import HTab.Base( vPutStrLn )
import HTab.Tableau( OpenFlag(..), tableauStart )
import HTab.Formula( formulaLanguageInfo, languageTrans, Theory, RelInfo, Encoding, Task,
                     Formula, encodeValidityTest, encodeSatTest, encodeRetrieveTask,
                     showRelInfo )
import qualified HTab.Formula as F
import HTab.ModelGen ( Model )

import HTab.Timeout ( withNoTimeout, notifyOnTimeout, TimeoutSignal )


data TaskRunFlag = SUCCESS | FAILURE | TIMEOUT_

runWithParams :: CmdLineParams -> IO TaskRunFlag
runWithParams clp =
 time clp "Total time: "
  $ do
     let myPutStrLn str = vPutStrLn str (not $ quietMode clp)
     --
     let fromStdIn = do myPutStrLn $ "Reading from stdin (run again with" ++
                                     "`--help' for usage options)"
                        hSetBuffering stdin LineBuffering
                        getContents

     let parse = \i -> if simpleInput clp || head (words i)  == "begin"
                        then F.simpleParse clp i else F.parse clp i
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

runTasks :: (Theory,RelInfo,Encoding,[Task]) -> CmdLineParams -> TimeoutSignal ->  IO TaskRunFlag
runTasks allTasks@(theory,relInfo,encoding,tasks) clp ts =
 do
    let myPutStrLn str = vPutStrLn str (not $ quietMode clp)
    myPutStrLn "== Checking theory satisfiability =="
    res <- runOneTask (Satisfiable, genModel clp,[]) relInfo encoding theory clp ts
    case res of
     SUCCESS | null tasks -> return SUCCESS
             | otherwise  -> do myPutStrLn "\n==         Starting tasks         =="
                                res2 <- runTasks2 allTasks clp ts
                                myPutStrLn "\n==         End of   tasks         =="
                                return res2
     failOrTimeout        -> return failOrTimeout

--

runTasks2 :: (Theory,RelInfo,Encoding,[Task]) -> CmdLineParams -> TimeoutSignal -> IO TaskRunFlag
runTasks2 (_,_,_,[]) _ _                  = error "runTasks2 empty list error"
runTasks2 (theory,relInfo,encoding,(hd:tl)) clp ts =
 do res <- runOneTask hd relInfo encoding theory clp ts
    case res of
      SUCCESS | null tl   -> return SUCCESS
              | otherwise -> runTasks2 (theory,relInfo,encoding,tl) clp ts
      failOrTimeout       -> do _ <- runTasks2 (theory,relInfo,encoding,tl) clp ts
                                return failOrTimeout

--

runOneTask :: Task -> RelInfo -> Encoding -> Formula -> CmdLineParams -> TimeoutSignal -> IO TaskRunFlag
runOneTask (query,mOutFile,fs) relInfo encoding theory clp ts=
 time clp "Task time:"
 $ do
     let myPutStrLn str = vPutStrLn str (not $ quietMode clp)
     --
     myPutStrLn $ "\n* " ++ case query of {Valid       -> "Validity task";
                                           Satisfiable -> "Satisfiability task";
                                           Retrieve    -> "Instance retrieval task"}
     --
     result <-
      case query of
        Retrieve
          ->
            do let fLang = formulaLanguageInfo theory
               let initialBranch = emptyBranch clp fLang relInfo encoding
               let (noms,encfs) = encodeRetrieveTask relInfo encoding fLang theory fs
               --
               myPutStrLn $ "Instances making true: " ++ show fs
               --
               results <- mapM (tableauInit clp ts . addFirstFormulas clp initialBranch fLang) encfs
               if not $ null [ TIMEOUT | (TIMEOUT,_)  <- results]
                 then do myPutStrLn "TIMEOUT"
                         return TIMEOUT_
                 else do let goodnoms = [ n | (n,(CLOSED _ ,_))  <- zip noms results]
                         myPutStrLn $ show goodnoms
                         let doWrite f = do writeFile f (show goodnoms ++ "\n")
                                            unless (quietMode clp) $ vPutStrLn ("Nominals saved as " ++ f) (logState clp)
                         maybe (return ()) doWrite mOutFile
                         return SUCCESS

        valOrSat
          ->
            do let f = case valOrSat of
                        Valid       -> encodeValidityTest relInfo encoding theory fs
                        Satisfiable -> encodeSatTest      relInfo encoding theory fs
                        _           -> error "never happens"
               --
               f `seq` when (showFormula clp)
                        $ myPutStrLn
                         $ unlines ["Input for SAT test:",
                                    "{ " ++ show f ++ " }",
                                    "End of input",
                                    "Relations properties :" ++ showRelInfo relInfo ]
               --
               let fLang         = formulaLanguageInfo f
               let initialBranch = emptyBranch clp fLang relInfo encoding
               let branchInfo    = addFirstFormulas clp initialBranch fLang f
               let clp2          = if languageTrans fLang then clp{backJumping=False} else clp
               --
               result <- tableauInit clp2 ts branchInfo
               --
               case result of
                  (OPEN m, stats)   -> do myPutStrLn $
                                            case query of
                                                Valid       -> "The formula is not valid."
                                                Satisfiable -> "The formula is satisfiable."
                                                _           -> error "never happens"
                                          saveGenModel clp mOutFile m
                                          unless (quietMode clp) $
                                             printOutAllMetrics' stats
                                          return SUCCESS
                  (CLOSED _, stats) -> do myPutStrLn $
                                            case query of
                                                Valid       -> "The formula is valid."
                                                Satisfiable -> "The formula is unsatisfiable."
                                                _           -> error "never happens"
                                          unless (quietMode clp) $
                                             printOutAllMetrics' stats
                                          return FAILURE
                  (TIMEOUT, stats)  -> do myPutStrLn "TIMEOUT"
                                          unless (quietMode clp) $
                                             printOutAllMetrics' stats
                                          return TIMEOUT_
     --
     return $ case (query, result) of
               (     _     , TIMEOUT_) -> TIMEOUT_
               (Satisfiable, SUCCESS ) -> SUCCESS
               (Satisfiable, FAILURE ) -> FAILURE
               (Valid      , SUCCESS ) -> FAILURE
               (Valid      , FAILURE ) -> SUCCESS
               (Retrieve   , _       ) -> SUCCESS

--

saveGenModel :: CmdLineParams -> Maybe FilePath -> Model -> IO ()
saveGenModel clp mOutFile m = maybe (return ()) doWrite mOutFile
    where doWrite f = do writeFile f (show m)
                         unless (quietMode clp) $ vPutStrLn ("Model saved as " ++ f) (logState clp)

tableauInit :: CmdLineParams -> TimeoutSignal -> BranchInfo -> IO (OpenFlag,Statistics)
tableauInit clp ts bi =
        do vPutStrLn ">> Starting rules application" (logState clp)
           initStatsState $ initBranchState bd $ tableauStart clp bi
 where initStatsState  = initialStatisticsStateFor runStateT
       initBranchState = initialBranchStateFor runReaderT
       bd              = BranchData
                          { branch_clp  = clp,
                            timeout_signal = ts
			    }

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

