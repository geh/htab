module HTab.Main

( runWithParams, TaskRunFlag(..))

where
import Control.Applicative ( (<$>) )
import Control.Monad       ( when )
import Control.Monad.State( runStateT )

import System.Console.CmdArgs ( whenNormal, whenLoud )

import System.IO           ( hSetBuffering, stdin, BufferMode(LineBuffering)) 
import System.CPUTime( getCPUTime )
import qualified System.Timeout as T
import System.IO.Strict ( readFile )
import Prelude hiding ( readFile )

import HyLo.InputFile.Parser ( QueryType(..) )

import HTab.CommandLine( filename, timeout, Params, genModel, showFormula )
import HTab.Branch( BranchInfo(..), emptyBranch, addFirstFormulas)
import HTab.Statistics( Statistics, initialStatisticsStateFor, printOutMetricsFinal )
import HTab.Tableau( OpenFlag(..), tableauStart )
import HTab.Formula( formulaLanguageInfo, Theory, RelInfo, Encoding, Task,
                     Formula, encodeValidityTest, encodeSatTest, encodeRetrieveTask,
                     toNomSymbol, showRelInfo )
import qualified HTab.Formula as F
import HTab.ModelGen ( Model )

data TaskRunFlag = SUCCESS | FAILURE

runWithParams :: Params -> IO (Maybe TaskRunFlag)
runWithParams p =
 time "Total time: "
  $ do
     let fromStdIn = do myPutStrLn $ "Reading from stdin (run again with" ++
                                     "`--help' for usage options)"
                        hSetBuffering stdin LineBuffering
                        getContents

     let parse = \i -> if head (words i)  == "begin"
                        then F.simpleParse p i else F.parse p i
     allTasks <- parse <$> maybe fromStdIn readFile (filename p)
     --
     result <- if timeout p == 0
                then Just <$> runTasks allTasks p
                else T.timeout (timeout p * (10::Int)^(6::Int))
                               (runTasks allTasks p)
     --
     case result of
        Nothing      -> myPutStrLn "\nTimeout.\n"
        Just SUCCESS -> myPutStrLn "\nAll tasks successful.\n"
        Just FAILURE -> myPutStrLn "\nOne task failed.\n"
     --
     return result

--

runTasks :: (Theory,RelInfo,Encoding,[Task]) -> Params -> IO TaskRunFlag
runTasks allTasks@(theory,relInfo,encoding,tasks) p =
 do
    myPutStrLn "== Checking theory satisfiability =="
    res <- runOneTask (Satisfiable, genModel p,[]) relInfo encoding theory p
    case res of
     SUCCESS | null tasks -> return SUCCESS
             | otherwise  -> do myPutStrLn "\n==         Starting tasks         =="
                                res2 <- runTasks2 allTasks p
                                myPutStrLn "\n==         End of   tasks         =="
                                return res2
     FAILURE              -> return FAILURE

--

runTasks2 :: (Theory,RelInfo,Encoding,[Task]) -> Params -> IO TaskRunFlag
runTasks2 (_,_,_,[]) _                  = error "runTasks2 empty list error"
runTasks2 (theory,relInfo,encoding,(hd:tl)) p =
 do res <- runOneTask hd relInfo encoding theory p
    case res of
      SUCCESS | null tl   -> return SUCCESS
              | otherwise -> runTasks2 (theory,relInfo,encoding,tl) p
      FAILURE             -> do _ <- runTasks2 (theory,relInfo,encoding,tl) p
                                return FAILURE

--

runOneTask :: Task -> RelInfo -> Encoding -> Formula -> Params -> IO TaskRunFlag
runOneTask (query,mOutFile,fs) relInfo encoding theory p =
 time "Task time:"
 $ do
     myPutStrLn $ "\n* " ++ case query of {Valid       -> "Validity task";
                                           Satisfiable -> "Satisfiability task";
                                           Retrieve    -> "Instance retrieval task"}
     --
     result <-
      case query of
        Retrieve
          ->
            do let fLang = formulaLanguageInfo theory encoding
               let initialBranch = emptyBranch p fLang relInfo encoding
               let (noms,encfs) = encodeRetrieveTask relInfo encoding fLang theory fs
               --
               myPutStrLn $ "Instances making true: " ++ show fs
               --
               results <- mapM (tableauInit p . addFirstFormulas p initialBranch fLang) encfs
               let goodnoms = [ toNomSymbol encoding n | (n,(CLOSED _ ,_))  <- zip noms results]
               myPutStrLn $ show goodnoms
               let doWrite f = do writeFile f (show goodnoms ++ "\n")
                                  myPutStrLn ("Nominals saved as " ++ f)
               maybe (return ()) doWrite mOutFile
               return SUCCESS

        valOrSat
          ->
            do let f = case valOrSat of
                        Valid       -> encodeValidityTest relInfo encoding theory fs
                        Satisfiable -> encodeSatTest      relInfo encoding theory fs
                        _           -> error "never happens"
               --
               when (showFormula p)
                  $ myPutStrLn
                         $ unlines ["Input for SAT test:",
                                    "{ " ++ show f ++ " }",
                                    "End of input",
                                    "Relations properties :" ++ showRelInfo relInfo ]
               --
               let fLang         = formulaLanguageInfo f encoding
               let initialBranch = emptyBranch p fLang relInfo encoding
               let branchInfo    = addFirstFormulas p initialBranch fLang f
               --
               result <- tableauInit p branchInfo
               --
               case result of
                  (OPEN m, stats)   -> do myPutStrLn $
                                            case query of
                                                Valid       -> "The formula is not valid."
                                                Satisfiable -> "The formula is satisfiable."
                                                _           -> error "never happens"
                                          saveGenModel mOutFile m
                                          whenNormal $ printOutMetricsFinal stats
                                          return SUCCESS
                  (CLOSED _, stats) -> do myPutStrLn $
                                            case query of
                                                Valid       -> "The formula is valid."
                                                Satisfiable -> "The formula is unsatisfiable."
                                                _           -> error "never happens"
                                          whenNormal $ printOutMetricsFinal stats
                                          return FAILURE
     --
     return $ case (query, result) of
               (Satisfiable, SUCCESS ) -> SUCCESS
               (Satisfiable, FAILURE ) -> FAILURE
               (Valid      , SUCCESS ) -> FAILURE
               (Valid      , FAILURE ) -> SUCCESS
               (Retrieve   , _       ) -> SUCCESS

--

saveGenModel :: Maybe FilePath -> Model -> IO ()
saveGenModel mOutFile m = maybe (return ()) doWrite mOutFile
    where doWrite f = do writeFile f (show m)
                         myPutStrLn ("Model saved as " ++ f)

tableauInit :: Params -> BranchInfo -> IO (OpenFlag,Statistics)
tableauInit p bi =
        do whenLoud $ putStrLn ">> Starting rules application"
           initStatsState $ tableauStart p bi
 where initStatsState  = initialStatisticsStateFor runStateT

--

time :: String -> IO a -> IO a
time message action =
  do start  <- getCPUTime
     result <- action
     end <- getCPUTime
     let elapsedTime = fromInteger (end - start) / 1000000000000.0
     myPutStrLn $ message ++ show (elapsedTime :: Double)
     return result


myPutStrLn :: String -> IO ()
myPutStrLn str = do whenNormal $ putStrLn str

