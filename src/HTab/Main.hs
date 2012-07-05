module HTab.Main

( runWithParams, TaskRunFlag(..))

where
import Control.Applicative ( (<$>) )
import Control.Monad       ( when )
import Control.Monad.State( runStateT )

import System.Console.CmdArgs ( whenNormal, whenLoud )

import System.CPUTime( getCPUTime )
import qualified System.Timeout as T
import System.IO.Strict ( readFile )
import Prelude hiding ( readFile )

import HyLo.InputFile.Parser ( QueryType(..) )

import HTab.CommandLine( filename, timeout, Params, genModel, dotModel, showFormula )
import HTab.Branch( BranchInfo(..), initialBranch)
import HTab.Statistics( Statistics, initialStatisticsStateFor, printOutMetricsFinal )
import HTab.Tableau( OpenFlag(..), tableauStart )
import HTab.Formula( formulaLanguageInfo, Theory, RelInfo, Encoding, Task,
                     Formula, encodeValidityTest, encodeSatTest, encodeRetrieveTask,
                     toNomSymbol, showRelInfo )
import qualified HTab.Formula as F
import HTab.ModelGen ( Model, toDot )

data TaskRunFlag = SUCCESS | FAILURE

runWithParams :: Params -> IO (Maybe TaskRunFlag)
runWithParams p =
 time "Total time: "
  $ do
     let parse i = if head (words i)  == "begin"
                        then F.simpleParse p i else F.parse p i
     allTasks <- parse <$> readFile (filename p)
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
    res <- time "Task time:"
            $ runTask (Satisfiable, genModel p,[]) relInfo encoding theory p
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
 do res <- time "Task time:" $ runTask hd relInfo encoding theory p
    case res of
      SUCCESS | null tl   -> return SUCCESS
              | otherwise -> runTasks2 (theory,relInfo,encoding,tl) p
      FAILURE             -> do _ <- runTasks2 (theory,relInfo,encoding,tl) p
                                return FAILURE

--

runTask :: Task -> RelInfo -> Encoding -> Formula -> Params -> IO TaskRunFlag
runTask (Retrieve,mOutFile,fs) relInfo encoding theory p =
 do myPutStrLn "\n* Instance retrieval task"
    let fLang = formulaLanguageInfo encoding
    let (noms,encfs) = encodeRetrieveTask relInfo encoding fLang theory fs
    --
    myPutStrLn $ "Instances making true: " ++ show fs
    --
    results <- mapM (tableauInit p . initialBranch p fLang relInfo encoding) encfs
    let goods = [ toNomSymbol encoding n | (n,(CLOSED _ ,_)) <- zip noms results]
    myPutStrLn $ show goods
    let doWrite f = do writeFile f (show goods ++ "\n")
                       myPutStrLn ("Nominals saved as " ++ f)
    maybe (return ()) doWrite mOutFile
    return SUCCESS

runTask (Satisfiable,mOutFile,fs) relInfo encoding theory p =
 do myPutStrLn "\n* Satisfiability task"
    let f = encodeSatTest relInfo encoding theory fs
    --
    when (showFormula p)
       $ myPutStrLn
              $ unlines ["Input for SAT test:",
                         "{ " ++ show f ++ " }",
                         "End of input",
                         "Relations properties :" ++ showRelInfo relInfo ]
    --
    let fLang         = formulaLanguageInfo encoding
    --
    (result,stats) <- tableauInit p $ initialBranch p fLang relInfo encoding f
    --
    whenNormal $ printOutMetricsFinal stats
    --
    case result of
       OPEN m   -> do myPutStrLn "The formula is satisfiable."
                      saveGenModel mOutFile p m
                      return SUCCESS
       CLOSED _ -> do myPutStrLn "The formula is unsatisfiable."
                      return FAILURE

runTask (Valid,mOutFile,fs) relInfo encoding theory p =
 do myPutStrLn "\n* Validity task"
    let f = encodeValidityTest relInfo encoding theory fs
    --
    when (showFormula p)
       $ myPutStrLn
              $ unlines ["Input for SAT test:",
                         "{ " ++ show f ++ " }",
                         "End of input",
                         "Relations properties :" ++ showRelInfo relInfo ]
    --
    let fLang         = formulaLanguageInfo encoding
    --
    (result,stats) <- tableauInit p $ initialBranch p fLang relInfo encoding f
    --
    whenNormal $ printOutMetricsFinal stats
    --
    case result of
       OPEN m   -> do myPutStrLn "The formula is not valid."
                      saveGenModel mOutFile p m
                      return FAILURE
       CLOSED _ -> do myPutStrLn "The formula is valid."
                      return SUCCESS

runTask (Counting,_,_) _ _ _ _ =
 do myPutStrLn "\n* Counting task is NOT supported"
    return FAILURE

--

saveGenModel :: Maybe FilePath -> Params -> Model -> IO ()
saveGenModel mOutFile p m = maybe (return ()) doWrite mOutFile
    where doWrite f = do writeFile f output
                         myPutStrLn ("Model saved as " ++ f)
          output | dotModel p = toDot m
                 | otherwise  = show m

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
myPutStrLn str = whenNormal $ putStrLn str

