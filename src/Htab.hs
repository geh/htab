module Main (main)

where


import System.Environment(getArgs)
import HyLoLexer(hyloLexer)
import HyLoParse(parse)
import CommandLine(getConf,initialParams,paramsOk, filename, parseParams,
                   maxtimeout, showHelp, CmdLineParams, logState, logRules,
                   configureMetrics,fullClash)
import Branch(BranchInfo,initialBranchStateFor,BranchMonad, BranchData(..),
              addFormula,emptyBranch)
import Timeout(timeout)
import Statistics(Statistics, initialStatisticsStateFor, printOutAllMetrics')
import Control.Monad.State(runStateT)
import System.CPUTime(getCPUTime)
import Base(vPutStrLn)
import Tableau(liftStats, tableau, SatFlag(..))
import Formula(nnf,prefix)

main :: IO ()
main =
    do
      confhyloresrc <- getConf initialParams
      args <- getArgs
      let clp = parseParams confhyloresrc args

      if ( paramsOk clp )
        then do
               start <- getCPUTime;
               fstr <- readFile (filename clp);
               case (parse . hyloLexer $ fstr) of
                 f ->
                   do let f2 = if (fullClash clp) then f
                                                  else nnf f
                      let branchInfo = addFormula clp emptyBranch (prefix 0 f2)
                      result <- if (not ((maxtimeout clp) == 0))
                                   then timeout (maxtimeout clp)
                                               (tableauInit branchInfo clp)
                                               (return (TIMEOUT, Nothing))
                                   else (tableauInit branchInfo clp)

                      case result of
                       (SAT, Just stats)    -> (putStrLn "SAT" >>
                                               printOutAllMetrics' stats)
                       (UNSAT, Just stats)  -> (putStrLn "UNSAT" >>
                                               printOutAllMetrics' stats)
                       (TIMEOUT, Nothing)   -> (putStrLn "TIMEOUT")
                       _                    -> error ("Unexpected response: ("
                                                      ++ show (fst result)
                                                      ++ ", *)")

                      end <- getCPUTime
                      putStr "Elapsed time: "
                      print ((fromInteger (end - start)) / 1000000000000 :: Double)

        else showHelp


tableauInit :: BranchInfo -> CmdLineParams -> IO (SatFlag,Maybe Statistics)
tableauInit bi clp =
        do vPutStrLn ">> Starting rules application"
                      ((logState clp)||(logRules clp))
           res <- initStatsState $ initBranchState bd $ tableauStart clp
           case res of
            ((satflag,_),stats) -> return (satflag, Just stats)
 where initStatsState  = initialStatisticsStateFor runStateT
       initBranchState = initialBranchStateFor runStateT
       bd              = BranchData
                          { branch_info = bi,
                            branch_clp  = clp,
                            branch_path = [0]}

tableauStart :: CmdLineParams -> BranchMonad SatFlag
tableauStart clp =
 do liftStats $ configureMetrics clp    -- knows from the command line which statistics will be displayed
    tableau
