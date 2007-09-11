module Main (main)

where

import System.Environment(getArgs)
import HyLoLexer(hyloLexer)
import HyLoParse(parse)
import CommandLine(getConf,initialParams,paramsOk, filename, parseParams,
                   maxtimeout, showHelp, CmdLineParams, logState, genModel,
                   configureMetrics,fullClash)
import Branch(BranchInfo,initialBranchStateFor,BranchMonad, BranchData(..),
              addFormula,emptyBranch)
import Timeout(timeout)
import Statistics(Statistics, initialStatisticsStateFor, printOutAllMetrics')
import Control.Monad.State(runStateT)
import System.CPUTime(getCPUTime)
import Base(vPutStrLn)
import Tableau(liftStats, tableau, OpenFlag(..))
import Formula(nnf,prefix,formulaLanguageInfo,renameNominals)
import LatexOutput
import ModelGen ( HerbrandModel, inducedModel )

data SatFlagAndStats = SAT HerbrandModel Statistics | UNSAT Statistics | TIMEOUT

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
                   do let fLang = formulaLanguageInfo f
                      latexInit clp
                      let f2 = renameNominals $ if (fullClash clp) then f else nnf f
                      putStr ("\nInput:\n{ " ++ (show f2) ++" }\nEnd of input\n\n");
                      let branchInfo = addFormula clp
                                                  (emptyBranch fLang)
                                                  (prefix 0 f2)
                      result <- if (not ((maxtimeout clp) == 0))
                                   then timeout (maxtimeout clp)
                                               (tableauInit branchInfo clp)
                                               (return TIMEOUT)
                                   else (tableauInit branchInfo clp)

                      case result of
                       SAT m stats -> (putStrLn "The formula is satisfiable." >>
                                       saveGenModel clp m >>
                                       printOutAllMetrics' stats)
                       UNSAT stats -> (putStrLn "The formula is unsatisfiable." >>
                                       printOutAllMetrics' stats)
                       TIMEOUT     -> (putStrLn "TIMEOUT")

                      end <- getCPUTime
                      putStr "Elapsed time: "
                      print ((fromInteger (end - start)) / 1000000000000 :: Double)
                      latexEnd clp

        else showHelp


tableauInit :: BranchInfo -> CmdLineParams -> IO (SatFlagAndStats)
tableauInit bi clp =
        do vPutStrLn ">> Starting rules application" (logState clp)
           res <- initStatsState $ initBranchState bd $ tableauStart clp
           case res of
            ((OPEN m,_),stats)   -> return $ SAT m stats
            ((CLOSED,_),stats) -> return $ UNSAT stats
 where initStatsState  = initialStatisticsStateFor runStateT
       initBranchState = initialBranchStateFor runStateT
       bd              = BranchData
                          { branch_info = bi,
                            branch_clp  = clp,
                            branch_path = [0]}

tableauStart :: CmdLineParams -> BranchMonad OpenFlag
tableauStart clp =
 do liftStats $ configureMetrics clp    -- knows from the command line which statistics will be displayed
    tableau


saveGenModel :: CmdLineParams -> HerbrandModel -> IO ()
saveGenModel clp m = maybe (return ()) doWrite (genModel clp)
    where doWrite f = do writeFile f (show . inducedModel $ m)
                         putStrLn $ "Model saved as " ++ f
