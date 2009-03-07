module HTab.Main

( runWithParams, SatFlagAndStats(..) )

where
import Control.Applicative ( (<$>) )
import Control.Monad       ( unless )
import Control.Monad.State( runStateT )

import System.IO           ( hSetBuffering, stdin, BufferMode(LineBuffering)) 
import System.CPUTime( getCPUTime )


import HTab.CommandLine( filename, maxtimeout, CmdLineParams, logState, genModel,
                         configureMetrics, quietMode, inclBlockGlobal, inclBlockChain,
                         immediateBlock )
import HTab.Branch( Branch, BranchInfo(..),initialBranchStateFor,BranchMonad, BranchData(..),
                    emptyBranch, lastPref, BlockingMode(..), addFormulas )
import HTab.Statistics( Statistics, initialStatisticsStateFor, printOutAllMetrics' )
import HTab.Base( vPutStrLn )
import HTab.Tableau( liftStats, tableau, OpenFlag(..) )
import HTab.Formula( firstPrefixedFormula, formulaLanguageInfo, bps_empty,
                     PrFormula(..), LanguageInfo(..), Formula(..),
                     nom, parse )
import HTab.ModelGen ( HerbrandModel, inducedModel )


import HTab.Timeout ( withNoTimeout, notifyOnTimeout, TimeoutSignal )

data SatFlagAndStats = SAT HerbrandModel Statistics | UNSAT Statistics | TIMEOUT Statistics


runWithParams :: CmdLineParams -> IO (SatFlagAndStats)
runWithParams clp =
 do  start <- getCPUTime
     --
     let myPutStrLn = if quietMode clp then const (return ()) else putStrLn
     --
     let fromStdIn = do myPutStrLn $ "Reading from stdin (run again with" ++
                                     "`--help' for usage options)"
                        hSetBuffering stdin LineBuffering
                        getContents

     f <- parse <$> maybe fromStdIn readFile (filename clp)
     --
     let fLang = formulaLanguageInfo f
     --
     f `seq` myPutStrLn ("\nInput:\n{ " ++ (show f) ++" }\nEnd of input\n\n");
     --
     let initialBranch = emptyBranch fLang blockMode (immediateBlock clp)
                          where blockMode
                                  = if inclBlockChain clp && (not $ inclBlockGlobal clp)
                                     then InclusionBlockingChain
                                     else InclusionBlockingGlobal
     let branchInfo    = addFirstFormulas clp initialBranch f fLang
     --
     let handleTimeout
          | (maxtimeout clp) > 0 = notifyOnTimeout (maxtimeout clp)
          | otherwise            = withNoTimeout
     --
     result <- handleTimeout (tableauInit branchInfo clp)
     --
     case result of
        SAT m stats   -> do myPutStrLn "The formula is satisfiable."
                            saveGenModel clp m
                            unless (quietMode clp) $
                                printOutAllMetrics' stats
        UNSAT stats   -> do myPutStrLn "The formula is unsatisfiable."
                            unless (quietMode clp) $
                                printOutAllMetrics' stats
        TIMEOUT stats -> do myPutStrLn "TIMEOUT"
                            unless (quietMode clp) $
                                printOutAllMetrics' stats

     --
     end <- getCPUTime
     let elapsedTime = fromInteger (end - start) / 1000000000000.0
     myPutStrLn $ "Elapsed time: " ++ show (elapsedTime :: Double)
     --
     return result

saveGenModel :: CmdLineParams -> HerbrandModel -> IO ()
saveGenModel clp m = maybe (return ()) doWrite (genModel clp)
    where doWrite f = do writeFile f (show . inducedModel $ m)
                         unless (quietMode clp) $ putStrLn $ "Model saved as " ++ f

tableauInit :: BranchInfo -> CmdLineParams -> TimeoutSignal -> IO (SatFlagAndStats)
tableauInit bi clp ts =
        do vPutStrLn ">> Starting rules application" (logState clp)
           res <- initStatsState $ initBranchState bd $ tableauStart clp
           case res of
            ((OPEN m,_),stats)   -> return $ SAT m stats
            ((CLOSED _,_),stats) -> return $ UNSAT stats
            ((TIMEOUT_,_),stats) -> return $ TIMEOUT stats
 where initStatsState  = initialStatisticsStateFor runStateT
       initBranchState = initialBranchStateFor runStateT
       bd              = BranchData
                          { branch_info = bi,
                            branch_clp  = clp,
                            branch_path = [0],
                            timeout_signal = ts}

tableauStart :: CmdLineParams -> BranchMonad OpenFlag
tableauStart clp =
 do liftStats $ configureMetrics clp
    tableau

-- preparation of the branch at the beginning of the calculus:
-- add the input formula at prefix 0
-- add a nominal formula at a different prefix for each nominal of the input formula

addFirstFormulas :: CmdLineParams -> Branch -> Formula -> LanguageInfo -> BranchInfo
addFirstFormulas clp br_ f fLang
 = addFormulas clp br ( pf : ( map (\(p,n) ->  PrFormula p bps_empty (nom n)) $ zip [1..] ns)) []
    where ns = languageNoms fLang
          nbNs = length ns
          br = br_{lastPref = (lastPref br_) + nbNs}
          pf = firstPrefixedFormula f

