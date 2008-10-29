module HTab.Main

( runWithParams, SatFlagAndStats(..) )

where
import Control.Applicative ( (<$>) )
import Control.Monad       ( unless )
import Control.Monad.State( runStateT )

import System.IO           ( hSetBuffering, stdin, BufferMode(LineBuffering)) 
import System.CPUTime( getCPUTime )


import HTab.CommandLine( filename, maxtimeout, CmdLineParams, logState, genModel,
                         configureMetrics,fullClash,quietMode, inclBlockGlobal, inclBlockChain,
                         immediateBlock )
import HTab.Branch( Branch, BranchInfo(..),initialBranchStateFor,BranchMonad, BranchData(..),
                    emptyBranch, lastPref, BlockingMode(..) )
import HTab.Timeout( timeout )
import HTab.Statistics( Statistics, initialStatisticsStateFor, printOutAllMetrics' )
import HTab.Base( vPutStrLn )
import HTab.Tableau( liftStats, tableau, OpenFlag(..) )
import HTab.Formula( firstPrefixedFormula,nnf,formulaLanguageInfo, bps_empty,
                     PrFormula(..), LanguageInfo(..), NomSymbol, Formula(..), Atom(..),
                     parse )
import HTab.LatexOutput
import HTab.ModelGen ( HerbrandModel, inducedModel )



import HTab.Rules(BranchModification(..), applyMod)

data SatFlagAndStats = SAT HerbrandModel Statistics | UNSAT Statistics | TIMEOUT


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
     latexInit clp
     --
     let f2 = if (fullClash clp) then f else nnf f
     --
     f `seq` myPutStrLn ("\nInput:\n{ " ++ (show f2) ++" }\nEnd of input\n\n");
     --
     let branchInfo = addFirstFormulas clp (emptyBranch fLang blockMode (immediateBlock clp)) f2 (languageNoms fLang)
                        where blockMode = case (inclBlockGlobal clp , inclBlockChain clp) of
                                             (False, True) -> InclusionBlockingChain
                                             ( _  ,   _  ) -> InclusionBlockingGlobal
     --
     result <- if (not ((maxtimeout clp) == 0))
                then timeout (maxtimeout clp)
                             (tableauInit branchInfo clp)
                             (return TIMEOUT)
                else (tableauInit branchInfo clp)
     --
     case result of
        SAT m stats -> do myPutStrLn "The formula is satisfiable."
                          saveGenModel clp m
                          unless (quietMode clp) $
                              printOutAllMetrics' stats
        UNSAT stats -> do myPutStrLn "The formula is unsatisfiable."
                          unless (quietMode clp) $
                              printOutAllMetrics' stats
        TIMEOUT     ->    myPutStrLn "TIMEOUT"
     --
     end <- getCPUTime
     let elapsedTime = fromInteger (end - start) / 1000000000000.0
     myPutStrLn $ "Elapsed time: " ++ show (elapsedTime :: Double)
     --
     latexEnd clp
     --
     return result

saveGenModel :: CmdLineParams -> HerbrandModel -> IO ()
saveGenModel clp m = maybe (return ()) doWrite (genModel clp)
    where doWrite f = do writeFile f (show . inducedModel $ m)
                         unless (quietMode clp) $ putStrLn $ "Model saved as " ++ f

tableauInit :: BranchInfo -> CmdLineParams -> IO (SatFlagAndStats)
tableauInit bi clp =
        do vPutStrLn ">> Starting rules application" (logState clp)
           res <- initStatsState $ initBranchState bd $ tableauStart clp
           case res of
            ((OPEN m,_),stats)   -> return $ SAT m stats
            ((CLOSED _,_),stats) -> return $ UNSAT stats
 where initStatsState  = initialStatisticsStateFor runStateT
       initBranchState = initialBranchStateFor runStateT
       bd              = BranchData
                          { branch_info = bi,
                            branch_clp  = clp,
                            branch_path = [0]}

tableauStart :: CmdLineParams -> BranchMonad OpenFlag
tableauStart clp =
 do liftStats $ configureMetrics clp
    tableau

-- preparation of the branch at the beginning of the calculus:
-- add the input formula at prefix 0
-- add a nominal formula at a different prefix for each nominal of the input formula

addFirstFormulas :: CmdLineParams -> Branch -> Formula -> [NomSymbol] -> BranchInfo
addFirstFormulas clp br_ f ns
 = applyMod clp br
     ( BM_AddFormulas ( pf : ( map (\(p,n) ->  PrFormula p bps_empty (PosLit (N n))) $ zip [1..] ns))
     )
    where nbNs = length ns
          br = br_{lastPref = (lastPref br_) + nbNs}
          pf = firstPrefixedFormula f
