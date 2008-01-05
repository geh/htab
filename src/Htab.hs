module Main (main)

where

import qualified HyLo.InputFile.Lexer as L
import qualified HyLoParse as P

import CommandLine( filename, getCmdLineParams, usage,
                    maxtimeout, showHelp, CmdLineParams, logState, genModel,
                    configureMetrics,fullClash,quietMode )
import Branch( Branch, BranchInfo(..),initialBranchStateFor,BranchMonad, BranchData(..),
               emptyBranch, lastPr )
import Timeout( timeout )
import Statistics( Statistics, initialStatisticsStateFor, printOutAllMetrics' )
import Base( vPutStrLn )
import Tableau( liftStats, tableau, OpenFlag(..) )
import Formula( firstPrefixedFormula,nnf,formulaLanguageInfo, bps_empty,
                PrFormula(..), LanguageInfo(..), NomSymbol, Formula(..), Atom(..))
import LatexOutput
import ModelGen ( HerbrandModel, inducedModel )

import Control.Applicative ( (<$>) )
import Control.Monad       ( unless )
import Control.Monad.State( runStateT )

import System.IO           ( hPrint, stderr, hSetBuffering, stdin, BufferMode(LineBuffering)) 
import System.Exit         ( exitWith, ExitCode(ExitFailure) )
import System.Environment( getProgName )
import System.CPUTime( getCPUTime )

import Data.Version        ( showVersion )
import Paths_HTab ( version )

import Prelude hiding ( catch )
import Control.Exception   ( catch )


import Rules(BranchModification(..), applyMods)

data SatFlagAndStats = SAT HerbrandModel Statistics | UNSAT Statistics | TIMEOUT

main :: IO ()
main = do r <- runCmdLineVersion
                `catch` \e -> do
                    hPrint stderr (show e)
                    exit r_RUNTIME_ERROR
          --
          case r of
            Nothing        -> exit r_DID_NOT_RUN
            Just (SAT _ _) -> exit r_SAT
            Just (UNSAT _) -> exit r_UNSAT
            Just TIMEOUT   -> exit r_TIMEOUT
    --
    where r_SAT           = 1
          r_UNSAT         = 2
          r_TIMEOUT       = 3
          r_DID_NOT_RUN   = 10
          r_RUNTIME_ERROR = 13

exit :: Int -> IO a
exit = exitWith . ExitFailure


runCmdLineVersion :: IO (Maybe SatFlagAndStats)
runCmdLineVersion =
    do p_clp <- getCmdLineParams
       case p_clp of
         Left  err -> do putStrLn header
                         putStrLn err
                         progName <- getProgName
                         putStrLn $ "Try `" ++ progName ++ " --help' " ++
                                     "for more information"
                         return Nothing
         --
         Right clp -> if showHelp clp
                        then do putStrLn header
                                progName <- getProgName
                                putStrLn $ usage (progName ++ " [OPTIONS]")
                                putStrLn gpl_tag
                                return Nothing
                        --
                        else Just <$> runWithParams clp

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

     f <- P.parse . L.lexify <$> maybe fromStdIn readFile (filename clp)
     --
     let fLang = formulaLanguageInfo f
     latexInit clp
     --
     let f2 = if (fullClash clp) then f else nnf f
     --
     f `seq` myPutStrLn ("\nInput:\n{ " ++ (show f2) ++" }\nEnd of input\n\n");
     --
     let branchInfo = addFirstFormulas clp (emptyBranch fLang) f2 (languageNoms fLang)
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
                         putStrLn $ "Model saved as " ++ f

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

header :: String
header = unlines ["HTab " ++ showVersion version,
                  "G. Hoffmann, C. Areces, D.Gorin and J. Heguiabehere. (c) 2002-2007."]

gpl_tag :: String
gpl_tag = unlines [
    "This program is distributed in the hope that it will be useful,",
    "but WITHOUT ANY WARRANTY; without even the implied warranty of",
    "MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the",
    "GNU General Public License for more details."]


-- preparation of the branch at the beginning of the calculus:
-- add the input formula at prefix 0
-- add a nominal formula at a different prefix for each nominal of the input formula

addFirstFormulas :: CmdLineParams -> Branch -> Formula -> [NomSymbol] -> BranchInfo
addFirstFormulas clp br_ f ns
 = applyMods clp br
     ( BM_AddFormulas [pf]
       : (map (\(p,n) -> BM_AddFormulas [PrFormula p bps_empty (PosLit (N n))]) $ zip [1..] ns)
     )
    where nbNs = length ns
          br = br_{lastPr = (lastPr br_) + nbNs}
          pf = firstPrefixedFormula f
