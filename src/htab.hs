module Main (main)

where

import HTab.CommandLine( getCmdLineParams, usage, showHelp)

import Control.Applicative ( (<$>) )

import System.IO           ( hPrint, stderr ) 
import System.Exit         ( exitWith, ExitCode(ExitFailure) )
import System.Environment( getProgName )

import Data.Version        ( showVersion )
import Paths_HTab ( version )

import Prelude hiding ( catch )
import Control.Exception   ( catch )

import HTab.Main ( runWithParams, SatFlagAndStats(..) )

main :: IO ()
main = do r <- runCmdLineVersion
                `catch` \e -> do
                    hPrint stderr (show e)
                    exit r_RUNTIME_ERROR
          --
          case r of
            Nothing          -> exit r_DID_NOT_RUN
            Just (SAT _ _)   -> exit r_SAT
            Just (UNSAT _)   -> exit r_UNSAT
            Just (TIMEOUT _) -> exit r_TIMEOUT
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

header :: String
header = unlines ["HTab " ++ showVersion version,
                  "G. Hoffmann, C. Areces, D.Gorin and J. Heguiabehere. (c) 2002-2007."]

gpl_tag :: String
gpl_tag = unlines [
    "This program is distributed in the hope that it will be useful,",
    "but WITHOUT ANY WARRANTY; without even the implied warranty of",
    "MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the",
    "GNU General Public License for more details."]

