module Main (main)

where

import Control.Monad ( unless )
import Control.Applicative ( (<$>) )

import System.Console.CmdArgs ( cmdArgs )

import System.IO           ( hPrint, stderr ) 
import System.Exit         ( exitWith, ExitCode(ExitFailure) )

import Data.Version        ( showVersion )
import Paths_HTab ( version )

import Prelude hiding ( catch )
import Control.Exception   ( catch, SomeException )

import HTab.Main ( runWithParams, TaskRunFlag(..) )
import HTab.CommandLine( defaultParams, checkParams )

main :: IO ()
main = do r <- runCmdLineVersion
                `catch` \(e::SomeException) -> do
                    let msg = show e
                    unless (msg == "ExitSuccess") $ hPrint stderr msg
                    exit r_RUNTIME_ERROR
          --
          case r of
            Nothing          -> exit r_DID_NOT_RUN
            Just SUCCESS     -> exit r_SAT
            Just FAILURE     -> exit r_UNSAT
            Just TIMEOUT_    -> exit r_TIMEOUT
    --
    where r_SAT           = 1
          r_UNSAT         = 2
          r_TIMEOUT       = 3
          r_DID_NOT_RUN   = 10
          r_RUNTIME_ERROR = 13

exit :: Int -> IO a
exit = exitWith . ExitFailure

runCmdLineVersion :: IO (Maybe TaskRunFlag)
runCmdLineVersion =
 do  clp  <- cmdArgs header [defaultParams]
     clpOK <- checkParams clp
     if clpOK
      then Just <$> runWithParams clp
      else return Nothing

header :: String
header = unlines ["HTab " ++ showVersion version,
                  "G. Hoffmann, C. Areces, D.Gorin and J. Heguiabehere. (c) 2002-2010.",
                  "http://code.google.com/p/intohylo/"]


