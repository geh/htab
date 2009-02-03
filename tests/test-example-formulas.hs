module Main ( main ) where

import Data.List ( tails )
import qualified Data.Set as Set

import Control.Applicative ( (<$>) )
import HyLo.Util           ( sequenceUntil )

import System.Exit        ( exitFailure          )
import System.FilePath    ( (</>)                )
import System.Directory   ( getDirectoryContents )
import System.Environment ( getArgs              )

import HyLo.Model
import HyLo.Model.Herbrand
import HyLo.InputFile

import HTab.CommandLine
import HTab.Main

main :: IO ()
main =
  do (sat_dir, unsat_dir) <- parseArgs
     --
     sat_tests   <- map (runExpecting Sat)   <$> frmFiles sat_dir
     unsat_tests <- map (runExpecting Unsat) <$> frmFiles unsat_dir
     --
     success <- and <$> sequenceUntil not (sat_tests ++ unsat_tests)
     if success
       then putStrLn "SUCCESS"
       else putStrLn "FAILURE" >> exitFailure

data Expected = Sat | Unsat deriving (Eq, Show)

parseArgs :: IO (FilePath, FilePath)
parseArgs = go =<< getArgs
    where go [sd, ud] = return (sd, ud)
          go _        = fail "Required args: <sat dir> <unsat dir>"

frmFiles :: FilePath -> IO [FilePath]
frmFiles dir = map (dir </>) . filter (endsWith ".frm") <$>
                   getDirectoryContents dir

endsWith :: String -> String -> Bool
endsWith t s = t `elem` (tails s)

runHTab :: FilePath -> IO SatFlagAndStats
runHTab f = runWithParams clp
    where clp = defaultParams{filename   = Just f,
                              maxtimeout = 20,
                              quietMode  = True}

runExpecting :: Expected -> FilePath -> IO Bool
runExpecting exp_result file =
    do putStr (file ++ "......... ")
       r <- runHTab file
       case (r, exp_result) of
         (UNSAT _, Unsat) -> putStrLn "OK!" >> return True
         (UNSAT _, Sat)   -> putStrLn "FAILED! (unsat)" >> return False
         (SAT m _, Sat)   -> do b <- isASatisfyingModel (inducedModel m)
                                if b
                                  then do putStrLn "OK!"
                                          return True
                                  else do putStrLn "MODELCHECK FAILED"
                                          return False
         (SAT _ _, Unsat) -> putStrLn "FAILED! (sat)" >> return False
         (TIMEOUT _, _)     -> putStrLn "FAILED! (timeout)" >> return False
    --

    where isASatisfyingModel m =
            do fs <- parse <$> readFile file
               --
               let ws = Set.toList (worlds m)
               let g  = newVal (head ws)
               --
               return $ any (\w -> and [(m,g,w) |= f | f <- fs]) ws
