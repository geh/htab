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
import HyLo.Signature.String ( NomSymbol(..), PropSymbol(..), RelSymbol(..) )


import HTab.CommandLine
import HTab.Main

main :: IO ()
main =
  do (sat_dir, sat_no_mod_dir, unsat_dir) <- parseArgs
     --
     sat_tests        <- map (runExpecting Sat)      <$> frmFiles sat_dir
     sat_no_mod_tests <- map (runExpecting SatNoMod) <$> frmFiles sat_no_mod_dir
     unsat_tests      <- map (runExpecting Unsat)    <$> frmFiles unsat_dir
     --
     success <- and <$> sequenceUntil not (sat_tests ++ sat_no_mod_tests ++ unsat_tests)
     if success
       then putStrLn "SUCCESS"
       else putStrLn "FAILURE" >> exitFailure

data Expected = Sat | SatNoMod | Unsat deriving (Eq, Show)

parseArgs :: IO (FilePath, FilePath, FilePath)
parseArgs = go =<< getArgs
    where go [sd, snmd, ud] = return (sd, snmd, ud)
          go _              = fail "Required args: <sat dir> <sat no model dir> <unsat dir>"

frmFiles :: FilePath -> IO [FilePath]
frmFiles dir = map (dir </>) . filter (endsWith ".frm") <$>
                   getDirectoryContents dir

endsWith :: String -> String -> Bool
endsWith t s = t `elem` (tails s)

runHTab :: FilePath -> IO TaskRunFlag
runHTab f = runWithParams clp
    where clp = defaultParams{filename   = Just f,
                              maxtimeout = 20,
                              quietMode  = True,
                              genModel   = Just modelTmpFile}

modelTmpFile :: String
modelTmpFile = "model.tmp"

runExpecting :: Expected -> FilePath -> IO Bool
runExpecting exp_result file =
    do putStr (file ++ "......... ")
       r <- runHTab file
       case (r, exp_result) of
         (FAILURE, Unsat)    -> putStrLn "OK!" >> return True
         (FAILURE, _)        -> putStrLn "FAILED! (unsat)" >> return False
         (SUCCESS, SatNoMod) -> putStrLn "OK!" >> return True
         (SUCCESS, Sat)      -> do b <- isASatisfyingModel
                                   if b
                                     then do putStrLn "OK!"
                                             return True
                                     else do putStrLn "MODELCHECK FAILED"
                                             return False
         (SUCCESS, Unsat)    -> putStrLn "FAILED! (sat)" >> return False
         (TIMEOUT_ , _)      -> putStrLn "FAILED! (timeout)" >> return False
    --

    where isASatisfyingModel =
            do fs <- parse <$> readFile file
               m  <- read  <$> readFile modelTmpFile :: IO M
               --
               let ws = Set.toList (worlds m)
               --
               return $ any (\w -> and [(m,w) |= f | f <- fs]) ws

type M = Model NomSymbol NomSymbol PropSymbol RelSymbol
