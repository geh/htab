module Main (main)

where

import System
--import Control.Exception
--import Control.Concurrent
--import Control.Monad.State
--import Data.Dynamic(Typeable, typeOf, TyCon, mkTyCon, mkTyConApp, toDyn)
--import Data.Unique

import HyLoLexer(hyloLexer)
import HyLoParse
import CommandLine

--import Base
import Structures
import Rules

data SatFlag = SAT | UNSAT
 deriving Show

main :: IO ()
main =
    do {
        confhyloresrc <- getConf initialParams;
        args <- getArgs;
        let clp = parseParams confhyloresrc args in

        if ( paramsOk clp )
        then do {
                 fstr <- readFile (filename clp);
                 case (parse . hyloLexer $ fstr)
                 of {
                     structInfo ->
                        do {
                                isSat <- algoLoop structInfo clp;
                                case isSat of
                                 SAT       -> putStrLn "SAT"
                                 UNSAT     -> putStrLn "UNSAT"
                         };
                    }
                }
        else showHelp;
       }


algoLoop :: StructInfo -> CmdLineParams -> IO (SatFlag)
algoLoop si clp = do vPutStrLn ">> Starting rules application"
                                       ((logState clp)||(logRules clp));
                     algoLoopCount si 0 clp

algoLoopCount :: StructInfo -> Int -> CmdLineParams -> IO (SatFlag)
algoLoopCount si counter clp =
      do let showState = (logState clp)
         let showRules = (logRules clp)
         vPutStrLn ("\n>> Iteration #" ++ (show counter)) (showState || showRules)
         case si of
          StructOK sos -> do vPutStrLn (show sos) showState
                             let listOfRules = applicableRules sos
                             let r = chooseRule listOfRules
                             case r of
                              Just rule -> do vPutStrLn ("\n>> Rule : " ++ (show rule)) showRules
                                              let possibleStructures = applyRule rule sos
                                              chooseStruct possibleStructures counter clp
                              Nothing   -> do vPutStrLn "\n>> Saturated open branch" (showState || showRules)
                                              return SAT
          StructClash sos pf -> do vPutStrLn (show sos) showState
                                   vPutStrLn ("\nClasher : " ++ (show pf)) showState
                                   vPutStrLn ("\n>> Closed branch") showState
                                   return UNSAT


-- dumb rule-choosing strategy
chooseRule :: [RuleL] -> Maybe RuleL
chooseRule (hd:_)  = Just hd
chooseRule [] = Nothing

-- dumb depth-first strategy
chooseStruct :: [StructInfo] -> Int -> CmdLineParams -> IO (SatFlag)
chooseStruct (hd:tl) counter clp
    = do isSat <- algoLoopCount hd (counter+1) clp
         case (isSat) of
          SAT       -> do return SAT               -- stop there and return SAT
          UNSAT     -> chooseStruct tl counter clp -- examine next
chooseStruct [] counter clp
  = do vPutStrLn ("\n>> Stop width at level " ++ show counter) ((logState clp)||(logRules clp))
       return UNSAT


vPutStrLn :: String -> Bool -> IO ()
vPutStrLn s b = if b then putStrLn s
                     else return ()