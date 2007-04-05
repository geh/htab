module Main (main)

where

import System.Environment
--import Control.Exception
--import Control.Concurrent
--import Control.Monad.State
--import Data.Dynamic(Typeable, typeOf, TyCon, mkTyCon, mkTyConApp, toDyn)
--import Data.Unique

import HyLoLexer(hyloLexer)
import HyLoParse
import CommandLine

import Branch
import Rules

type NbClash = Int

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
                     branchInfo ->
                        do {
                                (isSat,nbClash) <- algoLoop branchInfo clp;
                                case isSat
                                of {
                                  SAT       -> putStrLn "SAT";
                                  UNSAT     -> putStrLn "UNSAT";
                                };

                                putStrLn ("Closed branches " ++ (show nbClash));
                         };
                    }
                }
        else showHelp;
       }


algoLoop :: BranchInfo -> CmdLineParams -> IO ((SatFlag,NbClash))
algoLoop si clp = do vPutStrLn ">> Starting rules application"
                                       ((logState clp)||(logRules clp));
                     algoLoopCount si 0 0 clp

algoLoopCount :: BranchInfo -> Int -> Int -> CmdLineParams -> IO (SatFlag,NbClash)
algoLoopCount si depth nbClashed clp =
      do let showState = (logState clp)
         let showRules = (logRules clp)
         case si of
          BranchOK br -> do vPutStrLn (show br) showState
                            let listOfRules = applicableRules br
                            let r = chooseRule listOfRules
                            case r of
                             Just rule -> do vPutStrLn ("\n>> Rule : " ++ (show rule)) showRules
                                             let possibleBranches = applyRule rule br
                                             chooseBranch possibleBranches depth 0 nbClashed clp
                             Nothing   -> do vPutStrLn "\n>> Saturated open branch" (showState || showRules)
                                             return (SAT,nbClashed)
          BranchClash br pf -> do vPutStrLn (show br) showState
                                  vPutStrLn ("\nClasher : " ++ (show pf)) showState
                                  vPutStrLn ("\n>> Closed branch") (showState || showRules)
                                  return (UNSAT,nbClashed+1)


-- dumb rule-choosing strategy
chooseRule :: [Rule] -> Maybe Rule
chooseRule (hd:_)  = Just hd
chooseRule [] = Nothing

-- dumb depth-first strategy
chooseBranch :: [BranchInfo] -> Int -> Int -> Int -> CmdLineParams -> IO (SatFlag,NbClash)
chooseBranch (hd:tl) depth width nbClashed clp
    = do let showState = (logState clp)
         let showRules = (logRules clp)
         vPutStrLn ("\n>> Depth #" ++ (show depth) ++ " Width #" ++ (show width)) (showState || showRules)
         alcRes <- algoLoopCount hd (depth+1) nbClashed clp
         case (alcRes) of
          (SAT,ncl)   -> do return (SAT,ncl)                         -- stop there and return SAT
          (UNSAT,ncl) -> chooseBranch tl depth (width+1) (ncl) clp -- examine next
chooseBranch [] depth width nbClashed clp
  = do vPutStrLn ("\n>> Stop width at level " ++ show depth ++ " width " ++ show width) ((logState clp)||(logRules clp))
       return (UNSAT,nbClashed)


vPutStrLn :: String -> Bool -> IO ()
vPutStrLn s b = if b then putStrLn s
                     else return ()