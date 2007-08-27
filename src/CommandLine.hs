----------------------------------------------------
--                                                --
-- CommandLine.hs:                                --
-- Functions that handle command line processing  --
-- and presentation
--                                                --
----------------------------------------------------

{-
Copyright (C) htab 2007
Guillaume Hoffmann - guillaumh@gmail.com
Copyright (C) HyLoRes 2002-2006
Carlos Areces      - areces@loria.fr      - http://www.loria.fr/~areces
Daniel Gorin       - dgorin@dc.uba.ar
Juan Heguiabehere  - juanh@inf.unibz.it - http://www.inf.unibz.it/~juanh/

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307,
USA.
-}

module CommandLine (
    CmdLineParams(..),

    showHelp, parseParams, getConf, initialParams,

    configureMetrics
) where

-- import Char(isDigit)

import Cparser(cParser)
import Clexer(cLexer)
import Statistics(Metric,closedBranches,StatisticsState,
                  addMetric, addInspectionMetric, setPrintOutInterval,
                  ruleApplicationCount)
import Char(isDigit)
import Base(intToBool)

data CmdLineParams = CLP {
           paramsOk      :: Bool,
           filename      :: String,
           logState      :: Bool,
           maxtimeout    :: Integer,
           statsStr      :: String,
           semBranch     :: Bool,
           fullClash     :: Bool,
           latexOutput   :: Bool,
           latexName   :: String
         } deriving (Show)

initialParams :: CmdLineParams
initialParams = CLP {paramsOk = False,
                     filename = "no file name",
                     logState = False,
                     maxtimeout = 0,
                     statsStr = ":0:c",
                     semBranch = True,
                     fullClash = True,
                     latexOutput = False,
                     latexName = "htab_out.tex"}

initialParamsStr :: String
initialParamsStr = concat ["% This is the default configuration file for htab\n",
                           "% Possible valriables to set are:\n",
                           "% Filename = [file of the formula to resolve]\n",
                           "% Timeout = [in seconds, 0 = no timeout]\n",
                           "% Showstate = [Show internal state during calculus, True | False]\n",
                           "% statistics = [statistics to print]\n",
                           "% Semanticbranching = [Use semantic branching instead of disjunction rule, True | False]\n",
                           "% Fullclash = [Detect full clashes instead of working with negative normal form]\n",
                           "% LatexOutput = [Do a LaTeX output of calculus]\n",
                           "% LatexName = [name for LaTeX output file]\n",
                           "\n",
                           "Timeout = ", show $ maxtimeout initialParams, " \n",
                           "Showstate = ", show $ logState initialParams, "\n",
                           "Statistics = ", statsStr initialParams, "\n",
                           "Semanticbranching = ", show $ semBranch initialParams,"\n",
                           "Fullclash = ", show $ fullClash initialParams,"\n",
                           "LatexOutput = ", show $ latexOutput initialParams,"\n",
                           "LatexName = ", show $ latexName initialParams,"\n"]


{- parseParams: Given

   - a string containing the command line

  parses the command line parameters and returns a CmdLineParams structure
 -}

parseParams :: CmdLineParams -> [String] -> CmdLineParams
parseParams clp  []          = clp
parseParams clp ("-t":[])    = clp{paramsOk = False}
parseParams clp ("-t":t:xs)  = parseParams clp{maxtimeout = (read t)} xs
parseParams clp ("-s":xs)    = parseParams clp{logState = True} xs
parseParams clp ("-l":xs)    = parseParams clp{latexOutput = True} xs
parseParams clp ("-lo":[])   = clp{paramsOk = False}
parseParams clp ("-lo":s:xs) = parseParams clp{latexName= s} xs
parseParams clp ("-st":[])   = clp{paramsOk = False}
parseParams clp ("-st":s:xs) = if (validStats s)
                                   then parseParams clp{statsStr=s} xs
                                   else clp{paramsOk = False}
parseParams clp ("-sb":b:xs)   = parseParams clp{semBranch = (intToBool $ read b)} xs
parseParams clp ("-sb":[])    = clp{paramsOk = False}
parseParams clp ("-fc":b:xs)   = parseParams clp{fullClash = (intToBool $ read b)} xs
parseParams clp ("-fc":[])    = clp{paramsOk = False}
parseParams clp ("-f":[])    = clp{paramsOk = False}
parseParams clp ("-f":f:xs)  = parseParams clp{filename = f, paramsOk = True} xs
parseParams clp  _           = clp{paramsOk = False}


{- defineParams: Rewrites the configuration in Params using L, where
- a Params structure p (previous parameters)
- a list L of pairs (Variable, Value) -}

defineParams :: CmdLineParams -> [(String,String)] -> CmdLineParams
defineParams p [] = p
defineParams p ((f,v):s) =
  case f of "file"       ->  defineParams p{filename      = v} s
            "timeout"    ->  defineParams p{maxtimeout       = read v} s
            "ss"         ->  defineParams p{logState      = read v} s
            "statistics" ->  defineParams p{statsStr = v} s
            "sembranch"  ->  defineParams p{semBranch = read v} s
            "fullclash"  ->  defineParams p{fullClash = read v} s
            "latexoutput"->  defineParams p{latexOutput = read v} s
            "latexname"  ->  defineParams p{latexName = v} s
            unknown      -> error ("Can't Happen!: Unknown configuration parameter " ++ show unknown ++ " \n")


{- getConf: reads file .htabrc for configuration if it exists,
otherwise it creates the file with default values and warns
the user -}

getConf :: CmdLineParams -> IO CmdLineParams
getConf p =
  catch getConf' (\_ -> createConf)
      where getConf' = do fconf <- readFile ".htabrc"
                          putStr "Reading parameters from .htabrc\n"
                          return (defineParams p (cParser (cLexer fconf)))
            createConf = do writeFile ".htabrc" initialParamsStr
                            putStr "File .htabrc does not exists.\n"
                            putStr "Writing default configuration file.\n"
                            return p



{- showHelp: print a short help for the program -}

showHelp :: IO ()

showHelp = putStrLn ("htab 0.01\n" ++
     "G. Hoffmann (c) 2007.\n" ++
     "C. Areces, D.Gorin and J. Heguiabehere. (c) 2002-2005.\n\n" ++
     "Usage: htab -f file_name [-t <t>|-st <s>|-r|-s|-l|-lo file_name]\n\n" ++
     "-t secs   : Timeout in seconds.\n" ++
     "-st string: Configure statistics\n" ++
     "-s        : Prints the internal state of the tableaux.\n" ++
     "-sb 0     : Don't use semantic branching.\n" ++
     "-sb 1     : Use semantic branching.\n" ++
     "-fc 0     : Don't use full clashes.\n" ++
     "-fc 1     : Use full clashes.\n" ++
     "-l        : Enable LaTeX output.\n" ++
     "-lo file  : Specify LaTeX output file (default: htab_out.tex).\n\n" ++
     "This program is distributed in the hope that it will be useful,\n" ++
     "but WITHOUT ANY WARRANTY; without even the implied warranty of\n" ++
     "MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n" ++
     "GNU General Public License for more details.\n")




metrics :: [(Char,Metric)]
metrics = [('c',closedBranches),
           ('r',ruleApplicationCount)]

parseStats :: String -> Maybe (String, Maybe (Int, String))
parseStats s
    | allMetricsExist fmIds &&
      (null opIms ||
       if (null inter)
           then (null imIds)
           else (all isDigit inter &&
                 allMetricsExist imIds')) = Just (fmIds,inspectionStats)
    -- | otherwise                           = Nothing
    | otherwise                          = error (show (fmIds, opIms))
    where (fmIds,opIms)   = break (== ':') s
          (inter,imIds)   = break (== ':') (tail opIms)
          imIds'          = tail imIds
          allMetricsExist = (all (flip elem validMetrics))
          validMetrics    = (fst . unzip) metrics
          inspectionStats = if ( null inter )
                                then Nothing
                                else Just (read inter, imIds)


{- validStats: says if a statatistics-configuration-string is valid.
   The string is a sequence of chars that represent metrics, optionally
   followed by a colon, a number, another colon, and the sequence of
   inspection metrics -}
validStats :: String -> Bool
validStats = (Nothing /=) . parseStats

{- statistics: Given
    - a CmdLineParams clp with a valid statistics string
  configures the proper metrics inside the StatisticsState -}
configureMetrics :: CmdLineParams -> StatisticsState ()
configureMetrics clp = do
                         let Just (fmIds,ims) = parseStats (statsStr clp)
                         let fms = filterMetrics fmIds
                         mapM_ addMetric fms
                         case ims of
                             Nothing          -> return ()
                             Just (i, ifmIds) -> do
                                 let ifms = filterMetrics ifmIds
                                 mapM_ addInspectionMetric ifms
                                 setPrintOutInterval i

filterMetrics :: String -> [Metric]
filterMetrics s = map snd (filter ((flip elem s) . fst) metrics)
