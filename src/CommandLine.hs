----------------------------------------------------
--                                                --
-- CommandLine.hs:                                --
-- Functions that handle command line processing  --
-- and presentation
--                                                --
----------------------------------------------------

module CommandLine (
    CmdLineParams(..), getCmdLineParams, defaultParams,
    usage, configureMetrics
) where

import Statistics(Metric,closedBranches,StatisticsState,
                  addMetric, addInspectionMetric, setPrintOutInterval,
                  ruleApplicationCount)
import Char(isDigit)
import Base(intToBool)
import System.FilePath(FilePath)
import System.Console.GetOpt ( OptDescr(..), ArgDescr(..), ArgOrder(..),
                               getOpt, usageInfo )

import System.Directory      ( getHomeDirectory, doesFileExist )
import System.FilePath       ( (</>) )
import System.Environment    ( getArgs )
import Data.Maybe ( isJust )
import Control.Monad.Error (MonadError(..))
import Control.Applicative ( (<$>) )

data CmdLineParams = CLP {
           showHelp      :: Bool,
           filename      :: Maybe FilePath,
           logState      :: Bool,
           maxtimeout    :: Integer,
           statsStr      :: String,
           semBranch     :: Bool,
           fullClash     :: Bool,
           latexOutput   :: Maybe FilePath,
           genModel      :: Maybe FilePath,
           quietMode     :: Bool
         } deriving (Show)

type CLPModifier   = CmdLineParams -> Either ParsingErrMsg CmdLineParams
type ParsingErrMsg = String

parseCmds :: [String] -> CmdLineParams -> Either ParsingErrMsg CmdLineParams
parseCmds argv clp = case getOpt RequireOrder options argv of
                       (clpMods, [],  []) -> thread clpMods clp
                       (      _,unk,  []) -> fail $ "Unknown option: " ++
                                                   unwords unk
                       (     _,   _,errs) -> fail $ unlines errs


thread :: Monad m => [a -> m a] -> a -> m a
thread = foldr (\f g -> \a -> f a >>= g) return

options :: [OptDescr CLPModifier]
options =
  [Option ['h','?']
          ["help"]
          (NoArg $ \c -> return c{showHelp = True})
          "display this help and exit",
   Option ['f']
          ["input-file"]
          (ReqArg ((not . null) ?-> \s c -> return c{filename = Just s}) "FILE")
          "obtain input formulas from FILE instead of STDIN",
   Option ['q']
          ["quiet", "silent"]
          (NoArg $ \c -> return c{quietMode = True})
          "suppress all normal output",
   Option ['t']
          ["timeout"]
          (ReqArg setTimeout "T")
          "run for at most T seconds",
   Option ['m']
          ["save-model"]
          (ReqArg ((not . null) ?-> \s c -> return c{genModel = Just s}) "FILE")
          (unlines [
          "if the formulas are satisfiable, output a model",
          "to FILE"]),
   Option ['s']
          ["log-state"]
          (NoArg $ \c -> return c{logState = True})
          "log the internal state (clauses, inUse and new)",
   Option ['l']
          ["latex-output"]
          (ReqArg ((not .null) ?-> \s c -> return c{latexOutput = Just s}) "FILE")
          "log rule applications",
   Option ['b']
          ["semantic-branching"]
          (ReqArg setSemanticBranching "[0|1]")
          "disable/enable semantic branching optimisation",
   Option ['c']
          ["full-clash"]
          (ReqArg setFullClash "[0|1]")
          "disable/enable full clash optimisation",
   Option ['S']
          ["statistics"]
          (ReqArg setStats "PAT")
          (unlines [
           "PAT configures the collecting of statistics.",
           "A valid PAT is of the form:",
           "",
           "   METRICS:INTERVAL:METRICS",
           "",
           "The `:INTERVAL:METRICS` argument is optional",
           "and declares metrics that will be printed at",
           "regular intervals (e.g. `:100:r' shows the",
           "number of rules applied so far, every 100",
           "iterations of the algorithm).",
           "",
           "METRICS is made of one or more of the following",
           "values:",
           "  c = number of closed branches",
           "  r = number of rules applied",
           "",
           "The default is `" ++ statsStr defaultParams ++ "'",
           ""])]

(?->) :: (String -> Bool) -> (String -> CLPModifier) -> String -> CLPModifier
p ?-> m = \s -> if (not $ null s) && p s
                  then m s
                  else \_ -> throwError ("Invalid argument: '" ++ s ++ "'")

setTimeout :: String -> CLPModifier
setTimeout = (all isDigit) ?-> \s c -> return c{maxtimeout = read s}


setSemanticBranching :: String -> CLPModifier
setSemanticBranching = is0or1 ?-> \s c -> return c{semBranch = intToBool $ read s}

setFullClash :: String -> CLPModifier
setFullClash = is0or1 ?->  \s c -> return c{fullClash = intToBool $ read s}

is0or1 :: String -> Bool
is0or1 s = (s == "1") || (s == "0")

setStats :: String -> CLPModifier
setStats = (isJust . parseStats) ?->
             \s c -> return c{statsStr = s}

defaultParams :: CmdLineParams
defaultParams = CLP {showHelp = False,
                     filename = Nothing,
                     logState = False,
                     latexOutput = Nothing,
                     maxtimeout = 0,
                     statsStr = ":0:c",
                     semBranch = True,
                     fullClash = False,
                     genModel = Nothing,
                     quietMode = False}

getCmdLineParams :: IO (Either ParsingErrMsg CmdLineParams)
getCmdLineParams =
    do let clp_0 = defaultParams
       m_rcfile <- findRc
       parse_clp_1 <- case m_rcfile of
                        Nothing -> return $ return clp_0
                        Just f  -> do rc_args <- words <$> readFile f
                                      return $  parseCmds rc_args clp_0
                                              `catchError`
                                                (\e -> fail $ f ++ ":\n" ++ e)
       --
       cmdline_args   <- getArgs
       --
       return $ do clp_1 <- parse_clp_1
                   parseCmds cmdline_args clp_1

{-
{- getConf: reads file .htabrc for configuration if it exists,
otherwise it creates the file with default values and warns
the user -}

getConf :: CmdLineParams -> FilePath -> IO CmdLineParams
getConf p configDir =
  catch getConf' (\_ -> createConf)
      where fullName = configDir ++ </> ++ ".htabrc"
            getConf' = do fconf <- readFile fullName
                          putStr $ "Reading parameters from " ++ fullName ++ "\n"
                          return (defineParams p (cParser (cLexer fconf)))
            createConf = do writeFile fullName initialParamsStr
                            putStr $ "File "  ++ fullName ++ " does not exist.\n"
                            putStr "Writing default configuration file.\n"
                            return p

-}

rcfile :: FilePath
rcfile = ".htabrc"


findRc :: IO (Maybe FilePath)
findRc =
    do existsInCurrent <- doesFileExist rcfile
       if existsInCurrent
         then return (Just rcfile)
         else do
             home <- getHomeDirectory
             let inHome = home </> rcfile
             --
             existsInHome <- doesFileExist inHome
             if existsInHome then return (Just inHome) else return Nothing



usage :: String -> String
usage header = unlines [
    usageInfo header options,
    "",
    "If a file called `" ++  "." </> rcfile ++ "' or `" ++ "~" </> rcfile
    ++ "' exists, it will be scanned for arguments first"
    ]

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
