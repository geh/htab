{-# OPTIONS_GHC -fno-warn-missing-fields #-}
module HTab.CommandLine (
    Params(..), UnitProp(..),
    defaultParams, configureStats, checkParams
) where

import System.Console.CmdArgs
import Data.List ( sort )
import Data.Maybe ( isNothing )
import HTab.Statistics( StatisticsState, setPrintOutInterval )

data Params = Params {
           filename        :: Maybe FilePath,
           stdin           :: Bool,
           genModel        :: Maybe FilePath,
           dotModel        :: Bool,
           timeout         :: Int,
           stats           :: Int,
           strategy        :: String,
           semBranch       :: Bool,
           backjumping     :: Bool,
           lazyBranching   :: Bool,
           unitProp        :: UnitProp,
           noLoopCheck     :: Bool,
           showFormula     :: Bool,
           allTransitive   :: Bool,
           allReflexive    :: Bool,
           allSymmetric    :: Bool,
           allFunctional   :: Bool,
           allInjective    :: Bool
         } deriving (Show, Data, Typeable)

data UnitProp = Eager | UPYes | UPNo deriving (Data, Typeable, Eq, Show)

defaultParams :: Annotate Ann
defaultParams
 = record Params{}
     [ filename       := Nothing += name "f" += typFile += help "input file",
       stdin          := False   += help "use standard input instead of file",
       genModel       := Nothing += name "m" += typFile += help "output model file",
       dotModel       := False   += help "output model in dot format (otherwise: hylolib format)",
       timeout        := 0       += name "t" += help "timeout (in seconds, default=none)",
       stats          := 0       += help "display statistics every n steps (default=none)",
       strategy       := strategyVal += help "specify rule order",
       semBranch      := True    += help "enable semantic branching (default)",
       backjumping    := True    += help "enable backjumping (default)",
       lazyBranching  := True    += help "enable lazy branching (default)" ,
       unitProp `enum_` [atom Eager += explicit += name "eager"        += help "unit propagation: eager (default)",
                         atom UPYes += explicit += name "unit-prop"    += help "unit propagation: enabled",
                         atom UPNo  += explicit += name "no-unit-prop" += help "unit propagation: disabled"] ,
       noLoopCheck    := False   += help "disable all loop check",
       showFormula    := False   += help "display formula",
       allTransitive  := False   += help "make all relations transitive",
       allReflexive   := False   += help "make all relations reflexive",
       allSymmetric   := False   += help "make all relations symmetric",
       allFunctional  := False   += help "make all relations functional",
       allInjective   := False   += help "make all relations injective"
      ] += verbosity

strategyVal :: String
strategyVal = "n@E<Db|*r"

checkParams :: Params -> IO Bool
checkParams p
 | strategy p `notPermutationOf` strategyVal =
    do putStrLn
        $ unlines ["ERROR",
                   "strategy should contain all of the following characters: ",
                   "  n = nominals               @ = satisfaction operator",
                   "  E = existential modality   < = diamond",
                   "  D = difference modality    b = down-arrow binder",
                   "  | = or                     * = transitive closure diamond",
                   "  r = role inclusion",
                   "",
                   "The default is `" ++ strategyVal ++ "'",
                   "The rules conjunction, box, universal modality and converse difference",
                   "modality are immediate, thus do not belong to the strategy."]
       return False
 | not (stdin p) && isNothing (filename p) =
    do putStrLn $ unlines ["ERROR: No input specified.","Run with --help for usage options"]
       return False
 | otherwise = return True
  where notPermutationOf l1 l2 = sort l1 /= sort l2

configureStats :: Params -> StatisticsState ()
configureStats p = setPrintOutInterval $ stats p
