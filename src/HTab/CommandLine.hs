----------------------------------------------------
--                                                --
-- CommandLine.hs:                                --
-- Functions that handle command line processing  --
-- and presentation
--                                                --
----------------------------------------------------

module HTab.CommandLine (
    CmdLineParams(..), UnitProp(..),
    defaultParams, configureStats, checkParams
) where

import System.Console.CmdArgs

import HTab.Base( permutationOf )
import HTab.Statistics( StatisticsState, setPrintOutInterval )

data CmdLineParams = CLP {
           filename        :: Maybe FilePath,
           genModel        :: Maybe FilePath,
           timeout         :: Int,
           stats           :: Int,
           strategy        :: String,
           fairStrategy    :: Bool,
           semBranch       :: Bool,
           backjumping     :: Bool,
           lazyBranching   :: Bool,
           unitProp        :: UnitProp,
           unrestrictedBlocking :: Bool,
           noLoopCheck     :: Bool,
           showFormula     :: Bool,
           allTransitive   :: Bool,
           allReflexive    :: Bool,
           allSymmetric    :: Bool,
           allFunctional   :: Bool,
           allInjective    :: Bool
         } deriving (Show, Data, Typeable)

data UnitProp = Eager | UPYes | UPNo deriving (Data, Typeable, Eq, Show)

defaultParams :: CmdLineParams
defaultParams
 = CLP{
       filename        = Nothing &= name "f" &= typFile &= help "input file",
       genModel        = Nothing &= name "m" &= typFile &= help "output model file",
       timeout         = 0       &= name "t" &= help "timeout (in seconds, default=none)",
       stats           = 0       &= help "display statistics every n steps (default=none)",
       strategy        = strategyVal &= help "specify rule order",
       fairStrategy    = False   &= help "enable fair strategy",
       semBranch       = True    &= help "enable semantic branching (default)",
       backjumping     = True    &= help "enable backjumping (default)",
       lazyBranching   = True    &= help "enable lazy branching (default)" ,
       unitProp        = enum [Eager &= explicit &= name "eager"        &= help "unit propagation: eager (default)",
                               UPYes &= explicit &= name "unit-prop"    &= help "unit propagation: enabled",
                               UPNo  &= explicit &= name "no-unit-prop" &= help "unit propagation: disabled"] ,
       unrestrictedBlocking = False &= help "enable unrestricted blocking",
       noLoopCheck     = False   &= help "disable all loop check",
       showFormula     = False   &= help "display formula",
       allTransitive   = False   &= help "make all relations transitive",
       allReflexive    = False   &= help "make all relations reflexive",
       allSymmetric    = False   &= help "make all relations symmetric",
       allFunctional   = False   &= help "make all relations functional",
       allInjective    = False   &= help "make all relations injective"
      } &= verbosity

strategyVal :: String
strategyVal = "n@E<Db|*ru"

checkParams :: CmdLineParams -> IO Bool
checkParams clp
 = if (strategy clp) `permutationOf` strategyVal
    then return True
    else do putStrLn
             $ unlines ["ERROR",
                        "strategy should contain all of the following characters: ",
                        "  n = nominals               @ = satisfaction operator",
                        "  E = existential modality   < = diamond",
                        "  D = difference modality    b = down-arrow binder",
                        "  | = or                     * = transitive closure diamond",
                        "  r = role inclusion         u = unrestricted blocking",
                        "",
                        "The default is `" ++ strategyVal ++ "'",
                        "The rules conjunction, box, universal modality and converse difference",
                        "modality are immediate, thus do not belong to the strategy."]
            return False

configureStats :: CmdLineParams -> StatisticsState ()
configureStats clp = setPrintOutInterval $ stats clp
