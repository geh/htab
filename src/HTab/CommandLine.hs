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
           filename        :: [FilePath],
           genModel        :: [FilePath],
           timeout         :: Int,
           stats           :: Int,
           strategy        :: String,
           fairStrategy    :: Bool,
-- optimizations enabled by default
           noSemBranch     :: Bool,
           noBackjumping   :: Bool,
           noLazyBranching :: Bool,
--
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

defaultCLP :: CmdLineParams
defaultCLP
 = CLP{
       filename        = [] &= flag "f" & typFile &  text "input file",
       genModel        = [] &= flag "m" & typFile & text "output model file",
       timeout         = 0 &= flag "t" & text "timeout (in seconds, default=none)",
       stats           = 0 &= text "display statistics every n steps (default=none)",
       strategy        = strategyVal &= text "specify rule order",
       fairStrategy    = False &= text "enable fair strategy",
       noSemBranch     = False &= text "disable semantic branching (default enabled)",
       noBackjumping   = False &= text "disable backjumping (default enabled)",
       noLazyBranching = False &= text "disable lazy branching (default enabled)" ,
       unitProp        = enum Eager [Eager &= explicit & flag "eager"        & text "unit propagation: eager (default)",
                                     UPYes &= explicit & flag "unit-prop"    & text "unit propagation: enabled",
                                     UPNo  &= explicit & flag "no-unit-prop" & text "unit propagation: disabled"] ,
       unrestrictedBlocking = False &= text "enable unrestricted blocking",
       noLoopCheck     = False &=  text "disable all loop check",
       showFormula     = False &= text "display formula",
       allTransitive   = False &= text "make all relations transitive",
       allReflexive    = False &= text "make all relations reflexive",
       allSymmetric    = False &= text "make all relations symmetric",
       allFunctional   = False &= text "make all relations functional",
       allInjective    = False &= text "make all relations injective"
      }

defaultParams :: Mode CmdLineParams
defaultParams = mode $ defaultCLP &= helpSuffix gpl_tag

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

gpl_tag :: [String]
gpl_tag = [
    "This program is distributed in the hope that it will be useful,",
    "but WITHOUT ANY WARRANTY; without even the implied warranty of",
    "MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the",
    "GNU General Public License for more details."]

configureStats :: CmdLineParams -> StatisticsState ()
configureStats clp = setPrintOutInterval $ stats clp
