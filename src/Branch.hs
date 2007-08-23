----------------------------------------------------
--                                                --
-- Branch.hs:                                     --
-- Branches used in the calculus.                 --
--                                                --
----------------------------------------------------


module Branch
(
Branch(..), BranchMonad, incLastPr, BranchInfo(..),
addFormulas, addFormula, addAccFormula, remFormula,
addBoxRuleCheck, BranchData(..),branch_depth,
emptyBranch,initialBranchStateFor,getCLParams


) where

-- Formulas are put in different lists depending on their kind
-- conjunctions, disjunctions, diamond, boxes,
-- and accessibility formulas.
-- there is also a "seen" map to store every formula seen during
-- the calculus, if full clashing is enabled, and at least contains
-- literals even if full clashing is disabled.
-- The highest prefix is also stored.

-- Each formula is prefixed

-- There is always one way of knowing that a rule has been applied:
-- for ^ , <> and v : as soon as a formula is used, it is deleted
-- for [] : we remember if a couple (accessibility formula, box formula) has
--          been treated, by storing it in a special list in the branch


import Control.Monad.State(StateT, modify,MonadState, get)
import Data.List(delete)
import qualified Data.Map as Map

import Statistics(Statistics)
import CommandLine(CmdLineParams, fullClash)
import Formula

import qualified Data.Array.Unboxed as UArray
import SpecialMatrix(addElement,newUArray,
                     indexOfEarliest,Column,Line)

import Control.Monad.ST(runST)
import Data.Array.MArray(thaw,freeze)
import Data.Set(Set,insert,empty,elems,singleton)

import Base(flatten)

import LatexOutput
import LatexOutputHelper
import Ix(range)

import Debug.Trace(trace)

type Clasher = PrFormula
data BranchInfo = BranchOK Branch |
                  BranchClash Branch Clasher

-- Lit structure is a Map, because it's easier to detect clashed
-- by looking if there is already something at the (prefix, prop) place
-- and if what is there contradicts what we want to add

type Seen_structure   = Map.Map PrFormula Bool
type Conj_structure   = [PrFormula]
type Disj_structure   = [PrFormula]
type Dia_structure    = [PrFormula]
type Box_structure    = [PrFormula]
type Neg_structure    = [PrFormula]
type At_structure     = [PrFormula]
type NegNom_structure = [PrFormula]
type Acc_structure    = [AccFormula]             -- accessibility relations
type Box_rule_chart   = [(PrFormula,AccFormula)]

type NomToEarliestPref = Map.Map Nominal Prefix
type PrefToFormulas    = Map.Map Prefix [Formula]

type Matrix = UArray.UArray (Int,Int) Bool

data Branch = Branch { seenStr :: Seen_structure,
                       conjStr :: Conj_structure,
                       disjStr :: Disj_structure,
                        diaStr :: Dia_structure,
                        boxStr :: Box_structure,
                        negStr :: Neg_structure,
                         atStr :: At_structure,
                     negNomStr :: NegNom_structure,
                        accStr :: Acc_structure,
                       boxRlCh :: Box_rule_chart,
                        lastPr :: Prefix,
                     nomToPref :: NomToEarliestPref,
                   prefToForms :: PrefToFormulas,
                 nomPrefMatrix :: Matrix,
                 inputLanguage :: Int }

--

branch_depth :: BranchData -> Int
branch_depth b = length $ branch_path b

--
emptyBranch :: LanguageInfo -> Branch
emptyBranch l =
                Branch
                { seenStr= Map.empty::Map.Map PrFormula Bool,
                  conjStr=[],
                  disjStr=[],
                  diaStr=[],
                  boxStr=[],
                  negStr=[],
                  atStr=[],
                  accStr=[],
                  boxRlCh=[],
                  negNomStr=[],
                  lastPr=0,
                  nomToPref= Map.empty::Map.Map Nominal Prefix,
                  prefToForms= Map.empty::Map.Map Prefix [Formula],
                  nomPrefMatrix = npMatrix,
                  inputLanguage = l
                }
 where
   npMatrix = if l == 0
               then newUArray ((1,1),(0,0))     -- empty array
               else newUArray ((0,0),(500,l-1)) -- HARDCODED number of rows ...


instance Show Branch where
    show br = "Input language: " ++ show (inputLanguage br) ++
              "\nSeen formulas: "  ++ show (Map.toList $ seenStr br)   ++
              "\nConjunctions: "   ++ show (conjStr br)  ++
              "\nDisjunctions: "   ++ show (disjStr br)  ++
              "\nDiamonds: "       ++ show (diaStr br)   ++
              "\nBoxes: "          ++ show (boxStr br)   ++
              "\nNegations: "      ++ show (negStr br)   ++
              "\nAts: "            ++ show (atStr br)   ++
              "\nNeg noms: "       ++ show (negNomStr br)   ++
              "\nAccesibility: "   ++ show (accStr br)   ++
              "\nBox rule chart: " ++ show (boxRlCh br)  ++
              "\nBiggest prefix: " ++ show (lastPr br) ++
              "\nNominal to earliest prefix: "    ++ show (Map.toList $ nomToPref br) ++
              "\nPrefix to formulas: "  ++ show (Map.toList $ prefToForms br)

instance ShowLatex Branch where
 showLatex br = "Input language: " ++ (putEol $ math $ show $ inputLanguage br)   ++ 
              "\nSeen formulas: "     ++ (putEol $ math $ showLatex $ seenStr br)   ++
              "\nConjunctions: "   ++ (putEol $ math $ separate ", " $ conjStr br)  ++
              "\nDisjunctions: "   ++ (putEol $ math $ separate ", " $ disjStr br)  ++
              "\nDiamonds: "       ++ (putEol $ math $ separate ", " $ diaStr br)   ++
              "\nBoxes: "          ++ (putEol $ math $ separate ", " $ boxStr br)   ++
              "\nNegations: "      ++ (putEol $ math $ separate ", " $ negStr br)   ++
              "\nAts: "            ++ (putEol $ math $ separate ", " $ atStr br)   ++
              "\nNeg noms: "       ++ (putEol $ math $ separate ", " $ negNomStr br)   ++
              "\nAccesibility: "   ++ (putEol $ math $ separate ", " $ accStr br)   ++
              "\nBox rule chart: " ++ (putEol $ separate ", " $ boxRlCh br)  ++
              "\nBiggest prefix: " ++ (putEol $ show $ lastPr br) ++
              "\nNominal to earliest prefix: "  ++ (putEol $ showLatex $ nomToPref br)   ++
              "\nPrefix to formulas: \\\\"      ++ (putEol $ math $ showLatex $ prefToForms br) ++
              "\nPrefix-Nominal matrix : " ++ (verbatim $ showLatex $ nomPrefMatrix br)

instance ShowLatex NomToEarliestPref where
 showLatex ntep = show $ Map.toList ntep

instance ShowLatex PrefToFormulas where
 showLatex ptf = separate "\\\\" $ Map.toList ptf

instance  ShowLatex (Prefix,[Formula]) where
 showLatex (p,fs)  = (bold $ show p) ++ ":" ++ ("[" ++ (separate ", " fs) ++ "]")

instance ShowLatex Seen_structure where
 showLatex ss  = "[" ++ (separate ", " $ Map.toList ss) ++ "]"

instance ShowLatex (PrFormula,Bool) where
 showLatex (pf,b)  = if b then "" ++ "(" ++ (showLatex pf) ++ ")"
                          else "\\neg" ++ "(" ++ (showLatex pf) ++ ")"

--type Matrix = UArray.UArray (Int,Int) Bool
instance ShowLatex Matrix where
 showLatex m = foldr insertEol "" $ map (separate " " . (getLineT m)) (range (0,5))

instance ShowLatex Bool where
 showLatex b = if b then "1"
                    else "."

--

{-
   "add formula(s)" functions, that handle all that is related
   to prefixes, nominals, and vId/nom rules
-}


addFormulas :: CmdLineParams -> Branch -> [PrFormula] -> BranchInfo
addFormulas clp br (hd:tl) = case (addFormula clp br hd) of
                               BranchOK br2         -> addFormulas clp br2 tl
                               bi@(BranchClash _ _) -> bi

addFormulas _ br [] = BranchOK br


addFormula :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
-- Case 1 :
-- p : a (a nominal)
addFormula clp br f@(PrFormula pr (PosLit (N n)))
  = addFormulas2 clp brUpdated (f:newFormulas)
     where matrix = (nomPrefMatrix br)
           (newMatrix,updatedNominals,newUrfather) = addElement_ matrix (pr,n)
           updatedNomToPref = Map.union (Map.fromList $ zip updatedNominals $ repeat newUrfather) (nomToPref br) -- update urfather(s)
           oldUrfathers = elems $ urfathersOfNominals (nomToPref br) (singleton pr::Set Int) updatedNominals
           urfathersToRetrieveFormulasFrom = delete newUrfather oldUrfathers -- avoid copying into the same prefix
           formulasToCopy = flatten $ map (getFormulas br) urfathersToRetrieveFormulasFrom
           newFormulas = map (PrFormula newUrfather) formulasToCopy
    -- we don't test if the new urfather is really new or the same as current one, hoping duplication will be avoided later
           brUpdated = br{nomPrefMatrix = newMatrix, nomToPref=updatedNomToPref}


-- Case 2
-- p : phi (not nominal)

-- if we work with the modal language
addFormula clp br f | isModal br =  addFormula2 clp br f

-- if we work with the hybrid language
addFormula clp br f@(PrFormula pr f2) 
 = addFormulas2 clp newBr (f:newFormula)
    where newBr      = addToPrefToForms br f
          m_urfather   = getUrfather br pr
          newFormula = case m_urfather of
                        Just urfather -> [PrFormula urfather f2]
                        Nothing -> []

{-
   Functions related to vId, nom, prefixes and nominals ...
-}

getFormulas :: Branch -> Prefix -> [Formula]
getFormulas br p = Map.findWithDefault [] p (prefToForms br)



addToPrefToForms :: Branch -> PrFormula -> Branch
addToPrefToForms br (PrFormula pre f) = br{prefToForms = newMap}
                                        where currentMap = prefToForms br
                                              newMap = Map.insertWith (\x y -> x++y) pre [f] currentMap

urfathersOfNominals :: NomToEarliestPref -> Set Int -> [Int] -> Set Int
-- takes the (nom -> earliest prefix) map
--       and a list of nominals
-- outputs the set of urfathers of these nominals (so that there are no doubles)
urfathersOfNominals ntp s (hd:tl) = case (Map.lookup hd ntp) of
                                     Just ur -> urfathersOfNominals ntp (insert ur s) tl
                                     Nothing -> urfathersOfNominals ntp s tl
urfathersOfNominals _   s [] = s

getUrfather :: Branch -> Prefix -> Maybe Prefix
getUrfather br pr = case m_idx1 of
                      Just idx1 -> indexOfEarliest $ (getColumn mat idx1)
                      Nothing -> Nothing
                     where mat = (nomPrefMatrix br)
                           m_idx1 = indexOfEarliest $ getLineT mat pr

{-
   Functions to read and write the prefix<->nominal array
-}

-- returns the updated matrix,
-- the list of indexes of modified columns
-- and the new urfather of the new equivalence class
addElement_ :: Matrix -> (Int,Int) -> (Matrix,[Int],Prefix)
addElement_ m (p,n) = runST (do tmp <- thaw m
                                (colIdxs,newUr) <- addElement tmp (p,n)
                                res <- freeze tmp
                                return (res,colIdxs,newUr))

getLineT :: Matrix -> Int -> Line
getLineT t lineNum = getLine' t lineNum 0 width
                     where width = (snd $ snd $ UArray.bounds t)

getLine' :: Matrix -> Int -> Int -> Int -> [Bool]
getLine' _ _ _ (-1) = []
getLine' t lineNum colNum remainder = (hd:tl)
                                      where hd = t UArray.! (lineNum,colNum)
                                            tl = getLine' t lineNum (colNum+1) (remainder-1)


getColumn :: Matrix -> Int -> Column
getColumn t column = getColumn' t column 0 height
                     where height = (fst $ snd $ UArray.bounds t)

getColumn' :: Matrix -> Int -> Int -> Int -> [Bool]
getColumn' _ _ _ (-1) = []
getColumn' t colNum lineNum remainder = (hd:tl)
                                        where hd = t UArray.! (lineNum,colNum)
                                              tl = getColumn' t colNum (lineNum+1) (remainder-1)



{-
   "add formula(s)" functions, that update the "seen structure"
   to detect clashes, and store the new formula in the right sub-structure
   (can't be called from outside this module)
-}

addFormulas2 :: CmdLineParams -> Branch -> [PrFormula] -> BranchInfo
addFormulas2 clp br (hd:tl) = case (addFormula2 clp br hd) of
                               BranchOK br2         -> addFormulas2 clp br2 tl
                               bi@(BranchClash _ _) -> bi

addFormulas2 _ br [] = BranchOK br


addFormula2 :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
addFormula2 clp br f@(PrFormula _ (Con _))
           = if (fullClash clp) then  case (addAndUpdateMap br f) of
                                        BranchOK bok       -> BranchOK bok{conjStr = (f:(conjStr bok))}
                                        bc@(BranchClash _ _) -> bc
                                else  BranchOK br{conjStr = (f:(conjStr br))}

addFormula2 clp br f@(PrFormula _ (Dis _))
           = if (fullClash clp) then  case (addAndUpdateMap br f) of
                                        BranchOK bok       -> BranchOK bok{disjStr = (f:(disjStr bok))}
                                        bc@(BranchClash _ _) -> bc
                                else  BranchOK br{disjStr = (f:(disjStr br))}


addFormula2 clp br f@(PrFormula _ (Box _ _))
           = if (fullClash clp) then  case (addAndUpdateMap br f) of
                                        BranchOK bok       -> BranchOK bok{boxStr = (f:(boxStr bok))}
                                        bc@(BranchClash _ _) -> bc
                                else  BranchOK br{boxStr = (f:(boxStr br))}

addFormula2 clp br f@(PrFormula _ (Dia _ _))
           = if (fullClash clp) then  case (addAndUpdateMap br f) of
                                        BranchOK bok       -> BranchOK bok{diaStr = (f:(diaStr bok))}
                                        bc@(BranchClash _ _) -> bc
                                else  BranchOK br{diaStr = (f:(diaStr br))}


addFormula2 clp br f@(PrFormula _ (At _ _))
           = if (fullClash clp) then  case (addAndUpdateMap br f) of
                                        BranchOK bok       -> BranchOK bok{atStr = (f:(atStr bok))}
                                        bc@(BranchClash _ _) -> bc
                                else  BranchOK br{atStr = (f:(atStr br))}


addFormula2 clp br f@(PrFormula _ (Neg _))
           = if (fullClash clp) then  case (addAndUpdateMap br f) of
                                        BranchOK bok       -> BranchOK bok{negStr = (f:(negStr bok))}
                                        bc@(BranchClash _ _) -> bc
                                else  BranchOK br{negStr = (f:(negStr br))}


addFormula2 _ br f@(PrFormula _ (NegLit (N _)))
           = case (addAndUpdateMap br f) of
               BranchOK bok         -> BranchOK bok{negNomStr = (f:(negNomStr bok))}
               bc@(BranchClash _ _) -> bc

-- then these 2 must be at the end
addFormula2 _ br f@(PrFormula _ (PosLit _))
           = addAndUpdateMap br f

addFormula2 _ br f@(PrFormula _ (NegLit _))
           = addAndUpdateMap br f

{-
   other modifications that can be done by a rule application
-}


addAccFormula :: Branch -> AccFormula -> Branch
addAccFormula br f = br{accStr=(f:(accStr br))}

--

addBoxRuleCheck :: Branch -> (PrFormula,AccFormula) -> Branch
addBoxRuleCheck br c = br{boxRlCh=(c:(boxRlCh br))}

--

incLastPr :: Branch -> Branch
incLastPr br = br{lastPr = ((lastPr br)+1)}

--

remFormula :: Branch  -> PrFormula -> Branch
remFormula br f@(PrFormula _ (Con _))        = br{conjStr=(delete f (conjStr br))}
remFormula br f@(PrFormula _ (Dia _ _))      = br{diaStr=(delete f (diaStr br))}
remFormula br f@(PrFormula _ (Dis _))        = br{disjStr=(delete f (disjStr br))}
remFormula br f@(PrFormula _ (Neg _))        = br{negStr=(delete f (negStr br))}
remFormula br f@(PrFormula _ (Box _ _))      = error "that formula should never be deleted"
remFormula br f@(PrFormula _ (At _ _))       = br{atStr=(delete f (atStr br))}
remFormula br f@(PrFormula _ (PosLit _))     = error "that formula should never be deleted"
remFormula br f@(PrFormula _ (NegLit (N _))) = br{negNomStr=(delete f (negNomStr br))}
remFormula br f@(PrFormula _ (NegLit _))     = error "that formula should never be deleted"


{-
    Monad related stuff
-}

data BranchData = BranchData { branch_info :: BranchInfo,
                               branch_clp :: CmdLineParams,
                               branch_path :: [Int]}

type BranchMonad a = StateT BranchData (StateT Statistics IO) a

mAddAccFormula :: AccFormula -> BranchMonad ()
mAddAccFormula accf = modifyIfOk ((flip addAccFormula) accf)

mAddBoxRuleCheck :: (PrFormula,AccFormula) -> BranchMonad ()
mAddBoxRuleCheck brc = modifyIfOk ((flip addBoxRuleCheck) brc)

mIncLastPr :: BranchMonad ()
mIncLastPr  = modifyIfOk incLastPr

mRemFormula :: PrFormula -> BranchMonad ()
mRemFormula pf = modifyIfOk ((flip remFormula) pf)

modifyIfOk :: (Branch -> Branch) -> BranchMonad ()
modifyIfOk f = modify (\bd -> case (branch_info bd) of
                               (BranchOK br) -> bd{branch_info=(BranchOK (f br))}
                               _             -> bd)     -- do nothing

mAddFormulas ::  [PrFormula] -> BranchMonad ()
mAddFormulas pfs = modify (\bd -> case (branch_info bd) of
                                   (BranchOK br) -> bd{branch_info=(addFormulas (branch_clp bd) br pfs)}
                                   _             -> bd)

--

initialBranchStateFor :: (MonadState BranchData m) =>  (m a -> BranchData -> b) -> BranchData -> m a -> b
initialBranchStateFor f bd = flip f bd

--

getCLParams :: BranchMonad CmdLineParams
getCLParams = do bd <- get
                 return (branch_clp bd)

{-
  Functions to update the "seen structures" map
-}


addAndUpdateMap :: Branch -> PrFormula -> BranchInfo
addAndUpdateMap br prf@(PrFormula pr (Neg f))
  = case (updateMap (seenStr br) (pr,f) False) of
     Just m  -> BranchOK br{seenStr = m}
     Nothing -> BranchClash br prf

addAndUpdateMap br prf@(PrFormula pr (NegLit a))
  = case (updateMap (seenStr br) (pr,(PosLit a)) False) of
     Just m  -> BranchOK br{seenStr = m}
     Nothing -> BranchClash br prf

addAndUpdateMap br prf@(PrFormula pr f)
  = case (updateMap (seenStr br) (pr,f) True) of
     Just m  -> BranchOK br{seenStr = m}
     Nothing -> BranchClash br prf


updateMap :: Seen_structure -> (Prefix,Formula) -> Bool -> Maybe Seen_structure
updateMap ss (pre,PosLit Taut) True
    = Just (Map.insert (PrFormula pre (PosLit Taut)) True ss) -- TODO no need to do anything -> return seen_structure

updateMap _ ( _ ,PosLit Taut) False
    = Nothing


updateMap ss (pre,PosLit a) b
  = case (Map.lookup (PrFormula pre (PosLit a)) ss) of
       Just b2 -> if b == b2 then Just ss
                             else Nothing                   -- clash!
       Nothing -> Just (Map.insert (PrFormula pre (PosLit a)) b ss)

updateMap _ (_,NegLit _) _
    = error $ "shouldn't happen"

updateMap ss (pre,f) b           -- Conj, Disj , Box, Dia, At
    = case (Map.lookup (PrFormula pre f) ss) of
       Just b2 -> if b == b2 then Just ss
                             else Nothing                   -- clash!
       Nothing -> Just (Map.insert (PrFormula pre f) b ss)


isModal :: Branch -> Bool
-- True if we are in the modal language
isModal br = (inputLanguage br) == 0
