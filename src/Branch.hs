----------------------------------------------------
--                                                --
-- Branch.hs                                      --
--                                                --
----------------------------------------------------


module Branch
(
Branch(..), BranchMonad, incLastPr, BranchInfo(..),
addFormulas, addFormula, addAccFormula, remFormula,
addBoxRuleCheck, BranchData(..),branch_depth,
emptyBranch,initialBranchStateFor,getCLParams,
addZeroInPath,incPathHead,nominals,Box_rule_chart

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


import Control.Monad.State(StateT, MonadState, get)
import Data.List(delete)
import qualified Data.Map as Map

import Statistics(Statistics)
import CommandLine(CmdLineParams, fullClash)
import Formula
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set


import qualified Data.Array.Unboxed as UArray
import SpecialMatrix(addElement,newUArray,
                     indexOfEarliest,Column,Row)

import Control.Monad.ST(runST)
import Data.Array.MArray(thaw,freeze)

import LatexOutputHelper
import Ix(range)

data BranchInfo = BranchOK Branch |
                  BranchClash Branch Prefix BranchingPrefixes Formula

-- Lit structure is a Map, because it's easier to detect clashed
-- by looking if there is already something at the (prefix, prop) place
-- and if what is there contradicts what we want to add

type Seen_structure   = Map.Map (Prefix,Formula) (Bool,BranchingPrefixes)
type Conj_structure   = [PrFormula]
type Disj_structure   = [PrFormula]
type Dia_structure    = [PrFormula]
type Neg_structure    = [PrFormula]
type At_structure     = [PrFormula]
type NegNom_structure = [PrFormula]
type Box_structure    = Map.Map (Prefix,Rel) [(BranchingPrefixes,Formula)]
type Acc_structure    = Map.Map (Prefix,Rel) [(BranchingPrefixes,Prefix)]
type Box_rule_chart   = Map.Map (Prefix,Rel,Prefix) (Set.Set Formula)


type NomToEarliestPref = Map.Map Nominal Prefix
type PrefToFormulas    = Map.Map Prefix [(BranchingPrefixes,Formula)]
type PrefToBrPrefs     = Map.Map Prefix BranchingPrefixes -- a urfather holds all the dependencies of its class

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
                   prToBrPrefs :: PrefToBrPrefs,
                 nomPrefMatrix :: Matrix,
                 inputLanguage :: Int}

--

branch_depth :: BranchData -> Int
branch_depth b = length $ branch_path b

--
emptyBranch :: LanguageInfo -> Branch
emptyBranch l =
                Branch
                { seenStr= Map.empty::Seen_structure,
                  conjStr=[],
                  disjStr=[],
                  diaStr=[],
                  boxStr=Map.empty::Box_structure,
                  negStr=[],
                  atStr=[],
                  accStr=Map.empty::Acc_structure,
                  boxRlCh=Map.empty::Box_rule_chart,
                  negNomStr=[],
                  lastPr= 0 ,
                  nomToPref= Map.empty::NomToEarliestPref,
                  prefToForms= Map.empty::PrefToFormulas,
                  prToBrPrefs= Map.empty::PrefToBrPrefs,
                  nomPrefMatrix = newUArray ((1,1),(0,0)),
                  inputLanguage = l
                }

instance Show Branch where
    show br = "Input language: " ++ show (inputLanguage br) ++
              "\nSeen formulas: "  ++ show (Map.toList $ seenStr br)   ++
              "\nConjunctions: "   ++ show (conjStr br)  ++
              "\nDisjunctions: "   ++ show (disjStr br)  ++
              "\nDiamonds: "       ++ show (diaStr br)   ++
              "\nBoxes: "          ++ show (boxStr br)   ++
              "\nNegations: "      ++ show (negStr br)   ++
              "\nAts: "            ++ show (atStr br)    ++
              "\nNeg noms: "       ++ show (negNomStr br)  ++
              "\nAccesibility: "   ++ show (accStr br)   ++
              "\nBox rule chart: " ++ show (boxRlCh br)  ++
              "\nBiggest prefix: " ++ show (lastPr br) ++
              "\nNominal to earliest prefix: "    ++ show (Map.toList $ nomToPref br) ++
              "\nPrefix to branching prefixes: " ++ show (Map.toList $ prToBrPrefs br) ++
              "\nPrefix to formulas: "  ++ show (Map.toList $ prefToForms br)

instance ShowLatex Branch where
 showLatex br = "Input language: " ++ (putEol $ math $ show $ inputLanguage br)   ++ 
              "\nSeen formulas: "  ++ (putEol $ math $ showLatex $ seenStr br)   ++
              "\nConjunctions: "   ++ (putEol $ math $ separate ", " $ conjStr br)  ++
              "\nDisjunctions: "   ++ (putEol $ math $ separate ", " $ disjStr br)  ++
              "\nDiamonds: "       ++ (putEol $ math $ separate ", " $ diaStr br)   ++
              "\nBoxes: "          ++ (putEol $ math $ show $ Map.toList $ boxStr br)   ++
              "\nNegations: "      ++ (putEol $ math $ separate ", " $ negStr br)   ++
              "\nAts: "            ++ (putEol $ math $ separate ", " $ atStr br)   ++
              "\nNeg noms: "       ++ (putEol $ math $ separate ", " $ negNomStr br)   ++
              "\nAccesibility: "   ++ (putEol $ math $ show $ Map.toList $ accStr br)   ++
              "\nBox rule chart: " ++ (putEol $ math $ show $ Map.toList $ boxRlCh br)  ++
              "\nBiggest prefix: " ++ (putEol $ show $ lastPr br) ++
              "\nNominal to earliest prefix: "  ++ (putEol $ showLatex $ nomToPref br)   ++
              "\nPrefix to branching prefixes: " ++ (putEol $ showLatex $ prToBrPrefs br) ++
              "\nPrefix to formulas: \\\\"      ++ (putEol $ math $ showLatex $ prefToForms br) ++
              "\nPrefix-Nominal matrix : " ++ (verbatim $ showLatex $ nomPrefMatrix br)

instance ShowLatex NomToEarliestPref where
 showLatex ntep = show $ Map.toList ntep

instance ShowLatex PrefToBrPrefs where
 showLatex ntep = show $ Map.toList ntep

instance ShowLatex PrefToFormulas where
 showLatex ptf =
   (genericSeparate showLat) "\\\\" $ Map.toList ptf
    where showLat (p,fs)  = (bold $ show p) ++ ":" ++ ("[" ++ (separate ", " fs) ++ "]")

instance ShowLatex Seen_structure where
 showLatex ss  = 
   "[" ++ ((genericSeparate showLat) ", " $ Map.toList ss) ++ "]"
    where showLat (pf,(b,bpfs)) = if b then "" ++ "(" ++ (showLatex pf) ++ ")(" ++ showLatex bpfs ++ ")"
                                       else "\\neg" ++ "(" ++ (showLatex pf) ++ ")(" ++ showLatex bpfs ++ ")"


instance ShowLatex Matrix where
 showLatex m = foldr insertEol "" $ map (separate " " . (getRow m)) (range (firstRow,lastDisplayedRow))
                  where firstRow = fst $ fst $ UArray.bounds m
                        lastRow  = fst $ snd $ UArray.bounds m
                        lastDisplayedRow = min lastRow 5

genericSeparate :: (a -> String) ->  String -> [a] -> String
genericSeparate _ _ [] = ""
genericSeparate f s os = foldl1 (\a1 a2 -> (a1 ++ s ++ a2)) $ map f os

--

{-
   "add formula(s)" functions, that handle all that is related
   to prefixes, nominals, and vId/nom rules
-}


addFormulas :: CmdLineParams -> Branch -> [PrFormula] -> BranchInfo
addFormulas clp br (hd:tl) = case (addFormula clp br hd) of
                               BranchOK br2             -> addFormulas clp br2 tl
                               bi@(BranchClash _ _ _ _) -> bi

addFormulas _ br [] = BranchOK br


addFormula :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
-- Case 1 :
-- p : a (a nominal)
addFormula clp br f@(PrFormula pr bprs f2@(PosLit (N n)))
  = addFormulas2 clp brUpdated nubbedNewFormulas
     where oldMatrixData    = UArray.assocs $ nomPrefMatrix br
           newMRowLength    = (lastPr br) + 1             -- 1 unit longer because in between, we may have created a new prefix
           newMColLength    = (inputLanguage br) - 1
           biggerOldMatrix  = newUArray ((0,0),(newMRowLength,newMColLength)) UArray.// oldMatrixData  -- make a (possibily) bigger matrix
           (newMatrix,updatedNominals,newUrfather) = addElement_ biggerOldMatrix (pr,n)
           updatedNomToPref = Map.union (Map.fromList $ zip updatedNominals $ repeat newUrfather) (nomToPref br) -- update urfather(s)
           oldUrfathers     = IntSet.elems $ urfathersOfNominals (nomToPref br) (IntSet.singleton pr) updatedNominals

           currentDependencies = bps_unions $ bprs:(map (findDeps br) oldUrfathers)
           updatedPrToBrPrefs = Map.insert pr currentDependencies (prToBrPrefs br)

           urfathersToRetrieveFormulasFrom = delete newUrfather oldUrfathers -- avoid copying into the same prefix
           formulasToCopy = concatMap (getFormulas br) urfathersToRetrieveFormulasFrom
           formulasToCopy2 = (PrFormula newUrfather bprs f2):(map (\(bprs2,f_) -> PrFormula newUrfather (bps_union currentDependencies bprs2) f_) formulasToCopy)

           nubbedNewFormulas = nubAndMergeDeps (f:formulasToCopy2)
           brUpdated         = br{nomPrefMatrix = newMatrix,
                                  nomToPref     = updatedNomToPref,
                                  prToBrPrefs   = updatedPrToBrPrefs}




-- Case 2
-- p : phi (not nominal)

-- if we work with the modal language
addFormula clp br f | isModal br =  addFormula2 clp br f

-- if we work with the hybrid language
addFormula clp br f@(PrFormula pr bprs f2)
 = addFormulas2 clp br (f:newFormula)
    where newFormula = case (getUrfatherAndDeps br pr) of
                        Just (urfather,bprs2) -> if urfather == pr
                                                  then []
                                                  else [PrFormula urfather (bps_union bprs bprs2) f2]
                        Nothing -> []


nubAndMergeDeps :: [PrFormula] -> [PrFormula]
-- Rationale : because of the equivalence classes, a same formula can be added to a branch as several prefixed formulas with different
-- branching dependencies. This functions takes a list of prefixes formulas, looks which inner formulas are the same and merge their
-- branching dependencies.
nubAndMergeDeps prfs =  namd prfs (Map.empty::Map.Map (Prefix,Formula) BranchingPrefixes)

namd :: [PrFormula] -> Map.Map (Prefix,Formula) BranchingPrefixes -> [PrFormula]
namd ((PrFormula p bps f):prfs) theMap =
  namd prfs (Map.insertWith bps_union (p,f) bps theMap)

namd [] theMap = map (\((p,f),bps) -> PrFormula p bps f) (Map.assocs theMap)


{-
   Functions related to vId, nom, prefixes and nominals ...
-}

getFormulas :: Branch -> Prefix -> [(BranchingPrefixes,Formula)]
getFormulas br p = Map.findWithDefault [] p (prefToForms br)


addToPrefToForms :: Branch -> PrFormula -> Branch
addToPrefToForms br (PrFormula pre bprs f) =
  br{prefToForms = newMap}
 where currentMap = prefToForms br
       newMap = Map.insertWith (\x y -> x++y) pre [(bprs,f)] currentMap

urfathersOfNominals :: NomToEarliestPref -> IntSet.IntSet -> [Int] -> IntSet.IntSet
-- takes the (nom -> earliest prefix) map
--       and a list of nominals
-- outputs the set of urfathers of these nominals (so that there are no doubles)
urfathersOfNominals ntp s (hd:tl) = case (Map.lookup hd ntp) of
                                     Just ur -> urfathersOfNominals ntp (IntSet.insert ur s) tl
                                     Nothing -> urfathersOfNominals ntp s tl
urfathersOfNominals _   s [] = s

getUrfatherAndDeps :: Branch -> Prefix -> Maybe (Prefix,BranchingPrefixes)
-- check if matrix size not enough for this urfather (eg when the prefix is created from the <> rule) -> return Nothing
getUrfatherAndDeps br pr =
  case nominal_idx1 of
   Just nidx -> case (indexOfEarliest $ getColumn mat nidx) of
                  Just urfather -> Just (urfather, deps)
                                    where deps = findDeps br urfather
                  Nothing -> Nothing
   Nothing   -> Nothing
  where mat = nomPrefMatrix br
        maxPrefixInMatrix = fst $ snd $ UArray.bounds mat
        nominals_row = getRow mat pr
        nominal_idx1 = if maxPrefixInMatrix < pr
                        then Nothing
                        else indexOfEarliest nominals_row

findDeps :: Branch -> Prefix -> BranchingPrefixes
findDeps br pr = Map.findWithDefault bps_empty pr (prToBrPrefs br)


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

getRow :: Matrix -> Int -> Row
getRow t rowNum = getRow' t rowNum 0 width
                   where width = (snd $ snd $ UArray.bounds t)

getRow' :: Matrix -> Int -> Int -> Int -> [Bool]
getRow' _ _ _ (-1) = []
getRow' m _ _ _ | matrixIsEmpty m = []
getRow' t rowNum colNum remainder = (hd:tl)
                                      where hd = t UArray.! (rowNum,colNum)
                                            tl = getRow' t rowNum (colNum+1) (remainder-1)


getColumn :: Matrix -> Int -> Column
getColumn t column = getColumn' t column 0 height
                     where height = (fst $ snd $ UArray.bounds t)

getColumn' :: Matrix -> Int -> Int -> Int -> [Bool]
getColumn' _ _ _ (-1) = []
getColumn' m _ _ _ | matrixIsEmpty m = []
getColumn' t colNum rowNum remainder = (hd:tl)
                                        where hd = t UArray.! (rowNum,colNum)
                                              tl = getColumn' t colNum (rowNum+1) (remainder-1)



{-
   "add formula(s)" functions, that update the "seen structure"
   to detect clashes, and store the new formula in the right sub-structure
   (can't be called from outside this module)
-}

addFormulas2 :: CmdLineParams -> Branch -> [PrFormula] -> BranchInfo
addFormulas2 clp br (hd:tl) =
   case (addFormula2 clp updatedPrefToFormsBr hd) of
     BranchOK br2             -> addFormulas2 clp br2 tl
     bi@(BranchClash _ _ _ _) -> bi
   where updatedPrefToFormsBr = addToPrefToForms br hd

addFormulas2 _ br [] = BranchOK br


addFormula2 :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
addFormula2 clp br pf@(PrFormula _ _ (Con _))
           = modBranchCaseFC clp br pf $ \b f -> b{conjStr = f:(conjStr b)}

addFormula2 clp br pf@(PrFormula _ _ (Dis _))
           = modBranchCaseFC clp br pf $ \b f -> b{disjStr = f:(disjStr b)}

addFormula2 clp br pf@(PrFormula _ _ (Box _ _))
           = modBranchCaseFC clp br pf
              $ \b (PrFormula pr bprs (Box r f)) -> b{boxStr = Map.insertWith (++) (pr,r) [(bprs,f)] (boxStr b)}

addFormula2 clp br pf@(PrFormula _ _ (Dia _ _))
           = modBranchCaseFC clp br pf $ \b f -> b{diaStr  = f:(diaStr b) }

addFormula2 clp br pf@(PrFormula _ _ (At _ _))
           = modBranchCaseFC clp br pf $ \b f -> b{atStr   = f:(atStr b)  }

addFormula2 clp br pf@(PrFormula _ _ (Neg _))
           = modBranchCaseFC clp br pf $ \b f -> b{negStr  = f:(negStr b) }

addFormula2 _ br f@(PrFormula _ _ (NegLit (N _)))
           = case (addAndUpdateMap br f) of
               BranchOK bok             -> BranchOK bok{negNomStr = f:(negNomStr bok)}
               bc@(BranchClash _ _ _ _) -> bc

addFormula2 _ br f@(PrFormula _ _ (PosLit _))
           = addAndUpdateMap br f

addFormula2 _ br f@(PrFormula _ _ (NegLit _))
           = addAndUpdateMap br f

modBranchCaseFC :: CmdLineParams -> Branch -> PrFormula
                   -> (Branch -> PrFormula -> Branch)
                   -> BranchInfo
modBranchCaseFC clp br f modBr =
 if (fullClash clp) then case (addAndUpdateMap br f) of
                          BranchOK bok             -> BranchOK $ modBr bok f
                          bc@(BranchClash _ _ _ _) -> bc
                    else  BranchOK $ modBr br f


{-
   other modifications that can be done by a rule application
-}


addAccFormula :: Branch -> AccFormula -> Branch
addAccFormula br (AccFormula bprs r p1 p2) =
  br{accStr=Map.insertWith (++) (p1,r) [(bprs,p2)] (accStr br)}

--

addBoxRuleCheck :: Branch -> (Prefix,Rel,Prefix,Formula) -> Branch
addBoxRuleCheck br (p1,r,p2,f) =
  br{boxRlCh=Map.insertWith Set.union (p1,r,p2) (Set.singleton f) (boxRlCh br)}

--

incLastPr :: Branch -> Branch
incLastPr br = br{lastPr = ((lastPr br)+1)}

--

remFormula :: Branch  -> PrFormula -> Branch
remFormula br f@(PrFormula _ _ (Con _))        = br{conjStr=(delete f (conjStr br))}
remFormula br f@(PrFormula _ _ (Dia _ _))      = br{diaStr=(delete f (diaStr br))}
remFormula br f@(PrFormula _ _ (Dis _))        = br{disjStr=(delete f (disjStr br))}
remFormula br f@(PrFormula _ _ (Neg _))        = br{negStr=(delete f (negStr br))}
remFormula _    (PrFormula _ _ (Box _ _))      = error "that formula should never be deleted"
remFormula br f@(PrFormula _ _ (At _ _))       = br{atStr=(delete f (atStr br))}
remFormula _    (PrFormula _ _ (PosLit _))     = error "that formula should never be deleted"
remFormula br f@(PrFormula _ _ (NegLit (N _))) = br{negNomStr=(delete f (negNomStr br))}
remFormula _    (PrFormula _ _ (NegLit _))     = error "that formula should never be deleted"



{-
  Functions to update the "seen structures" map
-}

data UpdateResult = UpdateSuccess Seen_structure | UpdateFailure BranchingPrefixes

addAndUpdateMap :: Branch -> PrFormula -> BranchInfo
addAndUpdateMap br (PrFormula pr bprs formula@(Neg f))
  = case (updateMap (seenStr br) (pr,f) (False,bprs)) of
     UpdateSuccess ss    -> BranchOK br{seenStr = ss}
     UpdateFailure bprs2 -> BranchClash br pr bprs2 formula

addAndUpdateMap br (PrFormula pr bprs f)
  = case (updateMap (seenStr br) (pr,f) (True,bprs)) of
     UpdateSuccess ss    -> BranchOK br{seenStr = ss}
     UpdateFailure bprs2 -> BranchClash br pr bprs2 f


updateMap :: Seen_structure -> (Prefix,Formula) -> (Bool,BranchingPrefixes) -> UpdateResult
updateMap ss (_,PosLit Taut) (True,_) = UpdateSuccess ss

updateMap _ (_,PosLit Taut) (False,bprs) = UpdateFailure bprs

updateMap ss (pre,NegLit a) (bool,bprs)
    = updateMap ss (pre,PosLit a) (not bool,bprs)

updateMap ss (pre,f) (bool,bprs)
  = case (Map.lookup (pre,f) ss) of
       Just (bool2,bprs2) -> if bool == bool2
                              then UpdateSuccess (Map.insert (pre,f) (bool,bps_union bprs bprs2) ss)
                              else UpdateFailure (bps_union bprs bprs2)           -- clash!
       Nothing            -> UpdateSuccess (Map.insert (pre,f) (bool,bprs) ss)



isModal :: Branch -> Bool
-- True if we are in the modal language
isModal br = (inputLanguage br) == 0

matrixIsEmpty :: Matrix -> Bool
matrixIsEmpty m = (fst $ fst $ b) > (fst $ snd $ b)
    where b = (UArray.bounds m)

nominals :: Branch -> [Nominal]
nominals br = range (0,(inputLanguage br) - 1)


{-
    Monad related stuff
-}

data BranchData = BranchData { branch_info :: BranchInfo,
                               branch_clp :: CmdLineParams,
                               branch_path :: [Int]}

type BranchMonad a = StateT BranchData (StateT Statistics IO) a


--

initialBranchStateFor :: (MonadState BranchData m) =>  (m a -> BranchData -> b) -> BranchData -> m a -> b
initialBranchStateFor f bd = flip f bd

--

getCLParams :: BranchMonad CmdLineParams
getCLParams = do bd <- get
                 return (branch_clp bd)


-- functions to be used with " modify "


addZeroInPath :: BranchData -> BranchData
addZeroInPath bd = bd{branch_path=(0:(branch_path bd))}

incPathHead :: BranchData -> BranchData
incPathHead bd = bd{branch_path=(((head (branch_path bd))+1):(tail $ branch_path bd))}

