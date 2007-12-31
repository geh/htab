----------------------------------------------------
--                                                --
-- Branch.hs                                      --
--                                                --
----------------------------------------------------


module Branch
(
Branch(..), BranchMonad, incLastPr, BranchInfo(..),
addFormulas, addFormula, addAccFormula, remFormula,
addBoxRuleCheck, addDiaRuleCheck, BranchData(..),branch_depth,
emptyBranch,initialBranchStateFor,getCLParams,
addZeroInPath,incPathHead,nominals,prefixes,Box_rule_chart,
getUrfather
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
import Data.List(delete, nub)

import qualified Data.Map as Map

import Statistics(Statistics)
import CommandLine(CmdLineParams, fullClash)

import Formula
import qualified Data.Set as Set

import qualified DisjSet as DS

import LatexOutputHelper
import Ix(range)

data BranchInfo = BranchOK Branch |
                  BranchClash Branch Prefix BranchingPrefixes Formula

-- Lit structure is a Map, because it's easier to detect clashed
-- by looking if there is already something at the (prefix, prop) place
-- and if what is there contradicts what we want to add

type Seen_structure   = Map.Map (Prefix,Formula) (Bool,BranchingPrefixes)
type Conj_structure   = Set.Set PrFormula
type Disj_structure   = Set.Set PrFormula
type Dia_structure    = Set.Set PrFormula
type Neg_structure    = Set.Set PrFormula
type At_structure     = Set.Set PrFormula
type NegNom_structure = Set.Set PrFormula
type Box_structure    = Map.Map (Prefix,Rel) [(BranchingPrefixes,Formula)]
type Acc_structure    = Map.Map (Prefix,Rel) [(BranchingPrefixes,Prefix)]
type Box_rule_chart   = Map.Map (Prefix,Rel,Prefix) (Set.Set Formula)
type Dia_rule_chart   = Map.Map Prefix (Set.Set Formula)

type PrefToFormulas    = Map.Map Prefix [(BranchingPrefixes,Formula)]
type PrefToBrPrefs     = Map.Map Prefix BranchingPrefixes

type EquivClasses = DS.DisjSet DS.Pointer

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
                       diaRlCh :: Dia_rule_chart,
                        lastPr :: Prefix,
                   prefToForms :: PrefToFormulas,
                   prToBrPrefs :: PrefToBrPrefs,
                nomPrefClasses :: EquivClasses,
                 inputLanguage :: LanguageInfo,
                  newToOldNoms :: NewToOldNomsMap}

--

branch_depth :: BranchData -> Int
branch_depth b = length $ branch_path b

--
emptyBranch :: LanguageInfo -> NewToOldNomsMap -> Branch
emptyBranch l ntom =
                Branch
                { seenStr= Map.empty::Seen_structure,
                  conjStr= Set.empty::Conj_structure,
                  disjStr= Set.empty::Disj_structure,
                  diaStr = Set.empty::Dia_structure,
                  boxStr = Map.empty::Box_structure,
                  negStr = Set.empty::Neg_structure,
                  atStr= Set.empty::At_structure,
                  accStr=Map.empty::Acc_structure,
                  boxRlCh=Map.empty::Box_rule_chart,
                  diaRlCh=Map.empty::Dia_rule_chart,
                  negNomStr= Set.empty::NegNom_structure,
                  lastPr= 0 ,
                  prefToForms= Map.empty::PrefToFormulas,
                  prToBrPrefs= Map.empty::PrefToBrPrefs,
                  nomPrefClasses= DS.mkDSet::EquivClasses,
                  inputLanguage = l,
                  newToOldNoms = ntom
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
              "\nDia rule chart: " ++ show (diaRlCh br)  ++
              "\nBiggest prefix: " ++ show (lastPr br) ++
              "\nPrefix to branching prefixes: " ++ show (Map.toList $ prToBrPrefs br) ++
              "\nPrefix to formulas: "  ++ show (Map.toList $ prefToForms br) ++
              "\nPrefix-Nominal classes : " ++ show (Map.toList $ nomPrefClasses br)

instance ShowLatex Branch where
 showLatex br = "Input language: " ++ (putEol $ math $ show $ inputLanguage br)   ++ 
              "\nSeen formulas: "  ++ (putEol $ math $ showLatex $ seenStr br)   ++
              "\nConjunctions: "   ++ (putEol $ math $ show $ conjStr br)  ++
              "\nDisjunctions: "   ++ (putEol $ math $ show $ disjStr br)  ++
              "\nDiamonds: "       ++ (putEol $ math $ show $ diaStr br)   ++
              "\nBoxes: "          ++ (putEol $ math $ show $ Map.toList $ boxStr br)   ++
              "\nNegations: "      ++ (putEol $ math $ show $ negStr br)   ++
              "\nAts: "            ++ (putEol $ math $ show $ atStr br)   ++
              "\nNeg noms: "       ++ (putEol $ math $ show $ negNomStr br)   ++
              "\nAccesibility: "   ++ (putEol $ math $ show $ Map.toList $ accStr br)   ++
              "\nBox rule chart: " ++ (putEol $ math $ show $ Map.toList $ boxRlCh br)  ++
              "\nDia rule chart: " ++ (putEol $ math $ show $ Map.toList $ diaRlCh br)  ++
              "\nBiggest prefix: " ++ (putEol $ show $ lastPr br) ++
              "\nPrefix to branching prefixes: " ++ (putEol $ math $ show $ Map.toList $ prToBrPrefs br) ++
              "\nPrefix to formulas: \\\\"      ++ (putEol $ math $ showLatex $ prefToForms br) ++
              "\nPrefix-Nominal classes : " ++ (putEol $ verbatim $ show $ nomPrefClasses br)


instance ShowLatex PrefToFormulas where
 showLatex ptf =
   (genericSeparate showLat) "\\\\" $ Map.toList ptf
    where showLat (p,fs)  = (bold $ show p) ++ ":" ++ ("[" ++ (separate ", " fs) ++ "]")

instance ShowLatex Seen_structure where
 showLatex ss  = 
   "[" ++ ((genericSeparate showLat) ", " $ Map.toList ss) ++ "]"
    where showLat (pf,(b,bpfs)) = if b then "" ++ "(" ++ (showLatex pf) ++ ")(" ++ showLatex bpfs ++ ")"
                                       else "\\neg" ++ "(" ++ (showLatex pf) ++ ")(" ++ showLatex bpfs ++ ")"

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
addFormula clp br f@(PrFormula pr bprs f2@(PosLit (N (NomSymbol n))))
  = addFormulas2 clp brUpdated nubbedNewFormulas
     where classes = nomPrefClasses br
           ((DS.Prefix rootP),classes2) = DS.find (DS.Prefix pr) classes

           (nomAncestor,classes3) = DS.find (DS.Nominal n) classes2

           oldUrfathers = nub $ rootP : case nomAncestor of
                                         (DS.Nominal _) -> [] -- if the nominal was not yet in the classes
                                         (DS.Prefix rr) -> [rr]

           newUrfather = minimum oldUrfathers

           classes4 = DS.union (DS.Prefix pr) (DS.Nominal n) classes3

           currentDependencies = bps_unions $ bprs:(map (findDeps br) oldUrfathers)
           updatedPrToBrPrefs = Map.insert newUrfather currentDependencies (prToBrPrefs br)

           urfathersToRetrieveFormulasFrom = delete newUrfather oldUrfathers -- avoid copying into the same prefix

           formulasToCopy = concatMap (getFormulas br) urfathersToRetrieveFormulasFrom
           formulasToCopy2 = (PrFormula newUrfather bprs f2):(map (\(bprs2,f_) -> PrFormula newUrfather (bps_union currentDependencies bprs2) f_) formulasToCopy)

           nubbedNewFormulas = nubAndMergeDeps (f:formulasToCopy2)
           brUpdated         = br{nomPrefClasses = classes4,
                                  prToBrPrefs    = updatedPrToBrPrefs}




-- Case 2
-- p : phi (not nominal)

-- if we work with the modal language
addFormula clp br f | isModal br =  addFormula2 clp br f

-- if we work with the hybrid language
addFormula clp br f@(PrFormula pr bprs f2)
 = addFormulas2 clp newBr (f:newFormula)
    where   (urfather,bprs2,newClasses) = getUrfatherAndDeps br (DS.Prefix pr)
            newFormula = if urfather == pr
                          then []
                          else [PrFormula urfather (bps_union bprs bprs2) f2]
            newBr = br{nomPrefClasses = newClasses}


nubAndMergeDeps :: [PrFormula] -> [PrFormula]
-- Rationale : because of the equivalence classes, a same formula can be added to a branch
-- as several prefixed formulas with different branching dependencies. This functions takes
-- a list of prefixes formulas, looks which inner formulas are the same and merge their
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


getUrfather :: Branch -> DS.Pointer -> Prefix
getUrfather b p = u
                  where (u,_,_) = getUrfatherAndDeps b p

getUrfatherAndDeps :: Branch -> DS.Pointer -> (Prefix,BranchingPrefixes,EquivClasses)
-- check if matrix size not enough for this urfather (eg when the prefix is created from the <> rule) -> return Nothing
getUrfatherAndDeps br p =
   if DS.isRoot p classes then defaultAnswer
                          else (ur,deps,newClasses)
  where classes = nomPrefClasses br
        (urfather, newClasses) = DS.find p classes -- TODO update branch's classes
        (DS.Prefix ur) = urfather
        DS.Prefix unboxedP = p
        defaultAnswer = (unboxedP,bps_empty,classes)
        deps = findDeps br ur

findDeps :: Branch -> Prefix -> BranchingPrefixes
findDeps br pr = Map.findWithDefault bps_empty pr (prToBrPrefs br)



{-
   "add formula(s)" functions, that update the "seen structure"
   to detect clashes, and store the new formula in the right sub-structure
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
           = modBranchCaseFC clp br pf $ \b f -> b{conjStr = Set.insert f (conjStr b)}

addFormula2 clp br pf@(PrFormula _ _ (Dis _))
           = modBranchCaseFC clp br pf $ \b f -> b{disjStr = Set.insert f (disjStr b)}

addFormula2 clp br pf@(PrFormula _ _ (Box _ _))
           = modBranchCaseFC clp br pf
              $ \b (PrFormula pr bprs (Box (RelSymbol r) f)) -> b{boxStr = Map.insertWith (++) (pr,r) [(bprs,f)] (boxStr b)}

addFormula2 clp br pf@(PrFormula _ _ (Dia _ _))
           = modBranchCaseFC clp br pf $ \b f@(PrFormula pr _ f2)
                                             -> b{diaStr  = if diaAlreadyDone b pr f2
                                                              then diaStr b
                                                              else Set.insert f (diaStr b)}

addFormula2 clp br pf@(PrFormula _ _ (At _ _))
           = modBranchCaseFC clp br pf $ \b f -> b{atStr   = Set.insert f (atStr b)}

addFormula2 clp br pf@(PrFormula _ _ (Neg _))
           = modBranchCaseFC clp br pf $ \b f -> b{negStr  = Set.insert f (negStr b)}

addFormula2 _ br f@(PrFormula _ _ (NegLit (N _)))
           = case (addAndUpdateMap br f) of
               BranchOK bok             -> BranchOK bok{negNomStr = Set.insert f (negNomStr bok)}
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
addAccFormula br (AccFormula bprs (RelSymbol r) p1 p2) =
  br{accStr=Map.insertWith (++) (p1,r) [(bprs,p2)] (accStr br)}

addAccFormula _ (AccFormula _ (InvRelSymbol _) _ _ ) = error "inverse modality not handled"
--

addBoxRuleCheck :: Branch -> (Prefix,Rel,Prefix,Formula) -> Branch
addBoxRuleCheck br (p1,r,p2,f) =
  br{boxRlCh=Map.insertWith Set.union (p1,r,p2) (Set.singleton f) (boxRlCh br)}

--

addDiaRuleCheck :: Branch -> Prefix -> Formula -> Branch
addDiaRuleCheck br pr f =
  br{diaRlCh=Map.insertWith Set.union pr (Set.singleton f) (diaRlCh br)}

--

diaAlreadyDone :: Branch -> Prefix -> Formula -> Bool
diaAlreadyDone b p f@(Dia _ _) =
  case Map.lookup p (diaRlCh b) of
     Nothing  -> False
     Just fset -> Set.member f fset

diaAlreadyDone _ _ _ = error "dia already done : wrong formula kind"


--

incLastPr :: Branch -> Branch
incLastPr br = br{lastPr = ((lastPr br)+1)}

--

remFormula :: Branch  -> PrFormula -> Branch
remFormula br f@(PrFormula _ _ (Con _))        = br{conjStr=(Set.delete f (conjStr br))}
remFormula br f@(PrFormula _ _ (Dia _ _))      = br{diaStr=(Set.delete f (diaStr br))}
remFormula br f@(PrFormula _ _ (Dis _))        = br{disjStr=(Set.delete f (disjStr br))}
remFormula br f@(PrFormula _ _ (Neg _))        = br{negStr=(Set.delete f (negStr br))}
remFormula _    (PrFormula _ _ (Box _ _))      = error "that formula should never be deleted"
remFormula br f@(PrFormula _ _ (At _ _))       = br{atStr=(Set.delete f (atStr br))}
remFormula _    (PrFormula _ _ (PosLit _))     = error "that formula should never be deleted"
remFormula br f@(PrFormula _ _ (NegLit (N _))) = br{negNomStr=(Set.delete f (negNomStr br))}
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
isModal br = (inputLanguage br) == 0

nominals :: Branch -> [NomSymbol]
nominals br = map NomSymbol $ range (0,(inputLanguage br) - 1)

prefixes :: Branch -> [Prefix]
prefixes br = range (0,lastPr br)

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

