----------------------------------------------------
--                                                --
-- Branch.hs                                      --
--                                                --
----------------------------------------------------


module Branch
(
Branch(..), BranchMonad, createNewPr, BranchInfo(..),
addFormulas, addFormula, addAccFormula, remFormula,
addDiaRuleCheck, addAtRuleCheck,
addExistRuleCheck, addUnivConstraint, BranchData(..),branch_depth,
emptyBranch,initialBranchStateFor,getCLParams,
addZeroInPath,incPathHead,prefixes,
getUrfather, getUrfatherAndDeps, isUrfather, isInclusionUrfather, isInInclusionUrfatherClass,
getInclusionUrfather, hasUnivMod, inclusionUrfathers,
calculateStepInfo, BlockingMode(..), diaAlreadyDone
) where

import Control.Monad.State(StateT, MonadState, get)
import Data.List(delete, nub, minimumBy)

import qualified Data.Map as Map
import qualified Data.List as List

import Statistics(Statistics)
import CommandLine(CmdLineParams, fullClash)

import Formula
import qualified Data.Set as Set

import qualified DisjSet as DS

import LatexOutputHelper

import Maybe(fromJust)
import DMap
import Base(moveInMap, almostCartesianProduct)

data BranchInfo = BranchOK Branch |
                  BranchClash Branch Prefix BranchingPrefixes Formula

type Clashable_info   = Map.Map Prefix (Map.Map Formula (Bool,BranchingPrefixes))
type Conj_structure   = Set.Set PrFormula
type Disj_structure   = Set.Set PrFormula
type Dia_structure    = Set.Set PrFormula
type Neg_structure    = Set.Set PrFormula
type At_structure     = Set.Set PrFormula
type Exist_structure  = Set.Set PrFormula
type Acc_structure    = Map.Map Prefix (Map.Map Rel [(BranchingPrefixes,Prefix )])
type Box_constraints  = Map.Map Prefix (Map.Map Rel [(BranchingPrefixes,Formula)])

type Dia_rule_chart    = Map.Map Prefix (Set.Set Formula)
type At_rule_chart     = Set.Set Formula
type Exist_rule_chart  = Set.Set Formula

type Univ_constraints  = [(BranchingPrefixes,Formula)]    -- TODO try Map.Map Formula BranchingPrefixes for dependencies update

type PrefToFormulas    = Map.Map Prefix (Set.Set Formula)
type PrefToBrPrefs     = Map.Map Prefix BranchingPrefixes

type EquivClasses = DS.DisjSet DS.Pointer
type InclusionUrfathersMap = Map.Map Prefix Prefix

type AugmentedPrefixes = [Prefix] -- list of prefixes that received formulas during the previous step of the algorithm

data BlockingMode = NoBlocking | InclusionBlocking
 deriving (Eq,Show)

data Branch = Branch {clashStr :: Clashable_info,
                 -- pending formulas
                       conjStr :: Conj_structure,
                       disjStr :: Disj_structure,
                        diaStr :: Dia_structure,
                      existStr :: Exist_structure,
                        negStr :: Neg_structure,
                         atStr :: At_structure,
                 -- other data
                        accStr :: Acc_structure,
                     boxConstr :: Box_constraints,
                       diaRlCh :: Dia_rule_chart,    -- saturation of the diamond rule
                        atRlCh :: At_rule_chart,     -- saturation of the @ rule
                     existRlCh :: Exist_rule_chart,  -- saturation of the exist rule
                      univCons :: Univ_constraints,
                        lastPr :: Prefix,
                   prefToForms :: PrefToFormulas,
                   prToBrPrefs :: PrefToBrPrefs,
                nomPrefClasses :: EquivClasses,
                 inputLanguage :: LanguageInfo,
                     inclUrMap :: Maybe InclusionUrfathersMap,
                       incrPrs :: AugmentedPrefixes,
                     blockMode :: BlockingMode}

--

branch_depth :: BranchData -> Int
branch_depth b = length $ branch_path b

--
emptyBranch :: LanguageInfo -> Branch
emptyBranch l =
                Branch
                { clashStr= Map.empty::Clashable_info,
                  conjStr= Set.empty::Conj_structure,
                  disjStr= Set.empty::Disj_structure,
                  diaStr = Set.empty::Dia_structure,
                  existStr = Set.empty::Exist_structure,
                  negStr = Set.empty::Neg_structure,
                  atStr= Set.empty::At_structure,
                  accStr=Map.empty::Acc_structure,
                  boxConstr=Map.empty::Box_constraints,
                  diaRlCh=Map.empty::Dia_rule_chart,
                  atRlCh=Set.empty::At_rule_chart,
                  existRlCh=Set.empty::Exist_rule_chart,
                  univCons=[],
                  lastPr= 0 ,
                  prefToForms= Map.empty::PrefToFormulas,
                  prToBrPrefs= Map.empty::PrefToBrPrefs,
                  nomPrefClasses= DS.mkDSet::EquivClasses,
                  inputLanguage = l,
                  inclUrMap = Nothing,
                  incrPrs = [],
                  blockMode = NoBlocking
                }

instance Show Branch where
    show br = "Input language: " ++ show (inputLanguage br) ++
              "\nClashable formulas: " ++ prettyShowMap_ (clashStr br) (\v -> "(" ++ prettyShowMap_clashable v ++ ")") "\n " ++
              "\nConjunctions: "   ++ show (Set.toList $ conjStr br)  ++
              "\nDisjunctions: "   ++ show (Set.toList $ disjStr br)  ++
              "\nDiamonds: "       ++ show (Set.toList $ diaStr br)   ++
              "\nExists: "         ++ show (Set.toList $ existStr br) ++
              "\nNegations: "      ++ show (Set.toList $ negStr br)   ++
              "\nAts: "            ++ show (Set.toList $ atStr br)    ++
              "\nAccesibility: "    ++ prettyShowMap_ (accStr br) (\v -> "(" ++ prettyShowMap_rel_bps_x v ++ ")") "\n " ++
              "\nBox constraints: " ++ prettyShowMap_ (boxConstr br) (\v -> "(" ++ prettyShowMap_rel_bps_x v ++ ")") "\n " ++
              "\nDia rule chart: "  ++ prettyShowMap_ (diaRlCh br) (show . Set.toList) "\n " ++
              "\n@ rule chart: "   ++ show (Set.toList $ atRlCh br) ++
              "\nExist rule chart:" ++ show (Set.toList $ existRlCh br) ++
              "\nUniv constraints: "++ show (univCons br) ++
              "\nBiggest prefix: " ++ show (lastPr br) ++
              "\nPrefix to branching prefixes: " ++ prettyShowMap_ (prToBrPrefs br) bps_show "\n " ++
              "\nPrefix to formulas: " ++ prettyShowMap_ (prefToForms br) (show . Set.toList) "\n " ++
              "\nInclusion urfather map: "  ++ show (inclUrMap br) ++
              "\nIncreased prefixes: " ++ show (incrPrs br) ++
              "\nBlocking mode: " ++ show (blockMode br) ++
              "\nPrefix-Nominal classes : " ++ prettyShowMap (nomPrefClasses br) ", "

instance ShowLatex Branch where
 showLatex br = "Input language: " ++ (putEol $ math $ show $ inputLanguage br)   ++ 
              "\nClashable formulas: "  ++ (putEol $ math $ showLatex $ clashStr br)   ++
              "\nConjunctions: "   ++ (putEol $ math $ show $ conjStr br)  ++
              "\nDisjunctions: "   ++ (putEol $ math $ show $ disjStr br)  ++
              "\nDiamonds: "       ++ (putEol $ math $ show $ diaStr br)   ++
              "\nExists: "         ++ (putEol $ math $ show $ existStr br) ++
              "\nNegations: "      ++ (putEol $ math $ show $ negStr br)   ++
              "\nAts: "            ++ (putEol $ math $ show $ atStr br)   ++
              "\nAccesibility: "   ++ (putEol $ math $ show $ Map.toList $ accStr br)   ++
              "\nBox constraints: " ++ (putEol $ math $ show $ Map.toList $ boxConstr br)  ++
              "\nDia rule chart: " ++ (putEol $ math $ show $ Map.toList $ diaRlCh br)  ++
              "\n@ rule chart: "   ++ (putEol $ math $ show $ Set.toList $ atRlCh br)  ++
              "\nExist rule chart:" ++ (putEol $ math $ show $ Set.toList $ existRlCh br)  ++
              "\nUniv constraints: "++ (putEol $ math $ show $ univCons br) ++
              "\nBiggest prefix: " ++ (putEol $ show $ lastPr br) ++
              "\nPrefix to branching prefixes: " ++ (putEol $ math $ show $ Map.toList $ prToBrPrefs br) ++
              "\nPrefix to formulas: \\\\"      ++ (putEol $ math $ showLatex $ prefToForms br) ++
              "\nPrefix-Nominal classes : " ++ (putEol $ math $ show $ nomPrefClasses br) ++
              "\nInclusion urfather map: "  ++ (putEol $ math $ show $ inclUrMap br) ++
              "\nIncreased prefixes: " ++ (putEol $ show (incrPrs br)) ++
              "\nBlocking mode: " ++ show (blockMode br)

instance ShowLatex PrefToFormulas where
 showLatex ptf =
   (genericSeparate showLat) "\\\\" $ Map.toList ptf
    where showLat (p,set_fs)  = (bold $ show p) ++ ":" ++ ("[" ++ (lseparate ", " $ Set.toList set_fs) ++ "]")

instance ShowLatex Clashable_info where
 showLatex cs  = 
   "[" ++ ((genericSeparate showLat) ", " $ flattenDMap cs) ++ "]"
    where showLat (pf,(b,bpfs)) = if b then "" ++ "(" ++ (showLatex pf) ++ ")(" ++ showLatex bpfs ++ ")"
                                       else "\\neg" ++ "(" ++ (showLatex pf) ++ ")(" ++ showLatex bpfs ++ ")"

genericSeparate :: (a -> String) ->  String -> [a] -> String
genericSeparate _ _ [] = ""
genericSeparate f s os = foldl1 (\a1 a2 -> (a1 ++ s ++ a2)) $ map f os



prettyShowMap :: (Show x, Show y) => Map.Map x y -> String -> String
prettyShowMap dasMap separator = prettyShowMap_ dasMap show separator

prettyShowMap_ :: (Show x, Show y) => Map.Map x y -> (y -> String) -> String -> String
prettyShowMap_ dasMap valueShow separator
 = concat $ List.intersperse separator $ map (\(k,v) -> show k ++ " -> " ++ valueShow v)
          $ Map.toList dasMap


prettyShowMap_clashable :: Map.Map Formula (Bool,BranchingPrefixes) -> String
prettyShowMap_clashable dasMap
 = concat $ List.intersperse ", " $ map (\(f,(bo,bp)) -> (if bo then "" else "!") ++ show f ++ " " ++ bps_show bp)
          $ Map.toList dasMap


prettyShowMap_rel_bps_x :: (Show a) => Map.Map Rel [(BranchingPrefixes,a)] -> String
prettyShowMap_rel_bps_x dasMap
 = concat $ List.intersperse ", " $ map (\(r,bp_x_s) -> (++) ("-" ++ show r ++ "-> ") $ concat $ List.intersperse ", "
                                           $ map (\(bp,x) -> show x ++ " " ++ bps_show bp) bp_x_s
                                        )
          $ Map.toList dasMap

--

{-
   "add formula(s)" functions, that handle all that is related
   to prefixes, nominals, and vId/nom rules
-}


addFormulas :: CmdLineParams -> Branch -> [PrFormula] -> BranchInfo
addFormulas clp br (hd:tl)
       = case addFormula clp br hd of
          BranchOK br2             -> addFormulas clp br2 tl
          bi@(BranchClash _ _ _ _) -> bi

addFormulas _ br [] = BranchOK br

addFormula :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
-- Case 1 :
-- p : a (a nominal)
--
addFormula clp br (PrFormula pr newFormulaBprs f2@(PosLit (N (NomSymbol n))))
  = result
     where classes = nomPrefClasses br
           ((DS.Prefix rootP),classes2) = DS.find (DS.Prefix pr) classes

           (nomAncestor,classes3) = DS.find (DS.Nominal n) classes2

           involvedUrfathers = nub $ rootP : case nomAncestor of
                                              (DS.Nominal _) -> []            -- if the nominal was not yet in the classes
                                              (DS.Prefix rr) -> [rr]

           newUrfather = minimum involvedUrfathers
           exUrfathers = delete newUrfather involvedUrfathers

           classes4 = DS.union (DS.Prefix pr) (DS.Nominal n) classes3

           currentDependencies = bps_unions $ newFormulaBprs:(map (findDeps br) involvedUrfathers)
           newPrToBrPrefs = Map.insert newUrfather currentDependencies (prToBrPrefs br)

           -- get clashable formulas from ex urfathers, add the current dependencies, union and see if there is a clash or not
           mClashableInfoSlots = map        (\exUrfather -> Map.lookup exUrfather (clashStr br))  involvedUrfathers
           clashableInfoSlots  = concatMap  (\(mSlot) -> maybe [] (\slot -> [slot]) mSlot )       mClashableInfoSlots

           successOrFailure_newClashableSlotUrfather = addDepsToClashableSlot (clashableInfoSlotsUnions clashableInfoSlots) newFormulaBprs
                           -- all of this is caused by the input formula of the function: add its dependencies

           result = case successOrFailure_newClashableSlotUrfather of
                     Slot_UpdateFailure clashingDeps ->
{-clash-}                 BranchClash br pr (bps_union clashingDeps currentDependencies) f2 -- if clash, it's because of: clashable formulas deps, new formula desps, involved classes deps
                     Slot_UpdateSuccess urfatherSlot ->
{-success-}           let newClashable_info = Map.insert newUrfather urfatherSlot (clashStr br)

                          -- move formulas of the prefix-to-formula map  (to keep consistency for inclusion urfather calculation) -- TODO: if input formula in H(@), disable?
                          newPrefixToFormulas = if hasUnivMod br
                                                  then foldr (\exUrfather prefToForms_ -> moveInMap prefToForms_ exUrfather newUrfather Set.union) (prefToForms br) exUrfathers
                                                  else (prefToForms br)

                          -- add the new formulas that should be sent to accessible prefixes to the branch
                          mapBoxs = map (\idx -> Map.findWithDefault (Map.empty) idx (boxConstr br) ) involvedUrfathers
                          mapAccs = map (\idx -> Map.findWithDefault (Map.empty) idx (accStr br)    ) involvedUrfathers
                          formulasToSend = concatMap (uncurry $ newFormulasToSend newFormulaBprs)
                                                     $ almostCartesianProduct mapBoxs mapAccs

                          -- move box constraint and accessibility relation data to the new urfather
                          newBoxConstr = foldr (\exUrfather boxStr_  -> moveInnerDataDMapPlusDeps newFormulaBprs boxStr_  exUrfather newUrfather)   (boxConstr br)  exUrfathers
                          newAccStr    = foldr (\exUrfather accStr_  -> moveInnerDataDMapPlusDeps newFormulaBprs accStr_  exUrfather newUrfather)   (accStr br)     exUrfathers

                          -- same for (<>) rule chart
                          newDiaRlCh = foldr (\exUrfather diaRlCh_ -> moveInMap diaRlCh_ exUrfather newUrfather Set.union)   (diaRlCh br) exUrfathers

                          nubbedNewFormulas = nubAndMergeDeps $ [PrFormula newUrfather newFormulaBprs f2] ++ formulasToSend
                          brUpdated         = br{nomPrefClasses = classes4,
                                                 boxConstr      = newBoxConstr,
                                                 accStr         = newAccStr,
                                                 prToBrPrefs    = newPrToBrPrefs,
                                                 prefToForms    = newPrefixToFormulas,
                                                 diaRlCh        = newDiaRlCh,
                                                 clashStr       = newClashable_info}
                         in
                           if hasUnivMod br then addFormulas2_withPrefToFormUpdate clp brUpdated nubbedNewFormulas
                                            else addFormulas2 clp brUpdated nubbedNewFormulas

-- Case 1,5
-- universal constraint
addFormula clp br (PrFormula _ bprs (A f))
 = addUnivConstraint clp blockedBr bprs f
    where blockedBr = br{blockMode = InclusionBlocking}

-- box constraint
addFormula clp br (PrFormula pr bprs (Box r f))
 = addBoxConstraint clp updatedBr pr r f bprs
     where updatedBr = addToAugmentedPrefixes pr br

-- Case 2
-- p : phi (not nominal)

-- if we work with the modal language
addFormula clp br f | isModal br =
  if hasUnivMod br
    then addFormula2_withPrefToFormUpdate clp br f  -- necessary to compute inclusion urfathers
    else addFormula2 clp br f   -- this one does not update the prefix to formulas map

-- if we work with the hybrid language
addFormula clp br f@(PrFormula pr bprs f2)
 = if urfather == pr
    then if hasUnivMod br then addFormula2_withPrefToFormUpdate clp newBr f
                          else addFormula2                      clp newBr f
    else if hasUnivMod br then addFormula2_withPrefToFormUpdate clp newBr (PrFormula urfather (bps_union bprs bprs2) f2)
                          else addFormula2                      clp newBr (PrFormula urfather (bps_union bprs bprs2) f2)
    where  (urfather,bprs2,newClasses) = getUrfatherAndDeps br (DS.Prefix pr)
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

addToPrefToForms :: Branch -> PrFormula -> Branch
addToPrefToForms br (PrFormula pre _ f) =
  br{prefToForms = newMap}
 where currentPtf = prefToForms br
       newMap = Map.insertWith (Set.union) pre (Set.singleton f) currentPtf

isUrfather :: Branch -> Prefix -> Bool
isUrfather b p = DS.isRoot (DS.Prefix p) classes
                  where classes = nomPrefClasses b

getUrfather :: Branch -> DS.Pointer -> Prefix
getUrfather b p = u
                  where (u,_,_) = getUrfatherAndDeps b p

getUrfatherAndDeps :: Branch -> DS.Pointer -> (Prefix,BranchingPrefixes,EquivClasses)
-- check if matrix size not enough for this urfather (eg when the prefix is created from the <> rule) -> return Nothing
getUrfatherAndDeps br p =
   if DS.isRoot p classes then defaultAnswer
                          else (ur,deps,newClasses)
  where classes = nomPrefClasses br
        (urfather, newClasses) = DS.find p classes
        (DS.Prefix ur) = urfather
        DS.Prefix unboxedP = p
        defaultAnswer = (unboxedP,bps_empty,classes)
        deps = findDeps br ur

findDeps :: Branch -> Prefix -> BranchingPrefixes
findDeps br pr = Map.findWithDefault bps_empty pr (prToBrPrefs br)

{-
   box-related constraints
-}

newFormulasToSend :: BranchingPrefixes -> Map.Map Rel [(BranchingPrefixes,Formula)] -> Map.Map Rel [(BranchingPrefixes,Prefix)] -> [PrFormula]
newFormulasToSend deps mapBox mapAcc
 = [PrFormula p (bps_unions [deps,bps1,bps2]) f |
                      r1 <- Map.keys mapBox,
                      r2 <- Map.keys mapAcc,    r1 == r2,
                      (bps1,f) <- (Map.!) mapBox r1,
                      (bps2,p) <- (Map.!) mapAcc r2     ]

addBoxConstraint :: CmdLineParams -> Branch -> Prefix -> RelSymbol -> Formula -> BranchingPrefixes -> BranchInfo
addBoxConstraint clp br nonRepresentativePr (RelSymbol r) f bprs
 = addFormulas clp newBr
               $ map (\(bprs2,p) -> PrFormula p (bps_union bprs bprs2) f) accessibleBprsPrs
   where pr = getUrfather br (DS.Prefix nonRepresentativePr)
         newBr = br{boxConstr = updateBoxConstr pr r f bprs (boxConstr br)}
         updateBoxConstr p1_ r_ f_ bprs_ boxConstr_ =
           case Map.lookup p1_ boxConstr_ of
             Nothing       -> Map.insert p1_ (Map.singleton r_ [(bprs_,f_)]) boxConstr_
             Just innerMap -> case Map.lookup r_ innerMap of
                                Nothing             -> Map.insert p1_ (Map.insert r_ [(bprs_,f_)] innerMap)                boxConstr_
                                Just innerInnerList -> Map.insert p1_ (Map.insert r_ ((bprs_,f_):innerInnerList) innerMap) boxConstr_

         accessibleBprsPrs = Map.findWithDefault [] r $ Map.findWithDefault Map.empty pr (accStr br)  -- [(BranchingPrefixes,Prefix)]

addBoxConstraint _ _ _ (InvRelSymbol _) _ _ = error "inverse modality not handled"


addAccFormula :: CmdLineParams -> Branch -> AccFormula -> BranchInfo
addAccFormula clp br (AccFormula bprs (RelSymbol r) nonRepresentativeP1 p2)
 = addFormulas clp newBr
               $ map (\(bprs2,f) -> PrFormula p2 (bps_union bprs bprs2) f) formulasToSend
   where p1 = getUrfather br (DS.Prefix nonRepresentativeP1)
         newBr    =      br{accStr=updateAccStr p1 r bprs p2 (accStr br)}
         updateAccStr p1_ r_ bprs_ p2_ accStr_ =
          case Map.lookup p1_ accStr_ of
            Nothing       -> Map.insert p1_ (Map.singleton r_ [(bprs_,p2_)]) accStr_
            Just innerMap -> case Map.lookup r_ innerMap of
                               Nothing             -> Map.insert p1_ (Map.insert r_ [(bprs_,p2_)] innerMap)                accStr_
                               Just innerInnerList -> Map.insert p1_ (Map.insert r_ ((bprs_,p2_):innerInnerList) innerMap) accStr_
         formulasToSend = Map.findWithDefault [] r $ Map.findWithDefault Map.empty p1 (boxConstr br) -- [(BranchingPrefixes,Prefix)]


addAccFormula _ _ (AccFormula _ (InvRelSymbol _) _ _ ) = error "inverse modality not handled"


{-
  universal modality-related machinery
-}

isInInclusionUrfatherClass :: Branch -> Prefix -> Bool
isInInclusionUrfatherClass br pr
 = let ur =  getUrfather br (DS.Prefix pr) in
   (getInclusionUrfather br ur) == ur

isInclusionUrfather :: Branch -> Prefix -> Bool
isInclusionUrfather br pr
 = if isUrfather br pr
    then (getInclusionUrfather br pr) == pr
    else False

getInclusionUrfather :: Branch -> Prefix -> Prefix
getInclusionUrfather br pr
 = let nomUrfather = getUrfather br (DS.Prefix pr) in
   giu_get_oldest (fromJust $ inclUrMap br) nomUrfather

giu_get_oldest :: InclusionUrfathersMap -> Prefix -> Prefix
giu_get_oldest ium pr = if parent == pr then pr else giu_get_oldest ium parent
                          where parent = ium Map.! pr

calculateInclusionUrfathers :: Branch -> Branch
-- calculates the prefix -> inclusion urfather map incrementally, by
-- updating the map from the given prefix, which typically is the smallest augmented
-- prefix in the previous step

-- if the inclusion urfather blocking mode is enabled, we handle this map
-- if not, we let it as it is
calculateInclusionUrfathers br =
    br{inclUrMap = newInclUrMap}
     where newInclUrMap =  case blockMode br of
                            NoBlocking        -> Nothing
                            InclusionBlocking -> Just $ calculateInclusionUrfathersMap br

calculateInclusionUrfathersMap :: Branch -> InclusionUrfathersMap
calculateInclusionUrfathersMap br = 
  case inclUrMap br of
   Just previousM -> if null $ incrPrs br
                      then fromScratchInclUrMap        -- this case is reached if we applied the (A) rule
                      else updatedInclUrMap previousM  -- works, provided that the augmented prefixes list is correctly filled
   Nothing        -> fromScratchInclUrMap

 where smallestModifiedPrefix = minimum $ incrPrs br 
       pr = smallestModifiedPrefix
       emptyM = Map.empty::InclusionUrfathersMap
       oneStep pref p2 iuMap =
         if formulasIncluded br pref p2
             then (Map.insert pref p2 iuMap,False) -- stop
             else (iuMap, True)
       updateM pref currentM_ = condFoldr (oneStep pref) currentM        (filter (isUrfather br) (reverse [0..pref-1]))
                                 where currentM = Map.insert pref pref currentM_
       updatedInclUrMap prevM = foldr     updateM        prevM           (filter (isUrfather br) [pr..(lastPr br)])

       fromScratchInclUrMap   = foldr     updateM        emptyM          (filter (isUrfather br) (prefixes br))


condFoldr :: (a -> b -> (b,Bool)) -> b -> [a] -> b
condFoldr _ lastB    []      = lastB
condFoldr f initialB (hd:tl)
   = let (newB,continue) = f hd initialB in
      if continue then condFoldr f newB tl else newB


formulasIncluded :: Branch -> Prefix -> Prefix-> Bool
-- is the set of formulas of the first prefix included in the set of the second prefix?
formulasIncluded br p1 p2 = Set.isSubsetOf (formulasOf p1) (formulasOf p2)
 where formulasOf p = (prefToForms br) Map.! p


{-
  Function that does everything needed to be done before each step of the tableaux calculus
  (essentially urfather calculation)
-}

calculateStepInfo :: Branch -> Branch
calculateStepInfo = wipeAugmentedPrefixes . calculateInclusionUrfathers

wipeAugmentedPrefixes :: Branch -> Branch
wipeAugmentedPrefixes br = br{incrPrs=[]}

addToAugmentedPrefixes :: Prefix -> Branch -> Branch
addToAugmentedPrefixes pr br = br{incrPrs = (pr:incrPrs br)} -- this list never gets too big, no need to nub it


{-
   "add formula(s)" functions, that update the "clashable formulas"
   to detect clashes, and store the new formula in the right sub-structure
-}

addFormulas2_withPrefToFormUpdate :: CmdLineParams -> Branch -> [PrFormula] -> BranchInfo
addFormulas2_withPrefToFormUpdate clp br (hd:tl) =
   case (addFormula2_withPrefToFormUpdate clp br hd) of
     BranchOK br2             -> addFormulas2_withPrefToFormUpdate clp br2 tl
     bi@(BranchClash _ _ _ _) -> bi

addFormulas2_withPrefToFormUpdate _ br [] = BranchOK br


addFormulas2 :: CmdLineParams -> Branch -> [PrFormula] -> BranchInfo
addFormulas2 clp br (hd:tl) =
   case (addFormula2 clp br hd) of
     BranchOK br2             -> addFormulas2 clp br2 tl
     bi@(BranchClash _ _ _ _) -> bi

addFormulas2 _ br [] = BranchOK br


addFormula2_withPrefToFormUpdate :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
addFormula2_withPrefToFormUpdate clp br f
 = addFormula2 clp updatedPrefToFormsBr f -- TODO more readable flow
    where updatedPrefToFormsBr = addToPrefToForms br f

addFormula2 :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
addFormula2 clp br pf@(PrFormula pr _ _) =
   addFormula3 clp updatedBr pf
 where updatedBr        = addToAugmentedPrefixes pr br

addFormula3 :: CmdLineParams -> Branch -> PrFormula -> BranchInfo
addFormula3 clp br pf@(PrFormula _ _ (Con _))
           = modBranchCaseFC clp br pf $ \b f -> b{conjStr = Set.insert f (conjStr b)}

addFormula3 clp br pf@(PrFormula _ _ (Dis _))
           = modBranchCaseFC clp br pf $ \b f -> b{disjStr = Set.insert f (disjStr b)}

addFormula3  _  _ (PrFormula _ _ (Box _ _))
           = error " '[]' formulas should have been treated before"

addFormula3 clp br pf@(PrFormula _ _ (Dia _ _))
           = modBranchCaseFC clp br pf $ \b f@(PrFormula pr _ f2)
                                             -> b{diaStr  = if diaAlreadyDone b pr f2            -- diamond rule saturation
                                                              then diaStr b
                                                              else Set.insert f (diaStr b)}
addFormula3 _ _ (PrFormula _ _ (A _))
           = error " 'A' formulas should have been treated before"

addFormula3 clp br pf@(PrFormula _ _ (E _))
           = modBranchCaseFC clp br pf $ \b f@(PrFormula _ _ f2) ->
                                                  b{existStr = if existAlreadyDone b f2      -- exist rule saturation
                                                                 then existStr b
                                                                 else Set.insert f (existStr b)}

addFormula3 clp br pf@(PrFormula _ _ (At _ _))
           = modBranchCaseFC clp br pf $ \b f@(PrFormula _ _ f2)  ->
                                                  b{atStr    = if atAlreadyDone b f2
                                                                 then atStr b
                                                                 else Set.insert f (atStr b)}

addFormula3 clp br pf@(PrFormula _ _ (Neg _))
           = modBranchCaseFC clp br pf $ \b f -> b{negStr  = Set.insert f (negStr b)}


addFormula3 _ br f@(PrFormula _ _ (PosLit _))
           = addAndUpdateMap br f

addFormula3 _ br f@(PrFormula _ _ (NegLit _))
           = addAndUpdateMap br f

modBranchCaseFC :: CmdLineParams -> Branch -> PrFormula
                   -> (Branch -> PrFormula -> Branch)
                   -> BranchInfo
-- if full clash is enabled, we add all formulas to the clashable formulas
modBranchCaseFC clp br f branchModifier
 =    -- (**) and when we get rid of full clash, still keep this function to update pref to forms
 if (fullClash clp) then case (addAndUpdateMap br f) of
                          BranchOK bok             -> BranchOK $ branchModifier bok f
                          bc@(BranchClash _ _ _ _) -> bc
                    else  BranchOK $ branchModifier br f


{-
   other modifications that can be done by a rule application
-}


--

addDiaRuleCheck :: Branch -> Prefix -> Formula -> Branch
addDiaRuleCheck br pr f =  -- TODO take pr's urfather ?
  br{diaRlCh=Map.insertWith Set.union ur (Set.singleton f) (diaRlCh br)}
   where ur = getUrfather br (DS.Prefix pr)

--

diaAlreadyDone :: Branch -> Prefix -> Formula -> Bool
diaAlreadyDone b p f@(Dia _ _) =
  case Map.lookup ur (diaRlCh b) of
     Nothing  -> False
     Just fset -> Set.member f fset
 where ur = getUrfather b (DS.Prefix p)

diaAlreadyDone _ _ _ = error "dia already done : wrong formula kind"

--

addExistRuleCheck :: Branch -> Formula -> Branch
addExistRuleCheck br f =
  br{existRlCh=Set.insert f (existRlCh br)}

--

existAlreadyDone :: Branch -> Formula -> Bool
existAlreadyDone b f@(E _) = Set.member f (existRlCh b)
existAlreadyDone _ _ = error "exist already done : wrong formula kind"

--

addAtRuleCheck :: Branch -> Formula -> Branch
addAtRuleCheck br f =
  br{atRlCh=Set.insert f (atRlCh br)}

--

atAlreadyDone :: Branch -> Formula -> Bool
atAlreadyDone b f@(At _ _) = Set.member f (atRlCh b)
atAlreadyDone _ _ = error "at already done : wrong formula kind"

--

addUnivConstraint :: CmdLineParams -> Branch -> BranchingPrefixes -> Formula -> BranchInfo
addUnivConstraint clp br bps f
 = addFormulas clp newBr
               $ map (\p -> PrFormula p bps f) $ urfathers
   where newBr = br{univCons = (bps,f):(univCons br)}
         prefs = [0..(lastPr br)]
         urfathers = filter (isUrfather br) prefs

--

createNewPr :: CmdLineParams -> Branch -> BranchInfo
createNewPr clp br
 = addFormulas clp newBr $ map (\(bps,f) -> PrFormula newPr bps f) univConstraints
   where newPr = (lastPr br) + 1
         newBr = br{lastPr = newPr}
         univConstraints = univCons br

--

remFormula :: Branch  -> PrFormula -> Branch
remFormula br f@(PrFormula _ _ (Con _))        = br{conjStr=(Set.delete f (conjStr br))}
remFormula br f@(PrFormula _ _ (Dia _ _))      = br{diaStr=(Set.delete f (diaStr br))}
remFormula br f@(PrFormula _ _ (E _))          = br{existStr=(Set.delete f (existStr br))}
remFormula br f@(PrFormula _ _ (Dis _))        = br{disjStr=(Set.delete f (disjStr br))}
remFormula br f@(PrFormula _ _ (Neg _))        = br{negStr=(Set.delete f (negStr br))}
remFormula br f@(PrFormula _ _ (At _ _))       = br{atStr=(Set.delete f (atStr br))}
remFormula _  _                                = error "that formula should never be deleted"


{-
  Functions to update the "clashable information" map
-}

data UpdateResult = UpdateSuccess Clashable_info | UpdateFailure BranchingPrefixes

addAndUpdateMap :: Branch -> PrFormula -> BranchInfo
addAndUpdateMap br (PrFormula pr bprs formula@(Neg f))
  = case updateMap (clashStr br) pr f False bprs of
     UpdateSuccess cs    -> BranchOK br{clashStr = cs}
     UpdateFailure bprs2 -> BranchClash br pr bprs2 formula

addAndUpdateMap br (PrFormula pr bprs f)
  = case updateMap (clashStr br) pr f True bprs of
     UpdateSuccess cs    -> BranchOK br{clashStr = cs}
     UpdateFailure bprs2 -> BranchClash br pr bprs2 f


-- Insert a piece of clashable information into all the clashable information of a branch

updateMap :: Clashable_info -> Prefix -> Formula -> Bool -> BranchingPrefixes -> UpdateResult
updateMap cs _   (PosLit Taut) True    _   = UpdateSuccess cs
updateMap _  _   (PosLit Taut) False  bprs = UpdateFailure bprs
updateMap cs pre (NegLit a)    bool   bprs = updateMap cs pre (PosLit a) (not bool) bprs
updateMap cs pre f             bool   bprs
  = case Map.lookup pre cs of
       Nothing            -> UpdateSuccess $ Map.insert pre (Map.singleton f (bool,bprs)) cs
       Just slot          -> case updateClashableInfoSlot slot f bool bprs of
                              Slot_UpdateSuccess updatedSlot -> UpdateSuccess $ Map.insert pre updatedSlot cs
                              Slot_UpdateFailure failureDeps -> UpdateFailure failureDeps

type Clashable_info_slot = Map.Map Formula (Bool,BranchingPrefixes)
data Slot_UpdateResult =   Slot_UpdateSuccess Clashable_info_slot                     -- updated slot
                         | Slot_UpdateFailure BranchingPrefixes                       -- list of sets of branching prefixes


-- Union an arbitrary number of clashable info slots
clashableInfoSlotsUnions :: [Clashable_info_slot] -> Slot_UpdateResult
clashableInfoSlotsUnions [] = Slot_UpdateSuccess (Map.empty::Clashable_info_slot)
clashableInfoSlotsUnions [cis] = Slot_UpdateSuccess cis
clashableInfoSlotsUnions (cis1:cis2:tl)
 = case unionClashableInfoSlots cis1 cis2 of
     failure@(Slot_UpdateFailure _) -> failure
     Slot_UpdateSuccess newCis      -> clashableInfoSlotsUnions (newCis:tl)

-- Union two clashable info slots

-- if there is a clash, the result reports the set of dependencies whose earliest dependency is the earliest
-- among all dependencies sets that caused the clash
unionClashableInfoSlots :: Clashable_info_slot -> Clashable_info_slot -> Slot_UpdateResult
unionClashableInfoSlots cis1 cis2
 = ucis_helper cis1 (Map.assocs cis2)
    where ucis_helper :: Clashable_info_slot -> [(Formula,(Bool,BranchingPrefixes))] -> Slot_UpdateResult
          ucis_helper cis f_b_bps_s =
             let (updateStatus,clashing_bps_s)
                                 = foldr (\(f,(bool,bps)) (upResult,clashingBps_s)
                                              -> case upResult of
                                                    Slot_UpdateSuccess cis_  ->  (updateClashableInfoSlot cis_ f bool bps, clashingBps_s      )
                                                    Slot_UpdateFailure bps_s ->  (updateClashableInfoSlot cis f bool bps, bps_s:clashingBps_s)  -- we reuse the input Clashabe Info Slot
                                         )
                                         (Slot_UpdateSuccess cis,[])   f_b_bps_s
                 result = case clashing_bps_s of
                              []    -> updateStatus                                    -- is 'success'
                              bps_s -> Slot_UpdateFailure $ findEarliestSet bps_s
                                         where findEarliestSet bprs_s = minimumBy compareBPSets bprs_s
                                               compareBPSets bps1 bps2 = compare  (deps_min bps1) (deps_min bps2)
             in
                result


-- Insert a piece of information in a clashable info slot

updateClashableInfoSlot :: Clashable_info_slot -> Formula -> Bool -> BranchingPrefixes -> Slot_UpdateResult
updateClashableInfoSlot cis (PosLit Taut) True   _   = Slot_UpdateSuccess cis
updateClashableInfoSlot  _  (PosLit Taut) False bprs = Slot_UpdateFailure bprs
updateClashableInfoSlot cis (NegLit a)    bool  bprs = updateClashableInfoSlot cis (PosLit a) (not bool) bprs
updateClashableInfoSlot cis f             bool  bprs
 = case Map.lookup f cis of
    Nothing -> Slot_UpdateSuccess $ Map.insert f (bool,bprs) cis
    Just (bool2,bprs2) -> if bool == bool2
                           then Slot_UpdateSuccess $ Map.insert f (bool,bprs_to_keep) cis
                           else Slot_UpdateFailure $ bps_union bprs bprs2
                             where bprs_to_keep = if (deps_min bprs2) <  (deps_min bprs) then bprs2 else bprs
                                  -- if the same information is caused by an earlier
                                  -- branching, only keep the information of the earliest set of dependencies

-- Other functions related to clashable information

addDepsToClashableSlot :: Slot_UpdateResult -> BranchingPrefixes -> Slot_UpdateResult
addDepsToClashableSlot res_cis bps =
 case res_cis of
  Slot_UpdateSuccess cis ->  Slot_UpdateSuccess $ Map.map (\(f,currentBps) -> (f,bps_union currentBps bps)) cis
  failure@(Slot_UpdateFailure _) -> failure

{-
     other functions
-}

isModal :: Branch -> Bool
isModal br = (languageNbNoms $ inputLanguage br) == 0

hasUnivMod :: Branch -> Bool
hasUnivMod br = languageUniv $ inputLanguage br

prefixes :: Branch -> [Prefix]
prefixes br = [0..(lastPr br)]

inclusionUrfathers :: Branch -> [Prefix]
inclusionUrfathers br = filter (isInclusionUrfather br) (prefixes br)

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

